// SPDX-FileCopyrightText: 2026-Present Nils Andreas Svee mailto:contact@lochnair.net (github @Lochnair)
//
// SPDX-License-Identifier: MPL-2.0

use std::{
    collections::{HashMap, VecDeque},
    path::PathBuf,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use anyhow::Context;
use log::{debug, info, warn};
use tokio::sync::watch;

use crate::{
    diagnostics::{DiagnosticRecord, DiagnosticsSender, DirectionStatistics, SpeedHistory},
    error::ChannelClosed,
    law::{Law, LawContext},
    measurement::model::{MeasurementEvent, MeasurementObservation, MeasurementStream},
    metrics::Metric,
    runtime::{Direction, Shaper},
    settings::Settings,
};

const ANOMALY_THRESHOLD_MS: f64 = 5_000.0;
const BASELINE_HALF_LIFE_SECS: f64 = 135.0;
const RECENT_HALF_LIFE_SECS: f64 = 0.4;
const STALE_AFTER: Duration = Duration::from_secs(30);

// The real safe-rate samples are kept in RAM-backed /tmp so a
// service restart does not throw them away. A reboot clears /tmp, and after a
// reboot the cell may be different anyway, so starting from zero is right then.
const HISTORY_PATH: &str = "/tmp/unravel-history";
const HISTORY_SAVE_EVERY: Duration = Duration::from_secs(30);
const HISTORY_MAX_AGE_SECS: u64 = 6 * 3600;
const HISTORY_HEADER: &str = "unravel-history 1";

struct RateState {
    current_kbps: f64,
    safe_rates: VecDeque<f64>,
    /// How many safe rates are real samples rather than the
    /// startup seeds (75-95% of base). Real samples sit at the back.
    observed: usize,
    /// Base the history was learned against.
    base_kbps: f64,
}

/// The saved history, without the header and time lines.
/// One line per direction: `<name> <base> <count> <rate>...`, real samples only.
fn history_body(size: usize, dirs: &[(&str, f64, &RateState)]) -> String {
    let mut body = format!("size {size}\n");
    for (name, base, state) in dirs {
        let skip = state.safe_rates.len() - state.observed;
        let real: Vec<String> = state.safe_rates.iter().skip(skip).map(|r| r.to_string()).collect();
        body.push_str(&format!("{name} {base} {} {}\n", real.len(), real.join(" ")));
    }
    body
}

/// Parse a saved history. None if it is malformed, from a
/// different history size, or older than HISTORY_MAX_AGE_SECS.
fn parse_history(text: &str, now_unix: u64, size: usize) -> Option<Vec<(String, f64, Vec<f64>)>> {
    let mut lines = text.lines();
    if lines.next()? != HISTORY_HEADER {
        return None;
    }
    let saved: u64 = lines.next()?.strip_prefix("saved ")?.parse().ok()?;
    if saved > now_unix + 60 || now_unix.saturating_sub(saved) > HISTORY_MAX_AGE_SECS {
        return None;
    }
    let saved_size: usize = lines.next()?.strip_prefix("size ")?.parse().ok()?;
    if saved_size != size {
        return None;
    }
    let mut dirs = vec![];
    for line in lines {
        let mut words = line.split_whitespace();
        let name = words.next()?.to_string();
        let base: f64 = words.next()?.parse().ok()?;
        let count: usize = words.next()?.parse().ok()?;
        let rates: Vec<f64> = words.map(|w| w.parse::<f64>()).collect::<Result<_, _>>().ok()?;
        if !(base.is_finite() && base > 0.0)
            || rates.len() != count
            || count > size
            || rates.iter().any(|r| !r.is_finite() || *r <= 0.0 || *r > 10.0 * base)
        {
            return None;
        }
        dirs.push((name, base, rates));
    }
    Some(dirs)
}

/// Put saved real samples at the back of the history, oldest first.
fn restore_samples(state: &mut RateState, rates: &[f64]) {
    let n = rates.len().min(state.safe_rates.len());
    for r in &rates[rates.len() - n..] {
        state.safe_rates.pop_front();
        state.safe_rates.push_back(*r);
    }
    state.observed = n;
}

fn unix_now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs())
}

impl RateState {
    fn new(base_speed: f64, size: u32, rng: &mut fastrand::Rng) -> Self {
        let mut rates = VecDeque::new();

        for _ in 0..size {
            rates.push_back((rng.f64() * 0.2 + 0.75) * base_speed);
        }

        Self {
            current_kbps: base_speed,
            safe_rates: rates,
            observed: 0,
            base_kbps: base_speed,
        }
    }

    fn calculate_rate(
        &mut self,
        shaper: &Shaper,
        traffic_kbps: f64,
        deltas: &[f64],
        delay_threshold_ms: f64,
        high_load_level: f64,
        rng: &mut fastrand::Rng,
    ) -> f64 {
        let mut next_kbps = self.current_kbps;

        if !deltas.is_empty() {
            let delta = deltas[deltas.len() / 2];

            if delta > 0.0 {
                let load = traffic_kbps / self.current_kbps;

                if delta < delay_threshold_ms && load > high_load_level {
                    self.safe_rates.pop_front();
                    self.safe_rates.push_back(traffic_kbps.floor());
                    self.observed = (self.observed + 1).min(self.safe_rates.len());

                    let max_rate = self
                        .safe_rates
                        .iter()
                        .copied()
                        .max_by(f64::total_cmp)
                        .unwrap();
                    next_kbps = self.current_kbps
                        * (1.0 + 0.1 * (1.0_f64 - self.current_kbps / max_rate).max(0.0))
                        + (shaper.base_kbps * 0.03);
                }

                if delta > delay_threshold_ms {
                    let rnd_rate = self.safe_rates[rng.usize(..self.safe_rates.len())];
                    next_kbps = rnd_rate.min(0.9 * traffic_kbps);
                }
            }
        }

        next_kbps.max(shaper.min_kbps).floor()
    }
}

pub(crate) struct SqmaLaw {
    settings: Settings,

    reflectors: HashMap<MeasurementStream, ReflectorState>,

    download: Option<RateState>,
    upload: Option<RateState>,

    fast_factor: f64,
    slow_factor: f64,

    rng: fastrand::Rng,
    diagnostics: Option<DiagnosticsSender>,

    // Restart-proof safe-rate history.
    history_path: PathBuf,
    history_saved_at: Option<Instant>,
    history_saved_body: String,

    // TODO: Eventually the selector should do its own calculations,
    // and not depend on the law for measurements
    control_tx: watch::Sender<Option<ControlSnapshot>>,
}

#[async_trait::async_trait]
impl Law for SqmaLaw {
    async fn run(mut self: Box<Self>, mut ctx: LawContext) -> anyhow::Result<()> {
        let interval = Duration::from_secs_f64(self.settings.advanced_settings.min_change_interval);

        let mut ticker = tokio::time::interval_at(
            tokio::time::Instant::now() + Duration::from_secs(10),
            interval,
        );

        ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);

        let mut initialized = false;

        loop {
            tokio::select! {
                event = ctx.measurements.recv() => {
                    let event = event.ok_or(ChannelClosed).context("Measurement channel closed")?;
                    self.observe(event, &ctx)?;
                }

                _ = ticker.tick() => {
                    if !initialized {
                        self.initialize(&ctx)?;
                        initialized = true;
                    } else {
                        self.evaluate(&mut ctx)?;
                    }

                    self.reflectors.retain(|_, state| {
                        Instant::now().saturating_duration_since(state.last_receive_at) <= STALE_AFTER
                    });
                }
            }
        }
    }
}

impl SqmaLaw {
    pub fn new(
        settings: Settings,
        control_tx: watch::Sender<Option<ControlSnapshot>>,
        diagnostics: Option<DiagnosticsSender>,
    ) -> Self {
        let tick = settings.advanced_settings.tick_interval;

        Self {
            settings,
            reflectors: HashMap::new(),
            download: None,
            upload: None,
            fast_factor: (0.5_f64.ln() / (RECENT_HALF_LIFE_SECS / tick)).exp(),
            slow_factor: (0.5_f64.ln() / (BASELINE_HALF_LIFE_SECS / tick)).exp(),
            rng: fastrand::Rng::new(),
            control_tx,
            diagnostics,
            history_path: PathBuf::from(HISTORY_PATH),
            history_saved_at: None,
            history_saved_body: String::new(),
        }
    }

    /// Put back the real samples saved before a restart.
    fn restore_history(&self, name: &str, base_kbps: f64, state: &mut RateState) {
        let Ok(text) = std::fs::read_to_string(&self.history_path) else {
            return;
        };
        let size = state.safe_rates.len();
        let Some(dirs) = parse_history(&text, unix_now(), size) else {
            warn!("Ignoring {}: unreadable, stale or a different history size", self.history_path.display());
            return;
        };
        let Some((_, saved_base, rates)) = dirs.iter().find(|(n, _, _)| n == name) else {
            return;
        };
        if *saved_base != base_kbps {
            info!("Not restoring {name} history: base was {saved_base}, now {base_kbps}");
            return;
        }
        restore_samples(state, rates);
        info!("Restored {} real {name} safe-rate samples", rates.len());
    }

    /// Write the real samples out, at most every 30 s and only if they changed.
    fn save_history(&mut self, now: Instant) {
        if self
            .history_saved_at
            .is_some_and(|t| now.saturating_duration_since(t) < HISTORY_SAVE_EVERY)
        {
            return;
        }
        let mut dirs = vec![];
        for (name, state) in [("download", self.download.as_ref()), ("upload", self.upload.as_ref())] {
            if let Some(state) = state {
                dirs.push((name, state.base_kbps, state));
            }
        }
        let size = dirs.first().map_or(0, |(_, _, s)| s.safe_rates.len());
        let body = history_body(size, &dirs);
        if body == self.history_saved_body {
            return;
        }
        self.history_saved_at = Some(now);
        let text = format!("{HISTORY_HEADER}\nsaved {}\n{body}", unix_now());
        let tmp = self.history_path.with_extension("tmp");
        let result = std::fs::write(&tmp, text).and_then(|_| std::fs::rename(&tmp, &self.history_path));
        match result {
            Ok(()) => self.history_saved_body = body,
            Err(error) => warn!("Could not save {}: {error}", self.history_path.display()),
        }
    }

    fn initialize(&mut self, ctx: &super::LawContext) -> anyhow::Result<()> {
        let size = self.settings.advanced_settings.speed_hist_size;

        if let Some(shaper) = ctx.shaper(Direction::Download) {
            let initial = (shaper.base_kbps * 0.6).max(shaper.min_kbps);

            ctx.set_rate(Direction::Download, initial)?;

            let mut state = RateState::new(shaper.base_kbps, size, &mut self.rng);
            state.current_kbps = initial;
            self.restore_history("download", shaper.base_kbps, &mut state);

            self.download = Some(state);
        }

        if let Some(shaper) = ctx.shaper(Direction::Upload) {
            let initial = (shaper.base_kbps * 0.6).max(shaper.min_kbps);

            ctx.set_rate(Direction::Upload, initial)?;

            let mut state = RateState::new(shaper.base_kbps, size, &mut self.rng);
            state.current_kbps = initial;
            self.restore_history("upload", shaper.base_kbps, &mut state);

            self.upload = Some(state);
        }

        Ok(())
    }

    fn deltas(&self, targets: &[MeasurementStream], now: Instant) -> (Vec<f64>, Vec<f64>) {
        let mut down = Vec::with_capacity(targets.len());
        let mut up = Vec::with_capacity(targets.len());

        let max_age = Duration::from_secs_f64(self.settings.advanced_settings.tick_interval * 2.0);

        for target in targets {
            let Some(state) = self.reflectors.get(target) else {
                continue;
            };

            if !state.valid || now.saturating_duration_since(state.last_receive_at) >= max_age {
                continue;
            }

            let down_delta = state.recent.down - state.baseline.down;
            let up_delta = state.recent.up - state.baseline.up;

            down.push(down_delta);
            up.push(up_delta);

            debug!(
                "Reflector: {} ({:?}) down_delay: {} up_delay: {}",
                target.peer, target.source, down_delta, up_delta
            );
        }

        down.sort_by(f64::total_cmp);
        up.sort_by(f64::total_cmp);

        (down, up)
    }

    fn evaluate(&mut self, ctx: &mut super::LawContext) -> anyhow::Result<()> {
        let now = Instant::now();

        let (down_deltas, up_deltas, target_count) = {
            let targets = ctx.targets.read().expect("active streams lock poisoned");
            let (down, up) = self.deltas(targets.as_slice(), now);
            (down, up, targets.len())
        };

        let num_reflectors = self.settings.reflectors.num_reflectors as usize;
        let minimum = num_reflectors.min(target_count);
        if target_count == 0 || down_deltas.len() < minimum || up_deltas.len() < minimum {
            warn!(
                "Not enough delta values (D: {}, U: {}, need {}), triggering reselection",
                down_deltas.len(),
                up_deltas.len(),
                minimum
            );
            let _ = ctx.reselect_trigger.try_send(true);
        }

        if down_deltas.is_empty() || up_deltas.is_empty() {
            warn!("No reflector data available, dropping to minimum rates");
            ctx.metrics.send(Metric::Event {
                name: "reflector_unavailable",
                reason: "",
                reflector: None,
                tags: &[],
            });

            for (direction, state) in [
                (Direction::Download, self.download.as_mut()),
                (Direction::Upload, self.upload.as_mut()),
            ] {
                let (Some(state), Some(shaper)) = (state, ctx.shaper(direction)) else {
                    continue;
                };

                ctx.set_rate(direction, shaper.min_kbps)?;
                state.current_kbps = shaper.min_kbps;
            }

            return Ok(());
        }

        let Some(traffic) = *ctx.traffic.borrow() else {
            // No traffic sample available. Retain current rates.
            ctx.metrics.send(Metric::Event {
                name: "traffic_sample_unavailable",
                reason: "",
                reflector: None,
                tags: &[],
            });
            return Ok(());
        };

        // Load uses the rate in effect during the traffic sample, before this evaluation.
        let (down_load, up_load) = if self.diagnostics.is_some() {
            (
                self.download
                    .as_ref()
                    .map(|s| traffic.rx_kbps / s.current_kbps),
                self.upload
                    .as_ref()
                    .map(|s| traffic.tx_kbps / s.current_kbps),
            )
        } else {
            (None, None)
        };

        for (direction, state, deltas, traffic_kbps, delay_ms) in [
            (
                Direction::Download,
                self.download.as_mut(),
                down_deltas.as_slice(),
                traffic.rx_kbps,
                self.settings.advanced_settings.download_delay_ms,
            ),
            (
                Direction::Upload,
                self.upload.as_mut(),
                up_deltas.as_slice(),
                traffic.tx_kbps,
                self.settings.advanced_settings.upload_delay_ms,
            ),
        ] {
            let (Some(state), Some(shaper)) = (state, ctx.shaper(direction)) else {
                continue;
            };

            let load = traffic_kbps / state.current_kbps;
            let next = state.calculate_rate(
                shaper,
                traffic_kbps,
                deltas,
                delay_ms,
                self.settings.advanced_settings.high_load_level,
                &mut self.rng,
            );

            if next != state.current_kbps {
                ctx.set_rate(direction, next)?;
                state.current_kbps = next;
            }

            ctx.metrics.send(Metric::Rate {
                direction,
                rate_kbps: state.current_kbps,
                load,
                delta_delay: deltas[deltas.len() / 2],
            });
        }

        self.save_history(now);

        if let Some(diagnostics) = &mut self.diagnostics {
            diagnostics.publish(now, |history_due| DiagnosticRecord {
                time: SystemTime::now(),
                download: self.download.as_ref().map(|s| DirectionStatistics {
                    load: down_load.unwrap(),
                    delta_ms: down_deltas[down_deltas.len() / 2],
                    rate_kbps: s.current_kbps,
                }),
                upload: self.upload.as_ref().map(|s| DirectionStatistics {
                    load: up_load.unwrap(),
                    delta_ms: up_deltas[up_deltas.len() / 2],
                    rate_kbps: s.current_kbps,
                }),
                history: history_due.then(|| SpeedHistory {
                    download: self
                        .download
                        .as_ref()
                        .map(|s| s.safe_rates.iter().copied().collect()),
                    upload: self
                        .upload
                        .as_ref()
                        .map(|s| s.safe_rates.iter().copied().collect()),
                }),
            });
        }

        Ok(())
    }

    fn observe(&mut self, event: MeasurementEvent, ctx: &super::LawContext) -> anyhow::Result<()> {
        let observation = match event {
            MeasurementEvent::Observation(reply) => reply,
            MeasurementEvent::Loss(_) => return Ok(()),
        };

        let sample = EwmaStats::from_reply(&observation);
        let (state, anomaly) = {
            let state = self
                .reflectors
                .entry(observation.stream)
                .or_insert_with(|| ReflectorState::new(sample, observation.observed_at));

            let anomaly = state.update(
                sample,
                observation.observed_at,
                self.slow_factor,
                self.fast_factor,
            );

            (*state, anomaly)
        };

        if anomaly {
            ctx.metrics.send(Metric::Event {
                name: "reselection",
                reason: "anomaly",
                reflector: Some(observation.stream.peer),
                tags: &[],
            });

            let _ = ctx.reselect_trigger.try_send(true);
        } else {
            ctx.metrics.send(Metric::Baseline {
                reflector: observation.stream.peer,
                baseline_up_ewma: state.baseline.up,
                baseline_down_ewma: state.baseline.down,
                recent_up_ewma: state.recent.up,
                recent_down_ewma: state.recent.down,
            });
        }

        self.control_tx.send_replace(Some(ControlSnapshot {
            reflectors: self.reflectors.clone(),
        }));

        ctx.metrics.send(Metric::Ping {
            reflector: observation.stream.peer,
            measurement_type: observation.stream.source,
            rtt: observation.rtt_ms(),
            up_time: observation
                .one_way
                .map(|o| o.uplink.as_nanos() as f64 / 1000000.0)
                .unwrap_or(observation.rtt_ms() / 2.0),
            down_time: observation
                .one_way
                .map(|o| o.downlink.as_nanos() as f64 / 1000000.0)
                .unwrap_or(observation.rtt_ms() / 2.0),
        });

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct ControlSnapshot {
    pub reflectors: HashMap<MeasurementStream, ReflectorState>,
}

#[derive(Clone, Copy, Debug)]
pub struct EwmaStats {
    pub down: f64,
    pub up: f64,
}

impl EwmaStats {
    fn from_reply(reply: &MeasurementObservation) -> Self {
        Self {
            down: reply
                .one_way
                .map(|o| o.downlink.as_nanos() as f64 / 1000000.0)
                .unwrap_or(reply.rtt_ms() / 2.0),
            up: reply
                .one_way
                .map(|o| o.uplink.as_nanos() as f64 / 1000000.0)
                .unwrap_or(reply.rtt_ms() / 2.0),
        }
    }

    fn update(&mut self, sample: Self, factor: f64) {
        self.down = self.down * factor + sample.down * (1.0 - factor);
        self.up = self.up * factor + sample.up * (1.0 - factor);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ReflectorState {
    pub baseline: EwmaStats,
    pub recent: EwmaStats,
    /// Last response, including rejected measurements.
    pub last_receive_at: Instant,
    /// Whether the retained EWMAs are usable after the latest response.
    pub valid: bool,
}

impl ReflectorState {
    fn new(sample: EwmaStats, received_at: Instant) -> Self {
        Self {
            baseline: sample,
            recent: sample,
            last_receive_at: received_at,
            valid: true,
        }
    }

    fn reset(&mut self, sample: EwmaStats, received_at: Instant) {
        *self = Self::new(sample, received_at);
    }

    fn update(
        &mut self,
        sample: EwmaStats,
        received_at: Instant,
        slow_factor: f64,
        fast_factor: f64,
    ) -> bool {
        if received_at.saturating_duration_since(self.last_receive_at) > STALE_AFTER {
            self.reset(sample, received_at);
        }
        self.last_receive_at = received_at;

        if sample.up > self.baseline.up + ANOMALY_THRESHOLD_MS
            || sample.down > self.baseline.down + ANOMALY_THRESHOLD_MS
        {
            self.valid = false;
            return true;
        }

        self.baseline.update(sample, slow_factor);
        self.recent.update(sample, fast_factor);

        self.baseline.down = self.baseline.down.min(self.recent.down);
        self.baseline.up = self.baseline.up.min(self.recent.up);
        self.valid = true;

        false
    }
}

#[cfg(test)]
mod history_tests {
    use super::*;
    use crate::runtime::Shaper;

    fn state(current: f64) -> (RateState, fastrand::Rng) {
        let mut rng = fastrand::Rng::with_seed(7);
        let mut st = RateState::new(20000.0, 100, &mut rng);
        st.current_kbps = current;
        (st, rng)
    }

    fn with_observed(st: &mut RateState, real: &[f64]) {
        for r in real {
            st.safe_rates.pop_front();
            st.safe_rates.push_back(*r);
        }
        st.observed = real.len();
    }

    fn saved(st: &RateState, at: u64) -> String {
        format!("{HISTORY_HEADER}\nsaved {at}\n{}", history_body(100, &[("upload", 20000.0, st)]))
    }

    #[test]
    fn history_round_trips_only_the_real_samples() {
        let (mut st, _) = state(6200.0);
        with_observed(&mut st, &[6200.0, 6875.5, 7100.0]);
        let dirs = parse_history(&saved(&st, 1000), 1010, 100).unwrap();
        assert_eq!(dirs, vec![("upload".to_string(), 20000.0, vec![6200.0, 6875.5, 7100.0])]);
    }

    #[test]
    fn empty_history_restores_nothing() {
        let (st, _) = state(12000.0);
        let dirs = parse_history(&saved(&st, 1000), 1010, 100).unwrap();
        let (mut fresh, _) = state(12000.0);
        restore_samples(&mut fresh, &dirs[0].2);
        assert_eq!(fresh.observed, 0);
    }

    #[test]
    fn stale_or_future_history_is_ignored() {
        let (mut st, _) = state(6200.0);
        with_observed(&mut st, &[6200.0]);
        assert!(parse_history(&saved(&st, 1000), 1000 + HISTORY_MAX_AGE_SECS + 1, 100).is_none());
        assert!(parse_history(&saved(&st, 5000), 1000, 100).is_none());
        assert!(parse_history(&saved(&st, 1000), 1000 + HISTORY_MAX_AGE_SECS, 100).is_some());
    }

    #[test]
    fn other_history_size_or_garbage_is_ignored() {
        let (mut st, _) = state(6200.0);
        with_observed(&mut st, &[6200.0]);
        assert!(parse_history(&saved(&st, 1000), 1010, 50).is_none());
        assert!(parse_history("", 1010, 100).is_none());
        assert!(parse_history("unravel-history 2\nsaved 1000\nsize 100\n", 1010, 100).is_none());
        let bad = format!("{HISTORY_HEADER}\nsaved 1000\nsize 100\nupload 20000 2 6200 NaN\n");
        assert!(parse_history(&bad, 1010, 100).is_none());
        let short = format!("{HISTORY_HEADER}\nsaved 1000\nsize 100\nupload 20000 3 6200 6300\n");
        assert!(parse_history(&short, 1010, 100).is_none());
        let wild = format!("{HISTORY_HEADER}\nsaved 1000\nsize 100\nupload 20000 1 900000\n");
        assert!(parse_history(&wild, 1010, 100).is_none());
    }

    #[test]
    fn history_file_is_written_and_read_back() {
        let dir = std::env::temp_dir().join(format!("unravel-hist-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("unravel-history");
        let (mut st, _) = state(6200.0);
        with_observed(&mut st, &[6100.0, 6300.0]);
        let text = saved(&st, unix_now());
        std::fs::write(&path, &text).unwrap();
        let back = std::fs::read_to_string(&path).unwrap();
        let dirs = parse_history(&back, unix_now(), 100).unwrap();
        assert_eq!(dirs[0].2, vec![6100.0, 6300.0]);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn restored_samples_count_as_real_and_sit_at_the_back() {
        let (mut st, _) = state(12000.0);
        restore_samples(&mut st, &[6000.0, 6200.0, 6400.0]);
        assert_eq!(st.observed, 3);
        assert_eq!(st.safe_rates.len(), 100);
        let tail: Vec<f64> = st.safe_rates.iter().skip(97).copied().collect();
        assert_eq!(tail, vec![6000.0, 6200.0, 6400.0]);
    }

    #[test]
    fn a_raise_counts_a_real_sample() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(10000.0);
        let deltas = vec![0.0, 5.0, 10.0, 15.0, 20.0];
        st.calculate_rate(&shaper, 9500.0, &deltas, 25.0, 0.8, &mut rng);
        assert_eq!(st.observed, 1);
        assert_eq!(*st.safe_rates.back().unwrap(), 9500.0);
    }
}
