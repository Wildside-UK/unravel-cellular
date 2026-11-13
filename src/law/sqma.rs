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
const HISTORY_HEADER: &str = "unravel-history 2";
const HISTORY_HEADER_V1: &str = "unravel-history 1";

struct RateState {
    current_kbps: f64,
    safe_rates: VecDeque<f64>,
    /// How many safe rates are real samples rather than the
    /// startup seeds (75-95% of base). Real samples sit at the back.
    observed: usize,
    /// Base the history was learned against.
    base_kbps: f64,
    /// Unix time of each real sample, oldest first, matched to the
    /// back of safe_rates. A sample with no time here counts as time 0.
    sample_times: VecDeque<u64>,
}

/// One saved direction: name, base and the real samples as (rate, unix time).
type SavedDirection = (String, f64, Vec<(f64, u64)>);

impl RateState {
    /// The real samples with their times, oldest first.
    fn real_samples(&self) -> Vec<(f64, u64)> {
        let skip = self.safe_rates.len() - self.observed;
        let missing = self.observed.saturating_sub(self.sample_times.len());
        let times = self.sample_times.iter().skip(self.sample_times.len().saturating_sub(self.observed));
        let times = std::iter::repeat_n(&0, missing).chain(times);
        self.safe_rates.iter().skip(skip).copied().zip(times.copied()).collect()
    }
}

/// The saved history, without the header and time lines.
/// One line per direction: `<name> <base> <count> <rate>@<time>...`, real samples only.
fn history_body(size: usize, dirs: &[(&str, f64, Vec<(f64, u64)>)]) -> String {
    let mut body = format!("size {size}\n");
    for (name, base, samples) in dirs {
        let real: Vec<String> = samples.iter().map(|(r, t)| format!("{r}@{t}")).collect();
        body.push_str(&format!("{name} {base} {} {}\n", real.len(), real.join(" ")));
    }
    body
}

/// One saved sample: `<rate>@<time>` in format 2, a bare rate (time 0) in format 1.
fn parse_sample(word: &str, with_time: bool) -> Option<(f64, u64)> {
    if with_time {
        let (rate, time) = word.split_once('@')?;
        Some((rate.parse().ok()?, time.parse().ok()?))
    } else {
        Some((word.parse().ok()?, 0))
    }
}

/// Parse a saved history. None if it is malformed, from a
/// different history size, or older than HISTORY_MAX_AGE_SECS.
/// Format 1 (no sample times) is still read; its samples get time 0.
fn parse_history(text: &str, now_unix: u64, size: usize) -> Option<Vec<SavedDirection>> {
    let mut lines = text.lines();
    let with_time = match lines.next()? {
        HISTORY_HEADER => true,
        HISTORY_HEADER_V1 => false,
        _ => return None,
    };
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
        let samples: Vec<(f64, u64)> = words.map(|w| parse_sample(w, with_time)).collect::<Option<_>>()?;
        if !(base.is_finite() && base > 0.0)
            || samples.len() != count
            || count > size
            || samples.iter().any(|(r, _)| !r.is_finite() || *r <= 0.0 || *r > 10.0 * base)
        {
            return None;
        }
        dirs.push((name, base, samples));
    }
    Some(dirs)
}

/// Put saved real samples at the back of the history, oldest first.
fn restore_samples(state: &mut RateState, samples: &[(f64, u64)]) {
    let n = samples.len().min(state.safe_rates.len());
    state.sample_times.clear();
    for (r, t) in &samples[samples.len() - n..] {
        state.safe_rates.pop_front();
        state.safe_rates.push_back(*r);
        state.sample_times.push_back(*t);
    }
    state.observed = n;
}

/// Drop the real samples taken after `cutoff` (unix seconds).
fn samples_up_to(samples: Vec<(f64, u64)>, cutoff: u64) -> Vec<(f64, u64)> {
    samples.into_iter().filter(|(_, t)| *t <= cutoff).collect()
}

/// A history key is plain text: 1-64 of A-Z a-z 0-9 . _ : -
fn valid_history_key(key: &str) -> bool {
    (1..=64).contains(&key.len())
        && key.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b':' | b'-'))
}

/// Parse a key file: line 1 the key, line 2 (optional) the unix time the
/// previous key was last confirmed, 0 or missing = unknown.
fn parse_history_key(text: &str) -> Option<(String, u64)> {
    let mut lines = text.lines();
    let key = lines.next()?.trim();
    if !valid_history_key(key) {
        return None;
    }
    let confirmed = lines.next().and_then(|l| l.trim().parse().ok()).unwrap_or(0);
    Some((key.to_string(), confirmed))
}

fn history_path_for(base: &std::path::Path, key: &str) -> PathBuf {
    let mut name = base.as_os_str().to_owned();
    name.push(".");
    name.push(key);
    PathBuf::from(name)
}

/// Write a history file atomically (temp file, then rename).
fn write_history(path: &std::path::Path, body: &str) -> bool {
    let text = format!("{HISTORY_HEADER}\nsaved {}\n{body}", unix_now());
    let tmp = path.with_extension("tmp");
    match std::fs::write(&tmp, text).and_then(|_| std::fs::rename(&tmp, path)) {
        Ok(()) => true,
        Err(error) => {
            warn!("Could not save {}: {error}", path.display());
            false
        }
    }
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
            sample_times: VecDeque::new(),
        }
    }

    fn calculate_rate(
        &mut self,
        shaper: &Shaper,
        traffic_kbps: f64,
        deltas: &[f64],
        delay_threshold_ms: f64,
        high_load_level: f64,
        low_load_cut_floor: f64,
        idle_recovery_percent: f64,
        low_load_level: f64,
        rng: &mut fastrand::Rng,
    ) -> (f64, &'static str) {
        let mut next_kbps = self.current_kbps;
        let mut reason = "hold";

        if !deltas.is_empty() {
            let delta = deltas[deltas.len() / 2];
            let load = traffic_kbps / self.current_kbps;

            if delta > 0.0 {

                if delta < delay_threshold_ms && load > high_load_level {
                    self.safe_rates.pop_front();
                    self.safe_rates.push_back(traffic_kbps.floor());
                    self.observed = (self.observed + 1).min(self.safe_rates.len());
                    self.sample_times.push_back(unix_now());
                    if self.sample_times.len() > self.safe_rates.len() {
                        self.sample_times.pop_front();
                    }

                    let max_rate = self
                        .safe_rates
                        .iter()
                        .copied()
                        .max_by(f64::total_cmp)
                        .unwrap();
                    next_kbps = self.current_kbps
                        * (1.0 + 0.1 * (1.0_f64 - self.current_kbps / max_rate).max(0.0))
                        + (shaper.base_kbps * 0.03);
                    reason = "raise";
                }

                if delta > delay_threshold_ms {
                    let rnd_rate = self.safe_rates[rng.usize(..self.safe_rates.len())];
                    next_kbps = rnd_rate.min(0.9 * traffic_kbps);
                    reason = "cut";

                    // At low load, one tick over the threshold may
                    // only take the rate down to a fraction of where it was.
                    if low_load_cut_floor > 0.0 && load <= low_load_level {
                        let capped = self.current_kbps * low_load_cut_floor;
                        if next_kbps < capped {
                            next_kbps = capped;
                            reason = "cut-capped";
                        }
                    }
                }
            }

            // With the delay under the threshold and the link not
            // busy, drift toward the median of the safe-rate history. Outside
            // the delta > 0 check, as the idle median delta is often exactly 0.
            // Only real samples count: the startup seeds would pull an idle
            // link up to 75-95% of base after every restart.
            if idle_recovery_percent > 0.0
                && self.observed > 0
                && delta <= delay_threshold_ms
                && load <= low_load_level
            {
                let skip = self.safe_rates.len() - self.observed;
                let mut rates: Vec<f64> = self.safe_rates.iter().skip(skip).copied().collect();
                rates.sort_by(f64::total_cmp);
                let target = rates[rates.len() / 2].max(shaper.min_kbps);
                let step = shaper.base_kbps * idle_recovery_percent / 100.0;
                if self.current_kbps < target {
                    next_kbps = (self.current_kbps + step).min(target);
                    reason = "recover-up";
                } else if self.current_kbps > target {
                    next_kbps = (self.current_kbps - step).max(target);
                    reason = "recover-down";
                }
            }
        }

        (next_kbps.max(shaper.min_kbps).floor(), reason)
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

    // Restart-proof safe-rate history. history_path is history_base, or
    // history_base.<key> once a history key is known.
    history_base: PathBuf,
    history_path: PathBuf,
    history_saved_at: Option<Instant>,
    history_saved_body: String,

    // Optional per-key histories, the key read from a file.
    history_key_file: Option<PathBuf>,
    history_key_mtime: Option<SystemTime>,
    history_key: Option<String>,
    history_key_warned: bool,

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
        let history_key_file = Some(settings.advanced_settings.history_key_file.trim())
            .filter(|f| !f.is_empty())
            .map(PathBuf::from);

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
            history_base: PathBuf::from(HISTORY_PATH),
            history_path: PathBuf::from(HISTORY_PATH),
            history_saved_at: None,
            history_saved_body: String::new(),
            history_key_file,
            history_key_mtime: None,
            history_key: None,
            history_key_warned: false,
        }
    }

    /// Put back the real samples saved before a restart, or for a key.
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
        let body = self.current_body(None);
        if body == self.history_saved_body {
            return;
        }
        self.history_saved_at = Some(now);
        if write_history(&self.history_path, &body) {
            self.history_saved_body = body;
        }
    }

    /// The history body for both directions, without samples after `cutoff`.
    fn current_body(&self, cutoff: Option<u64>) -> String {
        let mut dirs = vec![];
        let mut size = 0;
        for (name, state) in [("download", self.download.as_ref()), ("upload", self.upload.as_ref())] {
            if let Some(state) = state {
                size = state.safe_rates.len();
                let mut samples = state.real_samples();
                if let Some(cutoff) = cutoff {
                    samples = samples_up_to(samples, cutoff);
                }
                dirs.push((name, state.base_kbps, samples));
            }
        }
        history_body(size, &dirs)
    }

    /// Re-read the key file if it changed. On a new key, file the current
    /// history under the old key and load the new key's history.
    fn poll_history_key(&mut self) {
        let Some(file) = self.history_key_file.clone() else {
            return;
        };
        let Ok(mtime) = std::fs::metadata(&file).and_then(|m| m.modified()) else {
            return;
        };
        if self.history_key_mtime == Some(mtime) {
            return;
        }
        self.history_key_mtime = Some(mtime);
        let Some((key, confirmed)) = std::fs::read_to_string(&file).ok().as_deref().and_then(parse_history_key) else {
            if !self.history_key_warned {
                warn!("Ignoring history key file {}: line 1 is not a valid key", file.display());
                self.history_key_warned = true;
            }
            return;
        };
        self.history_key_warned = false;
        if self.history_key.as_deref() == Some(key.as_str()) {
            return;
        }
        self.switch_history_key(key, confirmed);
    }

    fn switch_history_key(&mut self, key: String, confirmed: u64) {
        let new_path = history_path_for(&self.history_base, &key);
        let have_state = self.download.is_some() || self.upload.is_some();

        // Before the first key, adopt what has been learned so far unless the
        // key already has its own history.
        if self.history_key.is_none() && !new_path.exists() {
            // At startup nothing is in memory yet: file the single history
            // under the first key so it is still loaded.
            if !have_state && self.history_path.exists() {
                if let Err(error) = std::fs::copy(&self.history_path, &new_path) {
                    warn!("Could not copy {} to {}: {error}", self.history_path.display(), new_path.display());
                }
            }
            info!("History key is now {key}");
            self.history_key = Some(key);
            self.history_path = new_path;
            self.history_saved_body.clear();
            self.history_saved_at = None;
            return;
        }

        if have_state {
            let cutoff = (confirmed > 0).then_some(confirmed);
            let body = self.current_body(cutoff);
            write_history(&self.history_path, &body);
        }

        info!(
            "History key {} -> {key}",
            self.history_key.as_deref().unwrap_or("(none)")
        );
        self.history_key = Some(key);
        self.history_path = new_path;
        self.history_saved_body.clear();
        self.history_saved_at = None;

        let size = self.settings.advanced_settings.speed_hist_size;
        for name in ["download", "upload"] {
            let slot = if name == "download" { &self.download } else { &self.upload };
            let Some(old) = slot.as_ref() else {
                continue;
            };
            let mut state = RateState::new(old.base_kbps, size, &mut self.rng);
            state.current_kbps = old.current_kbps;
            self.restore_history(name, state.base_kbps, &mut state);
            if name == "download" {
                self.download = Some(state);
            } else {
                self.upload = Some(state);
            }
        }
    }

    fn initialize(&mut self, ctx: &super::LawContext) -> anyhow::Result<()> {
        let size = self.settings.advanced_settings.speed_hist_size;
        self.poll_history_key();

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
        self.poll_history_key();

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
            let (next, reason) = state.calculate_rate(
                shaper,
                traffic_kbps,
                deltas,
                delay_ms,
                self.settings.advanced_settings.high_load_level,
                self.settings.advanced_settings.low_load_cut_floor,
                self.settings.advanced_settings.idle_recovery_percent,
                self.settings.advanced_settings.low_load_level,
                &mut self.rng,
            );

            debug!(
                "Decision {:?}: median delta {:.2} ms, load {:.3}, rate {} -> {} kbit ({})",
                direction,
                deltas[deltas.len() / 2],
                load,
                state.current_kbps,
                next,
                reason
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
mod low_load_cut_tests {
    use super::*;
    use crate::runtime::Shaper;

    const TH: f64 = 25.0;
    const HIGH: f64 = 0.8;

    fn state(current: f64) -> (RateState, fastrand::Rng) {
        let mut rng = fastrand::Rng::with_seed(7);
        let mut st = RateState::new(20000.0, 100, &mut rng);
        st.current_kbps = current;
        (st, rng)
    }

    fn deltas(median: f64) -> Vec<f64> {
        vec![median - 10.0, median - 5.0, median, median + 5.0, median + 10.0]
    }

    #[test]
    fn off_matches_upstream_low_load_cut_goes_to_floor() {
        // 5 Nov run 1: 12000 kbit, 7.3% load, median 26.19 ms.
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(12000.0);
        let (next, why) = st.calculate_rate(&shaper, 876.0, &deltas(26.19), TH, HIGH, 0.0, 0.0, 0.3, &mut rng);
        assert_eq!(next, 5000.0);
        assert_eq!(why, "cut");
    }

    #[test]
    fn cap_limits_a_single_low_load_cut() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(12000.0);
        let (next, why) = st.calculate_rate(&shaper, 876.0, &deltas(26.19), TH, HIGH, 0.7, 0.0, 0.3, &mut rng);
        assert_eq!(next, 8400.0);
        assert_eq!(why, "cut-capped");
    }

    #[test]
    fn sustained_low_load_delay_still_reaches_the_floor() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(12000.0);
        let mut seen = vec![];
        for _ in 0..4 {
            let traffic = st.current_kbps * 0.08;
            let (next, _) = st.calculate_rate(&shaper, traffic, &deltas(35.0), TH, HIGH, 0.7, 0.0, 0.3, &mut rng);
            st.current_kbps = next;
            seen.push(next);
        }
        assert_eq!(seen, vec![8400.0, 5880.0, 5000.0, 5000.0]);
    }

    #[test]
    fn high_load_cut_is_not_capped() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(12000.0);
        let (next, why) = st.calculate_rate(&shaper, 11000.0, &deltas(30.0), TH, HIGH, 0.7, 0.0, 0.3, &mut rng);
        assert!(next <= 0.9 * 11000.0, "got {next}");
        assert_eq!(why, "cut");
    }

    #[test]
    fn moderate_load_cut_is_the_upstream_cut() {
        // Mid-upload at 0.75 load (between low_load_level and high_load_level).
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(17000.0);
        let traffic = 17000.0 * 0.75;
        let (next, why) = st.calculate_rate(&shaper, traffic, &deltas(26.3), TH, HIGH, 0.7, 0.0, 0.3, &mut rng);
        assert_eq!(why, "cut");
        assert!(next <= 0.9 * traffic, "got {next}");
    }
}

#[cfg(test)]
mod idle_recovery_tests {
    use super::*;
    use crate::runtime::Shaper;

    const TH: f64 = 25.0;
    const HIGH: f64 = 0.8;

    fn state(current: f64) -> (RateState, fastrand::Rng) {
        let mut rng = fastrand::Rng::with_seed(7);
        let mut st = RateState::new(20000.0, 100, &mut rng);
        st.current_kbps = current;
        (st, rng)
    }

    fn deltas(median: f64) -> Vec<f64> {
        vec![median - 10.0, median - 5.0, median, median + 5.0, median + 10.0]
    }

    #[test]
    fn no_recovery_from_startup_seeds_alone() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(5000.0);
        let (next, why) = st.calculate_rate(&shaper, 50.0, &deltas(0.0), TH, HIGH, 0.0, 3.0, 0.3, &mut rng);
        assert_eq!((next, why), (5000.0, "hold"));
    }

    fn with_observed(st: &mut RateState, real: &[f64]) {
        for r in real {
            st.safe_rates.pop_front();
            st.safe_rates.push_back(*r);
        }
        st.observed = real.len();
    }

    #[test]
    fn recovery_steps_up_to_the_real_median_even_at_zero_delta() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(5000.0);
        with_observed(&mut st, &[10000.0, 11000.0, 12000.0]);
        let mut path = vec![];
        for _ in 0..12 {
            let (next, _) = st.calculate_rate(&shaper, 50.0, &[-1.0, 0.0, 0.0, 0.5, 1.0], TH, HIGH, 0.0, 3.0, 0.3, &mut rng);
            st.current_kbps = next;
            path.push(next);
        }
        assert_eq!(path[0], 5600.0);
        assert_eq!(*path.last().unwrap(), 11000.0);
        assert!(path.windows(2).all(|w| w[1] >= w[0]));
    }

    #[test]
    fn recovery_steps_down_toward_the_real_median() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(15000.0);
        with_observed(&mut st, &[10000.0, 11000.0, 12000.0]);
        let (next, why) = st.calculate_rate(&shaper, 50.0, &deltas(3.0), TH, HIGH, 0.0, 3.0, 0.3, &mut rng);
        assert_eq!((next, why), (14400.0, "recover-down"));
    }

    #[test]
    fn busy_link_is_left_to_the_upstream_logic() {
        // High load and low delay: the normal raise, not recovery.
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(10000.0);
        with_observed(&mut st, &[6000.0, 6000.0, 6000.0]);
        let (next, why) = st.calculate_rate(&shaper, 9500.0, &deltas(10.0), TH, HIGH, 0.0, 3.0, 0.3, &mut rng);
        assert_eq!(why, "raise");
        assert!(next > 10000.0);
    }

    #[test]
    fn moderate_load_with_low_delay_holds_as_upstream() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let (mut st, mut rng) = state(13683.0);
        with_observed(&mut st, &[10000.0, 11000.0, 12000.0]);
        let (next, why) = st.calculate_rate(&shaper, 13683.0 * 0.79, &deltas(18.3), TH, HIGH, 0.0, 3.0, 0.3, &mut rng);
        assert_eq!((next, why), (13683.0, "hold"));
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
        format!("{HISTORY_HEADER}\nsaved {at}\n{}", history_body(100, &[("upload", 20000.0, st.real_samples())]))
    }

    #[test]
    fn history_round_trips_only_the_real_samples() {
        let (mut st, _) = state(6200.0);
        with_observed(&mut st, &[6200.0, 6875.5, 7100.0]);
        let dirs = parse_history(&saved(&st, 1000), 1010, 100).unwrap();
        assert_eq!(dirs, vec![("upload".to_string(), 20000.0, vec![(6200.0, 0), (6875.5, 0), (7100.0, 0)])]);
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
        assert!(parse_history("unravel-history 3\nsaved 1000\nsize 100\n", 1010, 100).is_none());
        let bad = format!("{HISTORY_HEADER_V1}\nsaved 1000\nsize 100\nupload 20000 2 6200 NaN\n");
        assert!(parse_history(&bad, 1010, 100).is_none());
        let short = format!("{HISTORY_HEADER_V1}\nsaved 1000\nsize 100\nupload 20000 3 6200 6300\n");
        assert!(parse_history(&short, 1010, 100).is_none());
        let wild = format!("{HISTORY_HEADER_V1}\nsaved 1000\nsize 100\nupload 20000 1 900000\n");
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
        assert_eq!(dirs[0].2, vec![(6100.0, 0), (6300.0, 0)]);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn restored_samples_count_as_real_and_sit_at_the_back() {
        let (mut st, _) = state(12000.0);
        restore_samples(&mut st, &[(6000.0, 1), (6200.0, 2), (6400.0, 3)]);
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
        st.calculate_rate(&shaper, 9500.0, &deltas, 25.0, 0.8, 0.0, 0.0, 0.3, &mut rng);
        assert_eq!(st.observed, 1);
        assert_eq!(*st.safe_rates.back().unwrap(), 9500.0);
    }
}

#[cfg(test)]
mod cellular_tests {
    // Needs idle recovery and the kept history together.
    use super::*;
    use crate::runtime::Shaper;

    #[test]
    fn restored_samples_switch_recovery_on_after_a_restart() {
        let shaper = Shaper::for_test(20000.0, 5000.0);
        let mut rng = fastrand::Rng::with_seed(7);
        let mut old = RateState::new(20000.0, 100, &mut rng);
        restore_samples(&mut old, &[(6000.0, 1), (6200.0, 2), (6400.0, 3)]);
        let text = format!("{HISTORY_HEADER}\nsaved 1000\n{}", history_body(100, &[("upload", 20000.0, old.real_samples())]));
        let dirs = parse_history(&text, 1010, 100).unwrap();

        // A fresh start sits at 0.6 x base with only seeds: without the history it would hold.
        let mut st = RateState::new(20000.0, 100, &mut rng);
        st.current_kbps = 12000.0;
        restore_samples(&mut st, &dirs[0].2);
        let deltas = vec![-7.0, -2.0, 3.0, 8.0, 13.0];
        let (next, why) = st.calculate_rate(&shaper, 50.0, &deltas, 25.0, 0.8, 0.0, 3.0, 0.3, &mut rng);
        assert_eq!((next, why), (11400.0, "recover-down"));
    }
}

#[cfg(test)]
mod per_cell_history_tests {
    use super::*;
    use crate::settings::{
        AdvancedSettings, NetworkSettings, ObservabilitySettings, OutputSettings, ReflectorSettings, Settings,
    };
    use std::path::{Path, PathBuf};

    struct Dir(PathBuf);

    impl Drop for Dir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn temp_dir(tag: &str) -> Dir {
        let dir = std::env::temp_dir().join(format!("unravel-pch-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        Dir(dir)
    }

    fn settings(key_file: &str) -> Settings {
        Settings {
            network: NetworkSettings {
                download_interface: "ifb0".into(),
                upload_interface: "eth0".into(),
                download_base_kbits: 50000.0,
                download_min_percent: 10.0,
                upload_base_kbits: 20000.0,
                upload_min_percent: 10.0,
                measurement_bind_device: None,
                measurement_mark: None,
                measurement_fib: None,
            },
            reflectors: ReflectorSettings::default(),
            output: OutputSettings::default(),
            observability: ObservabilitySettings::default(),
            advanced_settings: AdvancedSettings {
                history_key_file: key_file.into(),
                ..Default::default()
            },
        }
    }

    /// A law with both directions set up and its history files under `dir`.
    fn law(dir: &Path, key_file: &str) -> SqmaLaw {
        let (control_tx, _) = watch::channel(None);
        let mut law = SqmaLaw::new(settings(key_file), control_tx, None);
        law.rng = fastrand::Rng::with_seed(7);
        law.history_base = dir.join("unravel-history");
        law.history_path = law.history_base.clone();
        let mut down = RateState::new(50000.0, 100, &mut law.rng);
        down.current_kbps = 30000.0;
        let mut up = RateState::new(20000.0, 100, &mut law.rng);
        up.current_kbps = 12000.0;
        law.download = Some(down);
        law.upload = Some(up);
        law
    }

    fn add(state: &mut RateState, samples: &[(f64, u64)]) {
        for (r, t) in samples {
            state.safe_rates.pop_front();
            state.safe_rates.push_back(*r);
            state.sample_times.push_back(*t);
        }
        state.observed += samples.len();
    }

    /// Write the key file with an explicit mtime, as a writer would (temp + rename).
    fn write_key(file: &Path, text: &str, mtime_secs: u64) {
        let tmp = file.with_extension("new");
        std::fs::write(&tmp, text).unwrap();
        let f = std::fs::File::options().write(true).open(&tmp).unwrap();
        f.set_modified(UNIX_EPOCH + Duration::from_secs(mtime_secs)).unwrap();
        drop(f);
        std::fs::rename(&tmp, file).unwrap();
    }

    fn up(law: &SqmaLaw) -> Vec<(f64, u64)> {
        law.upload.as_ref().unwrap().real_samples()
    }

    #[test]
    fn key_change_swaps_histories() {
        let dir = temp_dir("swap");
        let key = dir.0.join("key");
        let mut law = law(&dir.0, key.to_str().unwrap());
        let now = unix_now();

        write_key(&key, "1363-200\n0\n", 1000);
        law.poll_history_key();
        assert_eq!(law.history_key.as_deref(), Some("1363-200"));
        assert_eq!(law.history_path, dir.0.join("unravel-history.1363-200"));

        add(law.upload.as_mut().unwrap(), &[(6200.0, now - 30), (6400.0, now - 20)]);
        write_key(&key, &format!("3501-320\n{now}\n"), 1001);
        law.poll_history_key();

        assert_eq!(law.history_key.as_deref(), Some("3501-320"));
        assert_eq!(law.history_path, dir.0.join("unravel-history.3501-320"));
        let st = law.upload.as_ref().unwrap();
        assert_eq!(st.observed, 0, "a new key starts from seeds only");
        assert_eq!(st.current_kbps, 12000.0, "current rate is left alone");
        assert_eq!(law.download.as_ref().unwrap().current_kbps, 30000.0);

        let saved = std::fs::read_to_string(dir.0.join("unravel-history.1363-200")).unwrap();
        let dirs = parse_history(&saved, unix_now(), 100).unwrap();
        let upload = dirs.iter().find(|d| d.0 == "upload").unwrap();
        assert_eq!(upload.2, vec![(6200.0, now - 30), (6400.0, now - 20)]);
    }

    #[test]
    fn returning_to_a_key_restores_its_samples() {
        let dir = temp_dir("return");
        let key = dir.0.join("key");
        let mut law = law(&dir.0, key.to_str().unwrap());
        let now = unix_now();

        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        add(law.upload.as_mut().unwrap(), &[(6200.0, now - 100), (6300.0, now - 90)]);

        write_key(&key, &format!("B\n{now}\n"), 1001);
        law.poll_history_key();
        add(law.upload.as_mut().unwrap(), &[(9000.0, now - 5)]);

        write_key(&key, &format!("A\n{now}\n"), 1002);
        law.poll_history_key();
        assert_eq!(up(&law), vec![(6200.0, now - 100), (6300.0, now - 90)]);
        assert_eq!(law.upload.as_ref().unwrap().observed, 2);

        write_key(&key, &format!("B\n{now}\n"), 1003);
        law.poll_history_key();
        assert_eq!(up(&law), vec![(9000.0, now - 5)]);
    }

    #[test]
    fn samples_in_the_ambiguous_window_are_dropped() {
        let dir = temp_dir("window");
        let key = dir.0.join("key");
        let mut law = law(&dir.0, key.to_str().unwrap());
        let now = unix_now();

        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        // Last confirmed on A at now - 10; the sample at now - 4 may be from B.
        add(law.upload.as_mut().unwrap(), &[(6200.0, now - 20), (6300.0, now - 10), (9000.0, now - 4)]);
        write_key(&key, &format!("B\n{}\n", now - 10), 1001);
        law.poll_history_key();

        write_key(&key, &format!("A\n{now}\n"), 1002);
        law.poll_history_key();
        assert_eq!(up(&law), vec![(6200.0, now - 20), (6300.0, now - 10)]);
    }

    #[test]
    fn unknown_change_time_drops_nothing() {
        let dir = temp_dir("unknown");
        let key = dir.0.join("key");
        let mut law = law(&dir.0, key.to_str().unwrap());
        let now = unix_now();

        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        add(law.upload.as_mut().unwrap(), &[(6200.0, now - 20), (9000.0, now - 4)]);
        write_key(&key, "B\n", 1001);
        law.poll_history_key();
        write_key(&key, "A\n0\n", 1002);
        law.poll_history_key();
        assert_eq!(up(&law), vec![(6200.0, now - 20), (9000.0, now - 4)]);
    }

    #[test]
    fn missing_or_garbage_key_file_keeps_v3_behaviour() {
        let dir = temp_dir("garbage");
        let key = dir.0.join("key");
        let mut law = law(&dir.0, key.to_str().unwrap());

        law.poll_history_key();
        assert_eq!(law.history_key, None);
        assert_eq!(law.history_path, dir.0.join("unravel-history"));

        for (i, text) in ["", "\n0\n", "has space\n0\n", "../etc\n0\n", &"x".repeat(65)].iter().enumerate() {
            write_key(&key, text, 1000 + i as u64);
            law.poll_history_key();
            assert_eq!(law.history_key, None, "{text:?}");
            assert_eq!(law.history_path, dir.0.join("unravel-history"));
        }
        assert!(law.history_key_warned);
    }

    #[test]
    fn garbage_after_a_key_keeps_the_current_key() {
        let dir = temp_dir("garbage-after");
        let key = dir.0.join("key");
        let mut law = law(&dir.0, key.to_str().unwrap());
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        write_key(&key, "not/a/key\n", 1001);
        law.poll_history_key();
        std::fs::remove_file(&key).unwrap();
        law.poll_history_key();
        assert_eq!(law.history_key.as_deref(), Some("A"));
    }

    #[test]
    fn unchanged_mtime_is_not_reread() {
        let dir = temp_dir("mtime");
        let key = dir.0.join("key");
        let mut law = law(&dir.0, key.to_str().unwrap());
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        write_key(&key, "B\n0\n", 1000);
        law.poll_history_key();
        assert_eq!(law.history_key.as_deref(), Some("A"));
    }

    #[test]
    fn first_key_adopts_samples_learned_before_it() {
        let dir = temp_dir("adopt");
        let key = dir.0.join("key");
        let mut law = law(&dir.0, key.to_str().unwrap());
        add(law.upload.as_mut().unwrap(), &[(6200.0, 5)]);
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        assert_eq!(up(&law), vec![(6200.0, 5)]);
    }

    #[test]
    fn first_key_at_startup_takes_over_the_single_history() {
        let dir = temp_dir("startup");
        let key = dir.0.join("key");
        let now = unix_now();
        let mut law = law(&dir.0, key.to_str().unwrap());
        law.download = None;
        law.upload = None;
        let v1 = format!("{HISTORY_HEADER_V1}\nsaved {now}\nsize 100\nupload 20000 2 6200 6300\n");
        std::fs::write(dir.0.join("unravel-history"), v1).unwrap();
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        assert_eq!(law.history_path, dir.0.join("unravel-history.A"));
        let mut st = RateState::new(20000.0, 100, &mut law.rng);
        law.restore_history("upload", 20000.0, &mut st);
        assert_eq!(st.real_samples(), vec![(6200.0, 0), (6300.0, 0)]);
        assert!(dir.0.join("unravel-history").exists(), "the single history is kept");
    }

    #[test]
    fn first_key_with_its_own_history_loads_it() {
        let dir = temp_dir("own");
        let key = dir.0.join("key");
        let now = unix_now();
        let mut law = law(&dir.0, key.to_str().unwrap());
        let body = history_body(100, &[("upload", 20000.0, vec![(7000.0, now - 60)])]);
        assert!(write_history(&dir.0.join("unravel-history.A"), &body));
        add(law.upload.as_mut().unwrap(), &[(6200.0, now - 5)]);
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        assert_eq!(up(&law), vec![(7000.0, now - 60)]);
        // What had been learned without a key is kept in the unkeyed file.
        let saved = std::fs::read_to_string(dir.0.join("unravel-history")).unwrap();
        let dirs = parse_history(&saved, unix_now(), 100).unwrap();
        assert_eq!(dirs.iter().find(|d| d.0 == "upload").unwrap().2, vec![(6200.0, now - 5)]);
    }

    #[test]
    fn a_stale_or_rebased_key_history_is_not_loaded() {
        let dir = temp_dir("stale");
        let key = dir.0.join("key");
        let now = unix_now();
        let mut law = law(&dir.0, key.to_str().unwrap());
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key();
        let other_base = history_body(100, &[("upload", 25000.0, vec![(7000.0, now - 60)])]);
        assert!(write_history(&dir.0.join("unravel-history.B"), &other_base));
        write_key(&key, "B\n0\n", 1001);
        law.poll_history_key();
        assert_eq!(law.upload.as_ref().unwrap().observed, 0);

        let old = format!(
            "{HISTORY_HEADER}\nsaved {}\n{}",
            now - HISTORY_MAX_AGE_SECS - 10,
            history_body(100, &[("upload", 20000.0, vec![(7000.0, 1)])])
        );
        std::fs::write(dir.0.join("unravel-history.C"), old).unwrap();
        write_key(&key, "C\n0\n", 1002);
        law.poll_history_key();
        assert_eq!(law.upload.as_ref().unwrap().observed, 0);
    }

    #[test]
    fn format_1_still_loads_with_time_zero() {
        let text = format!("{HISTORY_HEADER_V1}\nsaved 1000\nsize 100\nupload 20000 2 6200 6300\n");
        let dirs = parse_history(&text, 1010, 100).unwrap();
        assert_eq!(dirs[0].2, vec![(6200.0, 0), (6300.0, 0)]);
        // Time 0 means old: never dropped by a cutoff.
        assert_eq!(samples_up_to(dirs[0].2.clone(), 5), vec![(6200.0, 0), (6300.0, 0)]);
    }

    #[test]
    fn format_2_round_trips_times() {
        let body = history_body(100, &[("download", 50000.0, vec![(31000.0, 1700000000)])]);
        let text = format!("{HISTORY_HEADER}\nsaved 1000\n{body}");
        let dirs = parse_history(&text, 1010, 100).unwrap();
        assert_eq!(dirs, vec![("download".to_string(), 50000.0, vec![(31000.0, 1700000000)])]);
        let no_time = format!("{HISTORY_HEADER}\nsaved 1000\nsize 100\nupload 20000 1 6200\n");
        assert!(parse_history(&no_time, 1010, 100).is_none());
    }

    #[test]
    fn option_off_stays_on_the_single_history_file() {
        let dir = temp_dir("off");
        let key = dir.0.join("key");
        write_key(&key, "A\n0\n", 1000);
        let mut law = law(&dir.0, "");
        assert!(law.history_key_file.is_none());
        law.poll_history_key();
        assert_eq!(law.history_key, None);
        assert_eq!(law.history_path, dir.0.join("unravel-history"));
        add(law.upload.as_mut().unwrap(), &[(6200.0, 5)]);
        law.save_history(Instant::now());
        assert!(dir.0.join("unravel-history").exists());
        assert!(!dir.0.join("unravel-history.A").exists());
    }

    #[test]
    fn real_samples_tolerate_missing_times() {
        let mut rng = fastrand::Rng::with_seed(1);
        let mut st = RateState::new(20000.0, 10, &mut rng);
        for r in [1.0, 2.0, 3.0] {
            st.safe_rates.pop_front();
            st.safe_rates.push_back(r);
        }
        st.observed = 3;
        st.sample_times.push_back(99);
        assert_eq!(st.real_samples(), vec![(1.0, 0), (2.0, 0), (3.0, 99)]);
    }

    #[test]
    fn keys_are_plain_text_only() {
        assert!(valid_history_key("1363-200"));
        assert!(valid_history_key("a.b_c:d-9"));
        assert!(!valid_history_key(""));
        assert!(!valid_history_key("a/b"));
        assert!(!valid_history_key("a b"));
        assert!(!valid_history_key(&"x".repeat(65)));
        assert_eq!(parse_history_key("A\n123\n"), Some(("A".into(), 123)));
        assert_eq!(parse_history_key("A\n"), Some(("A".into(), 0)));
        assert_eq!(parse_history_key("A\njunk\n"), Some(("A".into(), 0)));
    }
}
