// SPDX-FileCopyrightText: 2026-Present Nils Andreas Svee mailto:contact@lochnair.net (github @Lochnair)
//
// SPDX-License-Identifier: MPL-2.0

use std::{
    collections::{HashMap, VecDeque},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use anyhow::Context;
use log::{debug, info, warn};
use serde::Deserialize;

use crate::{
    diagnostics::{DiagnosticRecord, DiagnosticsSender, DirectionStatistics, SpeedHistory},
    error::ChannelClosed,
    law::{Cadence, Law, LawContext, LawStore},
    measurement::model::{
        MeasurementEvent, MeasurementOutcome, MeasurementTarget, OneWayLatency, OneWayRejection,
        OneWayStatus,
    },
    metrics::Metric,
    runtime::{Direction, Shaper},
    settings::{
        ValidationReport, deserialize_flex_bool, validate_greater_than_zero_f64,
        validate_zero_or_greater_f64,
    },
};

const BASELINE_HALF_LIFE_SECS: f64 = 135.0;
const RECENT_HALF_LIFE_SECS: f64 = 0.4;
const STALE_AFTER: Duration = Duration::from_secs(30);
// Let queues drain before rebuilding all baselines after a local clock step.
const MEASUREMENT_SETTLE_TIME: Duration = Duration::from_secs(5);

// With save_history set, the recorded safe rates are saved in the law's store
// so a service restart does not throw them away. With history_key_file set as
// well, each key keeps its own history in history.<key>.txt.
const HISTORY_FILE: &str = "history.txt";
const HISTORY_SAVE_EVERY: Duration = Duration::from_secs(30);
const HISTORY_MAX_AGE_SECS: u64 = 6 * 3600;
// Format 2 stores each recorded rate with its unix time (rate@time).
// Format 1 (bare rates) is still read, with time 0.
const HISTORY_HEADER: &str = "unravel-history 2";
const HISTORY_HEADER_V1: &str = "unravel-history 1";

/// SQMA's own configuration, read from `law.sqma`.
#[derive(Clone, Debug, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub(crate) struct SqmaSettings {
    pub(crate) download_delay_ms: f64,
    pub(crate) high_load_level: f64,
    pub(crate) min_change_interval: f64,
    pub(crate) speed_hist_size: u32,
    /// Probe and traffic sampling period, in seconds.
    pub(crate) tick_interval: f64,
    pub(crate) upload_delay_ms: f64,
    /// At or below low_load_level, each cut can take the rate no lower than
    /// this fraction of the current rate (0 = off, the upstream behaviour).
    pub(crate) low_load_cut_floor: f64,
    /// When the delay is under the threshold and load is at or below
    /// low_load_level, step the rate towards the median of the recorded
    /// safe rates by this percentage of the base rate per evaluation
    /// (0 = off, the upstream behaviour).
    pub(crate) idle_recovery_percent: f64,
    /// Load at or below which low_load_cut_floor and idle_recovery_percent
    /// act. Above it, the decision is unchanged from upstream.
    pub(crate) low_load_level: f64,
    /// Keep the recorded safe rates across a service restart. They are read
    /// at startup if under 6 h old and saved with the same speed_hist_size
    /// and base rate. Off by default, the upstream behaviour.
    #[serde(deserialize_with = "deserialize_flex_bool")]
    pub(crate) save_history: bool,
    /// File naming the current history key (line 1) and when the previous
    /// key was last confirmed (line 2, unix seconds). Each key keeps its own
    /// safe-rate history. Needs save_history. Unset = off, one history for
    /// everything.
    pub(crate) history_key_file: Option<String>,
}

impl Default for SqmaSettings {
    fn default() -> Self {
        Self {
            download_delay_ms: 15.0,
            high_load_level: 0.8,
            min_change_interval: 0.5,
            speed_hist_size: 100,
            tick_interval: 0.5,
            upload_delay_ms: 15.0,
            low_load_cut_floor: 0.0,
            idle_recovery_percent: 0.0,
            low_load_level: 0.3,
            save_history: false,
            history_key_file: None,
        }
    }
}

impl SqmaSettings {
    /// Reads the `law.sqma` table; an absent table means all defaults.
    fn from_config(config: Option<config::Value>) -> anyhow::Result<Self> {
        let settings = match config {
            Some(value) => value
                .try_deserialize::<Self>()
                .context("Reading law.sqma settings")?,
            None => Self::default(),
        };
        let mut report = ValidationReport::default();
        settings.validate(&mut report);
        report.finish()?;
        Ok(settings)
    }

    fn validate(&self, report: &mut ValidationReport) {
        validate_zero_or_greater_f64(report, "law.sqma.download_delay_ms", self.download_delay_ms);

        validate_zero_or_greater_f64(report, "law.sqma.upload_delay_ms", self.upload_delay_ms);

        let high_load_level_valid =
            validate_zero_or_greater_f64(report, "law.sqma.high_load_level", self.high_load_level);

        if validate_greater_than_zero_f64(
            report,
            "law.sqma.min_change_interval",
            self.min_change_interval,
        ) && !Duration::try_from_secs_f64(self.min_change_interval)
            .is_ok_and(|interval| !interval.is_zero())
        {
            report.error(
                "law.sqma.min_change_interval",
                "must convert to a nonzero representable duration",
            );
        }

        if !Duration::try_from_secs_f64(self.tick_interval)
            .is_ok_and(|period| !period.is_zero() && Instant::now().checked_add(period).is_some())
        {
            report.error(
                "law.sqma.tick_interval",
                "must be a nonzero representable duration",
            );
        }

        if !(0.0..1.0).contains(&self.low_load_cut_floor) {
            report.error(
                "law.sqma.low_load_cut_floor",
                "must be at least 0 and below 1",
            );
        }

        if !(0.0..=100.0).contains(&self.idle_recovery_percent) {
            report.error(
                "law.sqma.idle_recovery_percent",
                "must be between 0 and 100",
            );
        }

        if !(0.0..=1.0).contains(&self.low_load_level) {
            report.error("law.sqma.low_load_level", "must be between 0 and 1");
        }

        if self.speed_hist_size == 0 {
            report.error("law.sqma.speed_hist_size", "must be greater than 0");
        }

        if let Some(path) = self.history_key_file.as_deref().map(str::trim)
            && !path.is_empty()
        {
            if !path.starts_with('/') {
                report.error("law.sqma.history_key_file", "must be an absolute path");
            } else if !self.save_history {
                report.warning(
                    "law.sqma.history_key_file",
                    "has no effect without save_history",
                );
            }
        }

        if high_load_level_valid {
            if self.high_load_level == 0.0 {
                report.warning(
                    "law.sqma.high_load_level",
                    "0 causes any positive load to be treated as high load",
                );
            } else if self.high_load_level > 1.0 {
                report.warning(
                    "law.sqma.high_load_level",
                    format!(
                        "{} requires utilisation to exceed the current shaper rate \
                         before the high-load threshold is reached",
                        self.high_load_level,
                    ),
                );
            }
        }
    }
}

struct RateState {
    current_kbps: f64,
    safe_rates: VecDeque<f64>,
    /// How many safe rates are recorded rather than startup placeholders.
    /// Recorded rates sit at the back.
    observed: usize,
    /// Base the history was learned against.
    base_kbps: f64,
    /// Unix time of each recorded rate, oldest first, matched to the back
    /// of safe_rates. A recorded rate with no time here counts as time 0.
    sample_times: VecDeque<u64>,
}

/// One saved direction: name, base and the recorded rates as (rate, unix time).
type SavedDirection = (String, f64, Vec<(f64, u64)>);

/// One direction to save: name, base and the recorded rates as (rate, unix time).
type DirectionSamples<'a> = (&'a str, f64, Vec<(f64, u64)>);

/// The saved history, without the header and time lines.
/// One line per direction: `<name> <base> <count> <rate>@<time>...`, recorded rates only.
fn history_body(size: usize, dirs: &[DirectionSamples]) -> String {
    let mut body = format!("size {size}\n");
    for (name, base, samples) in dirs {
        let recorded: Vec<String> = samples.iter().map(|(r, t)| format!("{r}@{t}")).collect();
        body.push_str(&format!(
            "{name} {base} {} {}\n",
            recorded.len(),
            recorded.join(" ")
        ));
    }
    body
}

/// One saved rate: `<rate>@<time>` in format 2, a bare rate (time 0) in format 1.
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
        let samples: Vec<(f64, u64)> = words
            .map(|w| parse_sample(w, with_time))
            .collect::<Option<_>>()?;
        if !(base.is_finite() && base > 0.0)
            || samples.len() != count
            || count > size
            || samples
                .iter()
                .any(|(r, _)| !r.is_finite() || *r <= 0.0 || *r > 10.0 * base)
        {
            return None;
        }
        dirs.push((name, base, samples));
    }
    Some(dirs)
}

/// Put saved recorded rates at the back of the history, oldest first.
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

/// Drop the recorded rates taken after `cutoff` (unix seconds).
fn samples_up_to(samples: Vec<(f64, u64)>, cutoff: u64) -> Vec<(f64, u64)> {
    samples.into_iter().filter(|(_, t)| *t <= cutoff).collect()
}

/// A history key is plain text: 1-64 of A-Z a-z 0-9 . _ : -
fn valid_history_key(key: &str) -> bool {
    (1..=64).contains(&key.len())
        && key
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b':' | b'-'))
}

/// Parse a key file: line 1 the key, line 2 (optional) the unix time the
/// previous key was last confirmed, 0 or missing = unknown.
fn parse_history_key(text: &str) -> Option<(String, u64)> {
    let mut lines = text.lines();
    let key = lines.next()?.trim();
    if !valid_history_key(key) {
        return None;
    }
    let confirmed = lines
        .next()
        .and_then(|l| l.trim().parse().ok())
        .unwrap_or(0);
    Some((key.to_string(), confirmed))
}

/// The store file holding the history for `key`.
fn history_file_for(key: &str) -> String {
    format!("history.{key}.txt")
}

/// Write a history file through the law's store.
async fn write_history(store: &LawStore, name: &str, body: &str) -> bool {
    let text = format!("{HISTORY_HEADER}\nsaved {}\n{body}", unix_now());
    match store.write(name, &text).await {
        Ok(()) => true,
        Err(error) => {
            warn!("Could not save history: {error:#}");
            false
        }
    }
}

fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
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

    /// The recorded rates with their times, oldest first.
    fn recorded_samples(&self) -> Vec<(f64, u64)> {
        let skip = self.safe_rates.len() - self.observed;
        let missing = self.observed.saturating_sub(self.sample_times.len());
        let times = self
            .sample_times
            .iter()
            .skip(self.sample_times.len().saturating_sub(self.observed));
        let times = std::iter::repeat_n(&0, missing).chain(times);
        self.safe_rates
            .iter()
            .skip(skip)
            .copied()
            .zip(times.copied())
            .collect()
    }

    fn calculate_rate(
        &mut self,
        shaper: &Shaper,
        traffic_kbps: f64,
        deltas: &[f64],
        delay_threshold_ms: f64,
        settings: &SqmaSettings,
        rng: &mut fastrand::Rng,
    ) -> f64 {
        let mut next_kbps = self.current_kbps;

        if !deltas.is_empty() {
            let delta = deltas[deltas.len() / 2];
            let load = traffic_kbps / self.current_kbps;

            if delta > 0.0 {
                if delta < delay_threshold_ms && load > settings.high_load_level {
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
                }

                if delta > delay_threshold_ms {
                    let rnd_rate = self.safe_rates[rng.usize(..self.safe_rates.len())];
                    next_kbps = rnd_rate.min(0.9 * traffic_kbps);

                    // At low load, each cut can take the rate no lower than
                    // low_load_cut_floor times the current rate.
                    if settings.low_load_cut_floor > 0.0 && load <= settings.low_load_level {
                        next_kbps = next_kbps.max(self.current_kbps * settings.low_load_cut_floor);
                    }
                }
            }

            // With the delay at or under the threshold and the link not
            // busy, step towards the median of the safe-rate history. This
            // sits outside the delta > 0 check, as the median delta on an
            // idle link can be exactly 0. Only recorded rates count: the
            // startup placeholders would pull an idle link towards about 85%
            // of the base rate after every restart.
            if settings.idle_recovery_percent > 0.0
                && self.observed > 0
                && delta <= delay_threshold_ms
                && load <= settings.low_load_level
            {
                let skip = self.safe_rates.len() - self.observed;
                let mut rates: Vec<f64> = self.safe_rates.iter().skip(skip).copied().collect();
                rates.sort_by(f64::total_cmp);
                let target = rates[rates.len() / 2].max(shaper.min_kbps);
                let step = shaper.base_kbps * settings.idle_recovery_percent / 100.0;
                if self.current_kbps < target {
                    next_kbps = (self.current_kbps + step).min(target);
                } else if self.current_kbps > target {
                    next_kbps = (self.current_kbps - step).max(target);
                }
            }
        }

        next_kbps
            .max(shaper.min_kbps)
            .min(shaper.max_kbps.unwrap_or(f64::INFINITY))
            .floor()
    }
}

pub(crate) struct SqmaLaw {
    settings: SqmaSettings,

    reflectors: HashMap<MeasurementTarget, ReflectorState>,
    /// Also retained after settling to exclude late replies to older probes.
    measurements_after: Option<Instant>,

    download: Option<RateState>,
    upload: Option<RateState>,

    fast_factor: f64,
    slow_factor: f64,

    rng: fastrand::Rng,
    diagnostics: Option<DiagnosticsSender>,

    // Restart-proof safe-rate history, when save_history is on.
    // history_name is HISTORY_FILE, or history.<key>.txt once a key is known.
    history_name: String,
    history_saved_at: Option<Instant>,
    history_saved_body: String,

    // Optional per-key histories, the key read from a file.
    history_key_file: Option<std::path::PathBuf>,
    history_key_mtime: Option<SystemTime>,
    history_key: Option<String>,
    history_key_warned: bool,

    // Missing reflector data is checked every tick; warn once per episode.
    warned_few_deltas: bool,
    warned_no_deltas: bool,
}

#[async_trait::async_trait]
impl Law for SqmaLaw {
    fn name(&self) -> &str {
        "sqma"
    }

    fn cadence(&self) -> Cadence {
        let tick = Duration::from_secs_f64(self.settings.tick_interval);
        Cadence {
            probe: tick,
            traffic: tick,
        }
    }

    async fn run(mut self: Box<Self>, mut ctx: LawContext) -> anyhow::Result<()> {
        let interval = Duration::from_secs_f64(self.settings.min_change_interval);

        let mut ticker = tokio::time::interval_at(
            tokio::time::Instant::now() + Duration::from_secs(10),
            interval,
        );

        ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);

        let mut initialized = false;

        loop {
            tokio::select! {
                biased;
                changed = ctx.clock_steps.changed() => {
                    changed.context("Clock-step channel closed")?;
                    let step = *ctx.clock_steps.borrow_and_update();
                    if let Some(step) = step {
                        warn!("SQMA resetting after local clock step of {:.3}s detected {:?} ago",
                            step.delta_secs, step.detected_at.elapsed());
                        self.recover_after_clock_step(&ctx)?;
                    }
                }

                _ = ticker.tick() => {
                    if self.measurements_after.is_some_and(|until| Instant::now() < until) {
                        continue;
                    }
                    if !initialized {
                        self.initialize(&ctx).await?;
                        initialized = true;
                    } else {
                        self.evaluate(&mut ctx).await?;
                    }

                    self.reflectors.retain(|_, state| {
                        Instant::now().saturating_duration_since(state.last_usable_at) <= STALE_AFTER
                    });
                }

                event = ctx.measurements.recv() => {
                    match event {
                        Ok(event) => self.observe(event, &ctx)?,
                        Err(tokio::sync::broadcast::error::RecvError::Lagged(count)) => {
                            warn!("Control law missed {count} measurement events");
                            ctx.metrics.send(Metric::event("measurement_lag", "control_law", None));
                        }
                        Err(tokio::sync::broadcast::error::RecvError::Closed) => {
                            return Err(ChannelClosed).context("Measurement channel closed");
                        }
                    }
                }
            }
        }
    }
}

impl SqmaLaw {
    /// `config` is the `law.sqma` table, if the configuration has one.
    pub fn new(
        config: Option<config::Value>,
        diagnostics: Option<DiagnosticsSender>,
    ) -> anyhow::Result<Self> {
        let settings = SqmaSettings::from_config(config)?;
        let tick = settings.tick_interval;
        // Per-key histories are saved histories, so they need save_history.
        let history_key_file = settings
            .history_key_file
            .as_deref()
            .map(str::trim)
            .filter(|path| !path.is_empty() && settings.save_history)
            .map(std::path::PathBuf::from);

        Ok(Self {
            settings,
            reflectors: HashMap::new(),
            measurements_after: None,
            download: None,
            upload: None,
            fast_factor: (0.5_f64.ln() / (RECENT_HALF_LIFE_SECS / tick)).exp(),
            slow_factor: (0.5_f64.ln() / (BASELINE_HALF_LIFE_SECS / tick)).exp(),
            rng: fastrand::Rng::new(),
            diagnostics,
            history_name: HISTORY_FILE.to_string(),
            history_saved_at: None,
            history_saved_body: String::new(),
            history_key_file,
            history_key_mtime: None,
            history_key: None,
            history_key_warned: false,
            warned_few_deltas: false,
            warned_no_deltas: false,
        })
    }

    /// Put back the recorded rates saved before a restart, or for a key.
    async fn restore_history(
        &self,
        store: &LawStore,
        name: &str,
        base_kbps: f64,
        state: &mut RateState,
    ) {
        if !self.settings.save_history {
            return;
        }
        let text = match store.read(&self.history_name).await {
            Ok(Some(text)) => text,
            Ok(None) => return,
            Err(error) => {
                warn!("Not restoring saved history: {error:#}");
                return;
            }
        };
        let size = state.safe_rates.len();
        let Some(dirs) = parse_history(&text, unix_now(), size) else {
            warn!("Ignoring saved history: unreadable, stale or a different history size");
            return;
        };
        let Some((_, saved_base, samples)) = dirs.iter().find(|(n, _, _)| n == name) else {
            return;
        };
        if *saved_base != base_kbps {
            info!("Not restoring {name} history: base was {saved_base}, now {base_kbps}");
            return;
        }
        restore_samples(state, samples);
        info!("Restored {} recorded {name} safe rates", samples.len());
    }

    /// Write the recorded rates out, at most every 30 s and only if they changed.
    async fn save_history(&mut self, store: &LawStore, now: Instant) {
        if !self.settings.save_history {
            return;
        }
        if self
            .history_saved_at
            .is_some_and(|t| now.saturating_duration_since(t) < HISTORY_SAVE_EVERY)
        {
            return;
        }
        self.history_saved_at = Some(now);
        let body = self.current_body(None);
        if body == self.history_saved_body {
            return;
        }
        if write_history(store, &self.history_name, &body).await {
            self.history_saved_body = body;
        }
    }

    /// The history body for both directions, without rates after `cutoff`.
    fn current_body(&self, cutoff: Option<u64>) -> String {
        let mut dirs = vec![];
        let mut size = 0;
        for (name, state) in [
            ("download", self.download.as_ref()),
            ("upload", self.upload.as_ref()),
        ] {
            if let Some(state) = state {
                size = state.safe_rates.len();
                let mut samples = state.recorded_samples();
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
    async fn poll_history_key(&mut self, store: &LawStore) {
        let Some(file) = self.history_key_file.clone() else {
            return;
        };
        let Ok(mtime) = tokio::fs::metadata(&file).await.and_then(|m| m.modified()) else {
            return;
        };
        if self.history_key_mtime == Some(mtime) {
            return;
        }
        self.history_key_mtime = Some(mtime);
        let text = tokio::fs::read_to_string(&file).await.ok();
        let Some((key, confirmed)) = text.as_deref().and_then(parse_history_key) else {
            if !self.history_key_warned {
                warn!(
                    "Ignoring history key file {}: line 1 is not a valid key",
                    file.display()
                );
                self.history_key_warned = true;
            }
            return;
        };
        self.history_key_warned = false;
        if self.history_key.as_deref() == Some(key.as_str()) {
            return;
        }
        self.switch_history_key(store, key, confirmed).await;
    }

    async fn switch_history_key(&mut self, store: &LawStore, key: String, confirmed: u64) {
        let old_name = self.history_name.clone();
        let new_name = history_file_for(&key);
        let new_text = match store.read(&new_name).await {
            Ok(text) => text,
            Err(error) => {
                warn!("Not switching history key to {key}: {error:#}");
                return;
            }
        };
        let have_state = self.download.is_some() || self.upload.is_some();

        // Before the first key, adopt what has been learned so far unless the
        // key already has its own history.
        if self.history_key.is_none() && new_text.is_none() {
            // At startup nothing is in memory yet: file the single history
            // under the first key so it is still loaded.
            if !have_state {
                match store.read(&old_name).await {
                    Ok(Some(text)) => {
                        if let Err(error) = store.write(&new_name, &text).await {
                            warn!("Could not copy {old_name} to {new_name}: {error:#}");
                        }
                    }
                    Ok(None) => {}
                    Err(error) => warn!("Could not read {old_name}: {error:#}"),
                }
            }
            info!("History key is now {key}");
            self.history_key = Some(key);
            self.history_name = new_name;
            self.history_saved_body.clear();
            self.history_saved_at = None;
            return;
        }

        if have_state {
            let cutoff = (confirmed > 0).then_some(confirmed);
            let body = self.current_body(cutoff);
            write_history(store, &old_name, &body).await;
        }

        info!(
            "History key {} -> {key}",
            self.history_key.as_deref().unwrap_or("(none)")
        );
        self.history_key = Some(key);
        self.history_name = new_name;
        self.history_saved_body.clear();
        self.history_saved_at = None;

        let size = self.settings.speed_hist_size;
        for name in ["download", "upload"] {
            let slot = if name == "download" {
                &self.download
            } else {
                &self.upload
            };
            let Some(old) = slot.as_ref() else {
                continue;
            };
            let (base_kbps, current_kbps) = (old.base_kbps, old.current_kbps);
            let mut state = RateState::new(base_kbps, size, &mut self.rng);
            state.current_kbps = current_kbps;
            self.restore_history(store, name, base_kbps, &mut state)
                .await;
            if name == "download" {
                self.download = Some(state);
            } else {
                self.upload = Some(state);
            }
        }
    }

    fn recover_after_clock_step(&mut self, ctx: &LawContext) -> anyhow::Result<()> {
        self.reflectors.clear();
        for (direction, state) in [
            (Direction::Download, self.download.as_mut()),
            (Direction::Upload, self.upload.as_mut()),
        ] {
            if let Some(shaper) = ctx.shaper(direction) {
                ctx.set_rate(direction, shaper.min_kbps)?;
                if let Some(state) = state {
                    state.current_kbps = shaper.min_kbps;
                }
            }
        }
        // Start the hold after lowering both rates, not when Runtime detected the step.
        self.measurements_after = Some(Instant::now() + MEASUREMENT_SETTLE_TIME);
        ctx.metrics.send(Metric::event(
            "measurement_recovery",
            "local_clock_step",
            None,
        ));
        Ok(())
    }

    async fn initialize(&mut self, ctx: &super::LawContext) -> anyhow::Result<()> {
        let size = self.settings.speed_hist_size;
        self.poll_history_key(ctx.store()).await;

        if let Some(shaper) = ctx.shaper(Direction::Download) {
            let initial = if self.measurements_after.is_some() {
                shaper.min_kbps
            } else {
                (shaper.base_kbps * 0.6).max(shaper.min_kbps)
            };

            ctx.set_rate(Direction::Download, initial)?;

            let mut state = RateState::new(shaper.base_kbps, size, &mut self.rng);
            state.current_kbps = initial;
            self.restore_history(ctx.store(), "download", shaper.base_kbps, &mut state)
                .await;

            self.download = Some(state);
        }

        if let Some(shaper) = ctx.shaper(Direction::Upload) {
            let initial = if self.measurements_after.is_some() {
                shaper.min_kbps
            } else {
                (shaper.base_kbps * 0.6).max(shaper.min_kbps)
            };

            ctx.set_rate(Direction::Upload, initial)?;

            let mut state = RateState::new(shaper.base_kbps, size, &mut self.rng);
            state.current_kbps = initial;
            self.restore_history(ctx.store(), "upload", shaper.base_kbps, &mut state)
                .await;

            self.upload = Some(state);
        }

        Ok(())
    }

    fn deltas(&self, targets: &[MeasurementTarget], now: Instant) -> (Vec<f64>, Vec<f64>) {
        let mut down = Vec::with_capacity(targets.len());
        let mut up = Vec::with_capacity(targets.len());

        let max_age = Duration::from_secs_f64(self.settings.tick_interval * 2.0);

        for target in targets {
            let Some(state) = self.reflectors.get(target) else {
                continue;
            };

            if !state.valid || now.saturating_duration_since(state.last_usable_at) >= max_age {
                continue;
            }

            let down_delta = state.recent.down - state.baseline.down;
            let up_delta = state.recent.up - state.baseline.up;

            down.push(down_delta);
            up.push(up_delta);

            debug!(
                "Reflector: {} ({:?}) down_delay: {} up_delay: {}",
                target.peer(),
                target.protocol(),
                down_delta,
                up_delta
            );
        }

        down.sort_by(f64::total_cmp);
        up.sort_by(f64::total_cmp);

        (down, up)
    }

    async fn evaluate(&mut self, ctx: &mut super::LawContext) -> anyhow::Result<()> {
        let now = Instant::now();
        self.poll_history_key(ctx.store()).await;

        let (down_deltas, up_deltas, target_count) = {
            let targets = ctx.applied.borrow().active_targets();
            let (down, up) = self.deltas(targets.as_slice(), now);
            (down, up, targets.len())
        };

        let minimum = ctx.num_reflectors().min(target_count);
        if target_count == 0 || down_deltas.len() < minimum || up_deltas.len() < minimum {
            if !self.warned_few_deltas {
                warn!(
                    "Not enough active delta values (D: {}, U: {}, need {})",
                    down_deltas.len(),
                    up_deltas.len(),
                    minimum
                );
                self.warned_few_deltas = true;
            }
        } else if self.warned_few_deltas {
            info!("Enough active delta values again");
            self.warned_few_deltas = false;
        }

        if down_deltas.is_empty() || up_deltas.is_empty() {
            if !self.warned_no_deltas {
                warn!("No reflector data available, dropping to minimum rates");
                self.warned_no_deltas = true;
            }
            ctx.metrics
                .send(Metric::event("reflector_unavailable", "", None));

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
        if self.warned_no_deltas {
            info!("Reflector data available again");
            self.warned_no_deltas = false;
        }

        let Some(traffic) = *ctx.traffic.borrow() else {
            // No traffic sample available. Retain current rates.
            ctx.metrics
                .send(Metric::event("traffic_sample_unavailable", "", None));
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
                self.settings.download_delay_ms,
            ),
            (
                Direction::Upload,
                self.upload.as_mut(),
                up_deltas.as_slice(),
                traffic.tx_kbps,
                self.settings.upload_delay_ms,
            ),
        ] {
            let (Some(state), Some(shaper)) = (state, ctx.shaper(direction)) else {
                continue;
            };

            let next = state.calculate_rate(
                shaper,
                traffic_kbps,
                deltas,
                delay_ms,
                &self.settings,
                &mut self.rng,
            );

            if next != state.current_kbps {
                ctx.set_rate(direction, next)?;
                state.current_kbps = next;
            }

            let delta = deltas[deltas.len() / 2];
            ctx.report_delay(direction, delta, Some(delay_ms))?;
            ctx.metrics.send(
                Metric::law("delta")
                    .tag("direction", direction.as_str())
                    .field("delta_delay", delta),
            );
        }

        self.save_history(ctx.store(), now).await;

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
        let MeasurementOutcome::Reply { one_way, .. } = event.outcome else {
            return Ok(());
        };
        if !ctx.applied.borrow().is_active(&event.target) {
            // Demoted targets can still have retained history. Consume their
            // reference invalidations without changing the active shaper rates.
            if let Some(state) = self.reflectors.get(&event.target)
                && event.started_at > state.last_started_at
                && one_way.is_some_and(|o| o.status == OneWayStatus::ReferenceChanged)
            {
                self.reflectors.remove(&event.target);
            }
            return Ok(());
        }
        let rejection = one_way.and_then(|latency| match latency.status {
            OneWayStatus::Unusable(reason) => Some(reason),
            _ => None,
        });
        let missing_timing =
            one_way.is_none() && !matches!(event.target, MeasurementTarget::IcmpEcho(_));
        if missing_timing || rejection.is_some() {
            // A delayed observation must not invalidate more recent history.
            if rejection != Some(OneWayRejection::OutOfOrder)
                && let Some(state) = self.reflectors.get_mut(&event.target)
                && event.started_at > state.last_started_at
            {
                state.valid = false;
                state.last_started_at = event.started_at;
            }
            if let Some(reason) = rejection {
                ctx.metrics.send(Metric::event(
                    "directional_rejected",
                    reason.reason(),
                    Some(event.target.peer()),
                ));
            }
            return Ok(());
        }
        let Some(rtt_ms) = event.rtt_ms() else {
            return Ok(());
        };
        if self
            .measurements_after
            .is_some_and(|after| event.started_at < after)
        {
            return Ok(());
        }
        if let Some(state) = self.reflectors.get(&event.target) {
            if event.started_at <= state.last_started_at {
                return Ok(());
            }
            if one_way.is_some_and(|o| o.status == OneWayStatus::ReferenceChanged) {
                // Rebuild only this target from its accepted new reference,
                // as for a newly active target. Other reflectors remain usable.
                self.reflectors.remove(&event.target);
                ctx.metrics.send(Metric::event(
                    "measurement_recovery",
                    "directional_reference_changed",
                    Some(event.target.peer()),
                ));
            }
        }
        let sample = EwmaStats::from_reply(rtt_ms, one_way);
        let state = self
            .reflectors
            .entry(event.target.clone())
            .or_insert_with(|| ReflectorState::new(sample, event.started_at, event.completed_at));
        state.update(
            sample,
            event.started_at,
            event.completed_at,
            self.slow_factor,
            self.fast_factor,
        );
        let reflector = event.target.peer().to_string();
        for (direction, baseline, recent) in [
            ("up", state.baseline.up, state.recent.up),
            ("down", state.baseline.down, state.recent.down),
        ] {
            ctx.metrics.send(
                Metric::law("baseline")
                    .tag("reflector", reflector.as_str())
                    .tag("direction", direction)
                    .field("baseline_ewma", baseline)
                    .field("recent_ewma", recent),
            );
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct EwmaStats {
    pub down: f64,
    pub up: f64,
}

impl EwmaStats {
    fn from_reply(rtt_ms: f64, one_way: Option<OneWayLatency>) -> Self {
        Self {
            down: one_way
                .map(|o| o.downlink.as_nanos() as f64 / 1000000.0)
                .unwrap_or(rtt_ms / 2.0),
            up: one_way
                .map(|o| o.uplink.as_nanos() as f64 / 1000000.0)
                .unwrap_or(rtt_ms / 2.0),
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
    /// Freshness of usable data, independent of raw reply liveness.
    pub last_usable_at: Instant,
    last_started_at: Instant,
    pub valid: bool,
}

impl ReflectorState {
    fn new(sample: EwmaStats, started_at: Instant, received_at: Instant) -> Self {
        Self {
            baseline: sample,
            recent: sample,
            last_usable_at: received_at,
            last_started_at: started_at,
            valid: true,
        }
    }

    fn update(
        &mut self,
        sample: EwmaStats,
        started_at: Instant,
        received_at: Instant,
        slow_factor: f64,
        fast_factor: f64,
    ) {
        if received_at.saturating_duration_since(self.last_usable_at) > STALE_AFTER {
            *self = Self::new(sample, started_at, received_at);
        }
        self.last_usable_at = received_at;
        self.last_started_at = started_at;
        self.baseline.update(sample, slow_factor);
        self.recent.update(sample, fast_factor);
        self.baseline.down = self.baseline.down.min(self.recent.down);
        self.baseline.up = self.baseline.up.min(self.recent.up);
        self.valid = true;
    }
}

#[cfg(test)]
mod per_cell_history_tests {
    use super::*;
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

    fn store(dir: &Path) -> LawStore {
        LawStore::new(dir, "sqma").unwrap()
    }

    /// Where the store keeps `name`.
    fn file(dir: &Path, name: &str) -> PathBuf {
        dir.join("sqma").join(name)
    }

    /// A law with save_history on, both directions set up, and `key_file`
    /// as its history key file ("" = off).
    fn law(key_file: &str) -> SqmaLaw {
        let mut law = SqmaLaw::new(None, None).unwrap();
        law.settings.save_history = true;
        law.history_key_file = (!key_file.is_empty()).then(|| PathBuf::from(key_file));
        law.rng = fastrand::Rng::with_seed(7);
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
        f.set_modified(UNIX_EPOCH + Duration::from_secs(mtime_secs))
            .unwrap();
        drop(f);
        std::fs::rename(&tmp, file).unwrap();
    }

    fn up(law: &SqmaLaw) -> Vec<(f64, u64)> {
        law.upload.as_ref().unwrap().recorded_samples()
    }

    #[tokio::test]
    async fn key_change_swaps_histories() {
        let dir = temp_dir("swap");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let mut law = law(key.to_str().unwrap());
        let now = unix_now();

        write_key(&key, "1363-200\n0\n", 1000);
        law.poll_history_key(&st).await;
        assert_eq!(law.history_key.as_deref(), Some("1363-200"));
        assert_eq!(law.history_name, "history.1363-200.txt");

        add(
            law.upload.as_mut().unwrap(),
            &[(6200.0, now - 30), (6400.0, now - 20)],
        );
        write_key(&key, &format!("3501-320\n{now}\n"), 1001);
        law.poll_history_key(&st).await;

        assert_eq!(law.history_key.as_deref(), Some("3501-320"));
        assert_eq!(law.history_name, "history.3501-320.txt");
        let state = law.upload.as_ref().unwrap();
        assert_eq!(state.observed, 0, "a new key starts from seeds only");
        assert_eq!(state.current_kbps, 12000.0, "current rate is left alone");
        assert_eq!(law.download.as_ref().unwrap().current_kbps, 30000.0);

        let saved = std::fs::read_to_string(file(&dir.0, "history.1363-200.txt")).unwrap();
        let dirs = parse_history(&saved, unix_now(), 100).unwrap();
        let upload = dirs.iter().find(|d| d.0 == "upload").unwrap();
        assert_eq!(upload.2, vec![(6200.0, now - 30), (6400.0, now - 20)]);
    }

    #[tokio::test]
    async fn returning_to_a_key_restores_its_samples() {
        let dir = temp_dir("return");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let mut law = law(key.to_str().unwrap());
        let now = unix_now();

        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        add(
            law.upload.as_mut().unwrap(),
            &[(6200.0, now - 100), (6300.0, now - 90)],
        );

        write_key(&key, &format!("B\n{now}\n"), 1001);
        law.poll_history_key(&st).await;
        add(law.upload.as_mut().unwrap(), &[(9000.0, now - 5)]);

        write_key(&key, &format!("A\n{now}\n"), 1002);
        law.poll_history_key(&st).await;
        assert_eq!(up(&law), vec![(6200.0, now - 100), (6300.0, now - 90)]);
        assert_eq!(law.upload.as_ref().unwrap().observed, 2);

        write_key(&key, &format!("B\n{now}\n"), 1003);
        law.poll_history_key(&st).await;
        assert_eq!(up(&law), vec![(9000.0, now - 5)]);
    }

    #[tokio::test]
    async fn samples_in_the_ambiguous_window_are_dropped() {
        let dir = temp_dir("window");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let mut law = law(key.to_str().unwrap());
        let now = unix_now();

        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        // Last confirmed on A at now - 10; the sample at now - 4 may be from B.
        add(
            law.upload.as_mut().unwrap(),
            &[(6200.0, now - 20), (6300.0, now - 10), (9000.0, now - 4)],
        );
        write_key(&key, &format!("B\n{}\n", now - 10), 1001);
        law.poll_history_key(&st).await;

        write_key(&key, &format!("A\n{now}\n"), 1002);
        law.poll_history_key(&st).await;
        assert_eq!(up(&law), vec![(6200.0, now - 20), (6300.0, now - 10)]);
    }

    #[tokio::test]
    async fn unknown_change_time_drops_nothing() {
        let dir = temp_dir("unknown");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let mut law = law(key.to_str().unwrap());
        let now = unix_now();

        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        add(
            law.upload.as_mut().unwrap(),
            &[(6200.0, now - 20), (9000.0, now - 4)],
        );
        write_key(&key, "B\n", 1001);
        law.poll_history_key(&st).await;
        write_key(&key, "A\n0\n", 1002);
        law.poll_history_key(&st).await;
        assert_eq!(up(&law), vec![(6200.0, now - 20), (9000.0, now - 4)]);
    }

    #[tokio::test]
    async fn missing_or_garbage_key_file_keeps_the_single_history() {
        let dir = temp_dir("garbage");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let mut law = law(key.to_str().unwrap());

        law.poll_history_key(&st).await;
        assert_eq!(law.history_key, None);
        assert_eq!(law.history_name, HISTORY_FILE);

        for (i, text) in [
            "",
            "\n0\n",
            "has space\n0\n",
            "../etc\n0\n",
            &"x".repeat(65),
        ]
        .iter()
        .enumerate()
        {
            write_key(&key, text, 1000 + i as u64);
            law.poll_history_key(&st).await;
            assert_eq!(law.history_key, None, "{text:?}");
            assert_eq!(law.history_name, HISTORY_FILE);
        }
        assert!(law.history_key_warned);
    }

    #[tokio::test]
    async fn garbage_after_a_key_keeps_the_current_key() {
        let dir = temp_dir("garbage-after");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let mut law = law(key.to_str().unwrap());
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        write_key(&key, "not/a/key\n", 1001);
        law.poll_history_key(&st).await;
        std::fs::remove_file(&key).unwrap();
        law.poll_history_key(&st).await;
        assert_eq!(law.history_key.as_deref(), Some("A"));
    }

    #[tokio::test]
    async fn unchanged_mtime_is_not_reread() {
        let dir = temp_dir("mtime");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let mut law = law(key.to_str().unwrap());
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        write_key(&key, "B\n0\n", 1000);
        law.poll_history_key(&st).await;
        assert_eq!(law.history_key.as_deref(), Some("A"));
    }

    #[tokio::test]
    async fn first_key_adopts_samples_learned_before_it() {
        let dir = temp_dir("adopt");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let mut law = law(key.to_str().unwrap());
        add(law.upload.as_mut().unwrap(), &[(6200.0, 5)]);
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        assert_eq!(up(&law), vec![(6200.0, 5)]);
    }

    #[tokio::test]
    async fn first_key_at_startup_takes_over_the_single_history() {
        let dir = temp_dir("startup");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let now = unix_now();
        let mut law = law(key.to_str().unwrap());
        law.download = None;
        law.upload = None;
        // What stock 0.6 writes (format 1), as carried over on the router.
        let v1 = format!("{HISTORY_HEADER_V1}\nsaved {now}\nsize 100\nupload 20000 2 6200 6300\n");
        st.write(HISTORY_FILE, &v1).await.unwrap();
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        assert_eq!(law.history_name, "history.A.txt");
        let mut state = RateState::new(20000.0, 100, &mut law.rng);
        law.restore_history(&st, "upload", 20000.0, &mut state).await;
        assert_eq!(state.recorded_samples(), vec![(6200.0, 0), (6300.0, 0)]);
        assert!(
            file(&dir.0, HISTORY_FILE).exists(),
            "the single history is kept"
        );
    }

    #[tokio::test]
    async fn first_key_with_its_own_history_loads_it() {
        let dir = temp_dir("own");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let now = unix_now();
        let mut law = law(key.to_str().unwrap());
        let body = history_body(100, &[("upload", 20000.0, vec![(7000.0, now - 60)])]);
        assert!(write_history(&st, "history.A.txt", &body).await);
        add(law.upload.as_mut().unwrap(), &[(6200.0, now - 5)]);
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        assert_eq!(up(&law), vec![(7000.0, now - 60)]);
        // What had been learned without a key is kept in the unkeyed file.
        let saved = std::fs::read_to_string(file(&dir.0, HISTORY_FILE)).unwrap();
        let dirs = parse_history(&saved, unix_now(), 100).unwrap();
        assert_eq!(
            dirs.iter().find(|d| d.0 == "upload").unwrap().2,
            vec![(6200.0, now - 5)]
        );
    }

    #[tokio::test]
    async fn a_stale_or_rebased_key_history_is_not_loaded() {
        let dir = temp_dir("stale");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        let now = unix_now();
        let mut law = law(key.to_str().unwrap());
        write_key(&key, "A\n0\n", 1000);
        law.poll_history_key(&st).await;
        let other_base = history_body(100, &[("upload", 25000.0, vec![(7000.0, now - 60)])]);
        assert!(write_history(&st, "history.B.txt", &other_base).await);
        write_key(&key, "B\n0\n", 1001);
        law.poll_history_key(&st).await;
        assert_eq!(law.upload.as_ref().unwrap().observed, 0);

        let old = format!(
            "{HISTORY_HEADER}\nsaved {}\n{}",
            now - HISTORY_MAX_AGE_SECS - 10,
            history_body(100, &[("upload", 20000.0, vec![(7000.0, 1)])])
        );
        st.write("history.C.txt", &old).await.unwrap();
        write_key(&key, "C\n0\n", 1002);
        law.poll_history_key(&st).await;
        assert_eq!(law.upload.as_ref().unwrap().observed, 0);
    }

    #[tokio::test]
    async fn format_1_still_loads_with_time_zero() {
        let text = format!("{HISTORY_HEADER_V1}\nsaved 1000\nsize 100\nupload 20000 2 6200 6300\n");
        let dirs = parse_history(&text, 1010, 100).unwrap();
        assert_eq!(dirs[0].2, vec![(6200.0, 0), (6300.0, 0)]);
        // Time 0 means old: never dropped by a cutoff.
        assert_eq!(
            samples_up_to(dirs[0].2.clone(), 5),
            vec![(6200.0, 0), (6300.0, 0)]
        );
    }

    #[tokio::test]
    async fn format_2_round_trips_times() {
        let body = history_body(100, &[("download", 50000.0, vec![(31000.0, 1700000000)])]);
        let text = format!("{HISTORY_HEADER}\nsaved 1000\n{body}");
        let dirs = parse_history(&text, 1010, 100).unwrap();
        assert_eq!(
            dirs,
            vec![("download".to_string(), 50000.0, vec![(31000.0, 1700000000)])]
        );
        let no_time = format!("{HISTORY_HEADER}\nsaved 1000\nsize 100\nupload 20000 1 6200\n");
        assert!(parse_history(&no_time, 1010, 100).is_none());
    }

    #[tokio::test]
    async fn option_off_stays_on_the_single_history_file() {
        let dir = temp_dir("off");
        let st = store(&dir.0);
        let key = dir.0.join("key");
        write_key(&key, "A\n0\n", 1000);
        let mut law = law("");
        law.poll_history_key(&st).await;
        assert_eq!(law.history_key, None);
        assert_eq!(law.history_name, HISTORY_FILE);
        add(law.upload.as_mut().unwrap(), &[(6200.0, 5)]);
        law.save_history(&st, Instant::now()).await;
        assert!(file(&dir.0, HISTORY_FILE).exists());
        assert!(!file(&dir.0, "history.A.txt").exists());
    }

    #[tokio::test]
    async fn real_samples_tolerate_missing_times() {
        let mut rng = fastrand::Rng::with_seed(1);
        let mut st = RateState::new(20000.0, 10, &mut rng);
        for r in [1.0, 2.0, 3.0] {
            st.safe_rates.pop_front();
            st.safe_rates.push_back(r);
        }
        st.observed = 3;
        st.sample_times.push_back(99);
        assert_eq!(st.recorded_samples(), vec![(1.0, 0), (2.0, 0), (3.0, 99)]);
    }

    #[tokio::test]
    async fn keys_are_plain_text_only() {
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

    #[test]
    fn key_file_needs_save_history_and_an_absolute_path() {
        // Without save_history it is only a warning, which does not fail.
        for (key_file, save, ok) in [
            (None, false, true),
            (Some(""), false, true),
            (Some("/tmp/unravel-history-key"), true, true),
            (Some("/tmp/unravel-history-key"), false, true),
            (Some("relative/key"), true, false),
        ] {
            let settings = SqmaSettings {
                history_key_file: key_file.map(Into::into),
                save_history: save,
                ..Default::default()
            };
            let mut report = ValidationReport::default();
            settings.validate(&mut report);
            assert_eq!(report.finish().is_ok(), ok, "{key_file:?}");
        }
    }

    #[test]
    fn key_file_is_off_without_save_history() {
        let mut config = config::Map::new();
        config.insert(
            "history_key_file".to_string(),
            config::Value::from("/tmp/unravel-history-key"),
        );
        let law = SqmaLaw::new(Some(config::Value::from(config)), None).unwrap();
        assert!(law.history_key_file.is_none());
    }

    #[test]
    fn uci_style_option_reaches_the_settings() {
        let mut config = config::Map::new();
        config.insert("save_history".to_string(), config::Value::from("1"));
        config.insert(
            "history_key_file".to_string(),
            config::Value::from("/tmp/unravel-history-key"),
        );
        let law = SqmaLaw::new(Some(config::Value::from(config)), None).unwrap();
        assert_eq!(
            law.history_key_file.as_deref(),
            Some(Path::new("/tmp/unravel-history-key"))
        );
    }
}
