//! Counts and times per candidate source, collected for one `simplify` call; `bench`
//! writes them out per case when `EGGY_STATS` names a file.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::time::Instant;

/// Key → (count, seconds).
static COUNTS: Mutex<BTreeMap<String, (u64, f64)>> = Mutex::new(BTreeMap::new());
/// Printed form of each pre-pass candidate of the current call → its source.
static LABELS: Mutex<BTreeMap<String, String>> = Mutex::new(BTreeMap::new());

/// Counts `key` once and adds `secs` to its time.
pub fn add(key: &str, secs: f64) {
    let mut c = COUNTS.lock().unwrap();
    let e = c.entry(key.to_string()).or_insert((0, 0.0));
    e.0 += 1;
    e.1 += secs;
}

/// Seconds since `start`.
pub fn since(start: Instant) -> f64 {
    start.elapsed().as_secs_f64()
}

/// Remembers that the pre-pass candidate `egg` came from `source`.
pub fn label(egg: &str, source: &str) {
    LABELS.lock().unwrap().entry(egg.to_string()).or_insert_with(|| source.to_string());
}

/// The source `label` gave `egg`, if any.
pub fn source_of(egg: &str) -> Option<String> {
    LABELS.lock().unwrap().get(egg).cloned()
}

/// The counts so far, cleared with the labels.
pub fn take() -> BTreeMap<String, (u64, f64)> {
    LABELS.lock().unwrap().clear();
    std::mem::take(&mut *COUNTS.lock().unwrap())
}
