//! VM trace normalization helpers for cross-VM comparison.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Normalized event for cross-VM comparison.
/// Drops absolute session IDs (may differ), normalizes to session index.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NormalizedEvent {
    pub kind: String,
    pub session_index: usize,
    pub sender: String,
    pub receiver: String,
    pub label: Option<String>,
}

/// Per-session trace: the subsequence of events for one session.
pub type SessionTrace = Vec<NormalizedEvent>;

/// Extract per-session traces from a flat event list.
#[must_use]
pub fn partition_by_session(events: &[NormalizedEvent]) -> BTreeMap<usize, SessionTrace> {
    let mut map: BTreeMap<usize, SessionTrace> = BTreeMap::new();
    for ev in events {
        map.entry(ev.session_index).or_default().push(ev.clone());
    }
    map
}
