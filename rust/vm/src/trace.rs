//! Trace normalization utilities.
//!
//! Session-local normalization reassigns ticks based on per-session
//! event counts. Global ticks are preserved for non-session events.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::session::SessionId;
use crate::vm::ObsEvent;

fn default_trace_schema_version() -> u32 {
    1
}

/// Version identifier for normalized trace payloads.
pub const TRACE_NORMALIZATION_SCHEMA_VERSION: u32 = 1;

/// Versioned normalized trace payload.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NormalizedTraceV1 {
    /// Schema version for normalized trace encoding.
    #[serde(default = "default_trace_schema_version")]
    pub schema_version: u32,
    /// Session-normalized observable events.
    pub events: Vec<ObsEvent>,
}

/// Extract the session id from an observable event, if present.
#[must_use]
pub fn obs_session(ev: &ObsEvent) -> Option<SessionId> {
    match ev {
        ObsEvent::Sent { session, .. }
        | ObsEvent::Received { session, .. }
        | ObsEvent::Opened { session, .. }
        | ObsEvent::Closed { session, .. }
        | ObsEvent::Acquired { session, .. }
        | ObsEvent::Released { session, .. }
        | ObsEvent::Transferred { session, .. }
        | ObsEvent::Forked { session, .. }
        | ObsEvent::Joined { session, .. }
        | ObsEvent::Aborted { session, .. }
        | ObsEvent::Tagged { session, .. }
        | ObsEvent::Checked { session, .. } => Some(*session),
        ObsEvent::Offered { edge, .. } | ObsEvent::Chose { edge, .. } => Some(edge.sid),
        ObsEvent::EpochAdvanced { sid, .. } => Some(*sid),
        ObsEvent::Halted { .. }
        | ObsEvent::Invoked { .. }
        | ObsEvent::Faulted { .. }
        | ObsEvent::OutputConditionChecked { .. } => None,
    }
}

/// Clone an event with a new tick value.
#[must_use]
pub fn with_tick(ev: &ObsEvent, tick: u64) -> ObsEvent {
    let mut out = ev.clone();
    match &mut out {
        ObsEvent::Sent {
            tick: event_tick, ..
        }
        | ObsEvent::Received {
            tick: event_tick, ..
        }
        | ObsEvent::Offered {
            tick: event_tick, ..
        }
        | ObsEvent::Chose {
            tick: event_tick, ..
        }
        | ObsEvent::Opened {
            tick: event_tick, ..
        }
        | ObsEvent::Closed {
            tick: event_tick, ..
        }
        | ObsEvent::EpochAdvanced {
            tick: event_tick, ..
        }
        | ObsEvent::Halted {
            tick: event_tick, ..
        }
        | ObsEvent::Invoked {
            tick: event_tick, ..
        }
        | ObsEvent::Acquired {
            tick: event_tick, ..
        }
        | ObsEvent::Released {
            tick: event_tick, ..
        }
        | ObsEvent::Transferred {
            tick: event_tick, ..
        }
        | ObsEvent::Forked {
            tick: event_tick, ..
        }
        | ObsEvent::Joined {
            tick: event_tick, ..
        }
        | ObsEvent::Aborted {
            tick: event_tick, ..
        }
        | ObsEvent::Tagged {
            tick: event_tick, ..
        }
        | ObsEvent::Checked {
            tick: event_tick, ..
        }
        | ObsEvent::Faulted {
            tick: event_tick, ..
        }
        | ObsEvent::OutputConditionChecked {
            tick: event_tick, ..
        } => *event_tick = tick,
    }
    out
}

/// Normalize a trace by assigning session-local ticks.
#[must_use]
pub fn normalize_trace(trace: &[ObsEvent]) -> Vec<ObsEvent> {
    let mut counters: BTreeMap<SessionId, u64> = BTreeMap::new();
    let mut out = Vec::with_capacity(trace.len());
    for ev in trace {
        if let Some(session) = obs_session(ev) {
            let counter = counters.entry(session).or_insert(0);
            let local_tick = *counter;
            *counter += 1;
            out.push(with_tick(ev, local_tick));
        } else {
            out.push(ev.clone());
        }
    }
    out
}

/// Clone a trace without normalization.
#[must_use]
pub fn strict_trace(trace: &[ObsEvent]) -> Vec<ObsEvent> {
    trace.to_vec()
}

/// Normalize a trace and wrap it in a versioned payload.
#[must_use]
pub fn normalize_trace_v1(trace: &[ObsEvent]) -> NormalizedTraceV1 {
    NormalizedTraceV1 {
        schema_version: TRACE_NORMALIZATION_SCHEMA_VERSION,
        events: normalize_trace(trace),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session::Edge;

    #[test]
    #[allow(clippy::as_conversions)]
    fn normalize_trace_memory_is_bounded_at_10k_events() {
        let mut trace = Vec::with_capacity(10_000);
        for i in 0..10_000usize {
            let sid = i % 32;
            let tick = i as u64;
            if i % 2 == 0 {
                trace.push(ObsEvent::Sent {
                    tick,
                    edge: Edge::new(sid, "A", "B"),
                    session: sid,
                    from: "A".to_string(),
                    to: "B".to_string(),
                    label: "m".to_string(),
                });
            } else {
                trace.push(ObsEvent::Received {
                    tick,
                    edge: Edge::new(sid, "B", "A"),
                    session: sid,
                    from: "B".to_string(),
                    to: "A".to_string(),
                    label: "m".to_string(),
                });
            }
        }

        let normalized = normalize_trace(&trace);
        assert_eq!(normalized.len(), trace.len());
        assert!(
            normalized.capacity() <= trace.len() + 1,
            "normalize_trace should allocate O(n) space without capacity blow-up"
        );
    }
}
