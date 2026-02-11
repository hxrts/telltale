//! VM trace normalization helpers for cross-VM comparison.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, HashMap};

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

/// Topology perturbation kinds recorded in effect traces.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum TopologyPerturbationKind {
    Crash,
    Partition,
    Heal,
}

/// Optional topology perturbation payload associated with an effect.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TopologyPerturbationEvent {
    pub kind: TopologyPerturbationKind,
    #[serde(default)]
    pub site: Option<String>,
    #[serde(default)]
    pub from: Option<String>,
    #[serde(default)]
    pub to: Option<String>,
}

/// Effect-trace record used for replay and determinism checks.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EffectTraceEvent {
    pub effect_id: u64,
    pub effect_kind: String,
    pub inputs: Value,
    pub outputs: Value,
    pub handler_identity: String,
    pub ordering_key: u64,
    #[serde(default)]
    pub topology: Option<TopologyPerturbationEvent>,
}

/// Output-condition verification record in replay traces.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct OutputConditionTraceEvent {
    pub predicate_ref: String,
    #[serde(default)]
    pub witness_ref: Option<String>,
    pub output_digest: String,
    pub passed: bool,
}

/// Replay bundle combining VM events with effect/output-condition traces.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ReplayTraceBundle {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    pub vm_trace: Vec<NormalizedEvent>,
    #[serde(default)]
    pub effect_trace: Vec<EffectTraceEvent>,
    #[serde(default)]
    pub output_condition_trace: Vec<OutputConditionTraceEvent>,
}

/// Try to extract a session identifier from an event payload.
///
/// Supports common shapes used by VM traces:
/// - `{ "session": <usize>, ... }`
/// - `{ "sid": <usize>, ... }`
/// - nested `{ "edge": { "sid": <usize> } }`
/// - nested `{ "endpoint": { "sid": <usize> } }`
#[must_use]
pub fn event_session<E>(event: &E) -> Option<usize>
where
    E: Serialize,
{
    let value = serde_json::to_value(event).ok()?;
    event_session_from_value(&value)
}

fn event_session_from_value(value: &Value) -> Option<usize> {
    match value {
        Value::Object(map) => {
            if let Some(sid) = map.get("session").and_then(Value::as_u64) {
                return usize::try_from(sid).ok();
            }
            if let Some(sid) = map.get("sid").and_then(Value::as_u64) {
                return usize::try_from(sid).ok();
            }
            if let Some(edge_sid) = map
                .get("edge")
                .and_then(Value::as_object)
                .and_then(|edge| edge.get("sid"))
                .and_then(Value::as_u64)
            {
                return usize::try_from(edge_sid).ok();
            }
            if let Some(endpoint_sid) = map
                .get("endpoint")
                .and_then(Value::as_object)
                .and_then(|endpoint| endpoint.get("sid"))
                .and_then(Value::as_u64)
            {
                return usize::try_from(endpoint_sid).ok();
            }

            for nested in map.values() {
                if let Some(sid) = event_session_from_value(nested) {
                    return Some(sid);
                }
            }
            None
        }
        Value::Array(items) => {
            for nested in items {
                if let Some(sid) = event_session_from_value(nested) {
                    return Some(sid);
                }
            }
            None
        }
        _ => None,
    }
}

/// Normalize tick values per session so traces can be compared independent of
/// cross-session scheduling interleavings.
#[must_use]
pub fn normalize_vm_trace<E>(
    trace: &[crate::vm_export::TickedObsEvent<E>],
) -> Vec<crate::vm_export::TickedObsEvent<E>>
where
    E: Serialize + Clone,
{
    let mut counters: HashMap<usize, u64> = HashMap::new();
    let mut out = Vec::with_capacity(trace.len());

    for ev in trace {
        if let Some(sid) = event_session(&ev.event) {
            let counter = counters.entry(sid).or_insert(0);
            out.push(crate::vm_export::TickedObsEvent {
                tick: *counter,
                event: ev.event.clone(),
            });
            *counter += 1;
        } else {
            out.push(ev.clone());
        }
    }

    out
}

/// Compare two traces after per-session normalization.
#[must_use]
pub fn traces_equivalent<E>(
    rust_trace: &[crate::vm_export::TickedObsEvent<E>],
    lean_trace: &[crate::vm_export::TickedObsEvent<E>],
) -> bool
where
    E: Serialize + Clone + PartialEq,
{
    normalize_vm_trace(rust_trace) == normalize_vm_trace(lean_trace)
}

/// Minimal shared observational equivalence relation for Lean/Rust VM traces.
///
/// Equivalence is defined as equality after per-session tick normalization.
#[must_use]
pub fn observationally_equivalent<E>(
    left: &[crate::vm_export::TickedObsEvent<E>],
    right: &[crate::vm_export::TickedObsEvent<E>],
) -> bool
where
    E: Serialize + Clone + PartialEq,
{
    traces_equivalent(left, right)
}

/// Extract per-session traces from a flat event list.
#[must_use]
pub fn partition_by_session(events: &[NormalizedEvent]) -> BTreeMap<usize, SessionTrace> {
    let mut map: BTreeMap<usize, SessionTrace> = BTreeMap::new();
    for ev in events {
        map.entry(ev.session_index).or_default().push(ev.clone());
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm_export::TickedObsEvent;
    use serde_json::json;

    #[test]
    fn event_session_extracts_common_shapes() {
        assert_eq!(
            event_session(&json!({"session": 3, "kind": "sent"})),
            Some(3)
        );
        assert_eq!(event_session(&json!({"sid": 4, "kind": "opened"})), Some(4));
        assert_eq!(
            event_session(&json!({"edge": {"sid": 5, "from": "A", "to": "B"}})),
            Some(5)
        );
        assert_eq!(
            event_session(&json!({"event": {"endpoint": {"sid": 6, "role": "A"}}})),
            Some(6)
        );
        assert_eq!(event_session(&json!({"kind": "halted"})), None);
    }

    #[test]
    fn normalize_vm_trace_rewrites_ticks_per_session() {
        let trace = vec![
            TickedObsEvent {
                tick: 10,
                event: json!({"session": 1, "kind": "sent"}),
            },
            TickedObsEvent {
                tick: 11,
                event: json!({"session": 2, "kind": "sent"}),
            },
            TickedObsEvent {
                tick: 12,
                event: json!({"session": 1, "kind": "received"}),
            },
        ];

        let normalized = normalize_vm_trace(&trace);
        assert_eq!(normalized[0].tick, 0);
        assert_eq!(normalized[1].tick, 0);
        assert_eq!(normalized[2].tick, 1);
    }

    #[test]
    fn traces_equivalent_compares_normalized_ticks() {
        let rust_trace = vec![
            TickedObsEvent {
                tick: 50,
                event: json!({"session": 1, "kind": "sent"}),
            },
            TickedObsEvent {
                tick: 99,
                event: json!({"session": 1, "kind": "received"}),
            },
        ];
        let lean_trace = vec![
            TickedObsEvent {
                tick: 1,
                event: json!({"session": 1, "kind": "sent"}),
            },
            TickedObsEvent {
                tick: 2,
                event: json!({"session": 1, "kind": "received"}),
            },
        ];
        assert!(traces_equivalent(&rust_trace, &lean_trace));
    }
}
