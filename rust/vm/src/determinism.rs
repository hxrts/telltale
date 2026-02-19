//! Determinism profile configuration for VM execution.

use std::collections::BTreeMap;

use crate::effect::EffectTraceEntry;
use crate::trace::{normalize_trace, obs_session};
use crate::vm::ObsEvent;
use serde::{Deserialize, Serialize};

/// Runtime effect-determinism tier used for admission and trace artifacts.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum EffectDeterminismTier {
    /// Strictly deterministic execution for fixed scheduler/effect inputs.
    #[default]
    StrictDeterministic,
    /// Deterministic under replayed effect outcomes.
    ReplayDeterministic,
    /// Nondeterminism is permitted only within a declared envelope bound.
    EnvelopeBoundedNondeterministic,
}

/// Determinism profile aligned with the VM architecture spec.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum DeterminismMode {
    /// Full determinism for fixed initial state/policy/effect trace.
    Full,
    /// Determinism modulo effect trace differences.
    ModuloEffects,
    /// Determinism modulo admissible commutative reorderings.
    ModuloCommutativity,
    /// Replay-deterministic profile under recorded effect outcomes.
    Replay,
}

/// Compare two executions according to a determinism profile.
#[must_use]
pub fn replay_consistent(
    mode: DeterminismMode,
    baseline_trace: &[ObsEvent],
    replay_trace: &[ObsEvent],
    baseline_effect_trace: &[EffectTraceEntry],
    replay_effect_trace: &[EffectTraceEntry],
) -> bool {
    match mode {
        DeterminismMode::Full => {
            baseline_trace == replay_trace && baseline_effect_trace == replay_effect_trace
        }
        DeterminismMode::ModuloEffects => {
            normalize_trace(baseline_trace) == normalize_trace(replay_trace)
        }
        DeterminismMode::ModuloCommutativity => {
            commutativity_normalize(baseline_trace) == commutativity_normalize(replay_trace)
        }
        DeterminismMode::Replay => baseline_trace == replay_trace,
    }
}

fn commutativity_normalize(trace: &[ObsEvent]) -> Vec<ObsEvent> {
    // Normalize per-session clocks first so session-local order is explicit.
    // Then canonicalize only eligible cross-session events, keeping non-session
    // events as deterministic barriers.
    let normalized = normalize_trace(trace);
    let mut out = Vec::with_capacity(normalized.len());
    let mut run = Vec::new();

    for event in normalized {
        if is_commutativity_eligible(&event) {
            run.push(event);
        } else {
            flush_commutative_run(&mut out, &mut run);
            out.push(event);
        }
    }
    flush_commutative_run(&mut out, &mut run);
    out
}

fn is_commutativity_eligible(event: &ObsEvent) -> bool {
    obs_session(event).is_some()
}

fn flush_commutative_run(out: &mut Vec<ObsEvent>, run: &mut Vec<ObsEvent>) {
    if run.is_empty() {
        return;
    }
    let mut buckets: BTreeMap<usize, Vec<ObsEvent>> = BTreeMap::new();
    for event in run.drain(..) {
        let sid = obs_session(&event).expect("eligible events are session scoped");
        buckets.entry(sid).or_default().push(event);
    }
    let mut cursors: BTreeMap<usize, usize> = buckets.keys().map(|sid| (*sid, 0)).collect();

    // BOUND: processes total_events across all buckets, exits when all cursors exhausted
    loop {
        let mut progressed = false;
        for (sid, events) in &buckets {
            let cursor = cursors.get_mut(sid).expect("cursor exists");
            if *cursor < events.len() {
                out.push(events[*cursor].clone());
                *cursor += 1;
                progressed = true;
            }
        }
        if !progressed {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session::Edge;
    use serde_json::json;

    fn entry(id: u64, kind: &str) -> EffectTraceEntry {
        EffectTraceEntry {
            effect_id: id,
            effect_kind: kind.to_string(),
            inputs: json!({}),
            outputs: json!({}),
            handler_identity: "h".to_string(),
            ordering_key: id,
            topology: None,
        }
    }

    #[test]
    fn full_mode_requires_exact_match() {
        let trace = vec![ObsEvent::Halted {
            tick: 1,
            coro_id: 0,
        }];
        let effects = vec![entry(0, "send_decision")];
        assert!(replay_consistent(
            DeterminismMode::Full,
            &trace,
            &trace,
            &effects,
            &effects
        ));
        assert!(!replay_consistent(
            DeterminismMode::Full,
            &trace,
            &trace,
            &effects,
            &[]
        ));
    }

    #[test]
    fn modulo_effects_ignores_effect_trace_differences() {
        let left = vec![ObsEvent::Sent {
            tick: 10,
            edge: Edge::new(1, "A", "B"),
            session: 1,
            from: "A".to_string(),
            to: "B".to_string(),
            label: "m".to_string(),
        }];
        let right = vec![ObsEvent::Sent {
            tick: 99,
            edge: Edge::new(1, "A", "B"),
            session: 1,
            from: "A".to_string(),
            to: "B".to_string(),
            label: "m".to_string(),
        }];
        assert!(replay_consistent(
            DeterminismMode::ModuloEffects,
            &left,
            &right,
            &[entry(0, "send_decision")],
            &[entry(9, "send_decision")]
        ));
    }

    #[test]
    fn modulo_commutativity_ignores_cross_session_reorderings() {
        let event_a = ObsEvent::Sent {
            tick: 1,
            edge: Edge::new(1, "A", "B"),
            session: 1,
            from: "A".to_string(),
            to: "B".to_string(),
            label: "x".to_string(),
        };
        let event_b = ObsEvent::Sent {
            tick: 1,
            edge: Edge::new(2, "C", "D"),
            session: 2,
            from: "C".to_string(),
            to: "D".to_string(),
            label: "y".to_string(),
        };
        let left = vec![event_a.clone(), event_b.clone()];
        let right = vec![event_b, event_a];
        assert!(replay_consistent(
            DeterminismMode::ModuloCommutativity,
            &left,
            &right,
            &[],
            &[]
        ));
    }

    #[test]
    fn modulo_commutativity_preserves_in_session_order() {
        let a1 = ObsEvent::Sent {
            tick: 1,
            edge: Edge::new(1, "A", "B"),
            session: 1,
            from: "A".to_string(),
            to: "B".to_string(),
            label: "a1".to_string(),
        };
        let a2 = ObsEvent::Received {
            tick: 2,
            edge: Edge::new(1, "B", "A"),
            session: 1,
            from: "B".to_string(),
            to: "A".to_string(),
            label: "a2".to_string(),
        };
        let b1 = ObsEvent::Sent {
            tick: 1,
            edge: Edge::new(2, "C", "D"),
            session: 2,
            from: "C".to_string(),
            to: "D".to_string(),
            label: "b1".to_string(),
        };

        let baseline = vec![a1.clone(), b1, a2.clone()];
        let invalid = vec![a2, a1];
        assert!(!replay_consistent(
            DeterminismMode::ModuloCommutativity,
            &baseline,
            &invalid,
            &[],
            &[]
        ));
    }

    #[test]
    fn modulo_commutativity_keeps_non_session_barriers_fixed() {
        let sent = ObsEvent::Sent {
            tick: 1,
            edge: Edge::new(1, "A", "B"),
            session: 1,
            from: "A".to_string(),
            to: "B".to_string(),
            label: "x".to_string(),
        };
        let barrier = ObsEvent::Halted {
            tick: 2,
            coro_id: 99,
        };
        let recv = ObsEvent::Received {
            tick: 3,
            edge: Edge::new(2, "C", "D"),
            session: 2,
            from: "C".to_string(),
            to: "D".to_string(),
            label: "y".to_string(),
        };

        let baseline = vec![sent.clone(), barrier.clone(), recv.clone()];
        let reordered = vec![recv, barrier, sent];
        assert!(!replay_consistent(
            DeterminismMode::ModuloCommutativity,
            &baseline,
            &reordered,
            &[],
            &[]
        ));
    }

    #[test]
    fn replay_mode_requires_exact_observation_trace() {
        let left = vec![ObsEvent::Halted {
            tick: 1,
            coro_id: 0,
        }];
        let right = vec![ObsEvent::Halted {
            tick: 2,
            coro_id: 0,
        }];
        assert!(replay_consistent(
            DeterminismMode::Replay,
            &left,
            &left,
            &[],
            &[]
        ));
        assert!(!replay_consistent(
            DeterminismMode::Replay,
            &left,
            &right,
            &[],
            &[]
        ));
    }
}
