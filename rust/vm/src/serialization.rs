//! Canonical serialization helpers for deterministic replay/testing artifacts.

use crate::determinism::EffectDeterminismTier;
use crate::effect::{CorruptionType, EffectTraceEntry};
use crate::trace::normalize_trace;
use crate::vm::ObsEvent;
use serde::{Deserialize, Serialize};

fn default_serialization_schema_version() -> u32 {
    1
}

/// Versioned canonical trace payload used for cross-target normalization.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CanonicalTraceV1 {
    /// Schema version for canonical trace serialization.
    #[serde(default = "default_serialization_schema_version")]
    pub schema_version: u32,
    /// Canonically normalized observable events.
    pub events: Vec<ObsEvent>,
}

/// Versioned canonical replay-state fragment used by tests and replay checks.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CanonicalReplayFragmentV1 {
    /// Schema version for canonical replay serialization.
    #[serde(default = "default_serialization_schema_version")]
    pub schema_version: u32,
    /// Canonically normalized observable trace.
    pub obs_trace: Vec<ObsEvent>,
    /// Canonically sorted effect trace.
    pub effect_trace: Vec<EffectTraceEntry>,
    /// Sorted crashed sites.
    pub crashed_sites: Vec<String>,
    /// Sorted directed partition edges.
    pub partitioned_edges: Vec<(String, String)>,
    /// Sorted directed corruption edges with policies.
    pub corrupted_edges: Vec<((String, String), CorruptionType)>,
    /// Sorted timeout horizons keyed by site.
    pub timed_out_sites: Vec<(String, u64)>,
    /// Declared effect determinism tier for this run.
    #[serde(default)]
    pub effect_determinism_tier: EffectDeterminismTier,
}

/// Normalize an observable trace into the canonical versioned format.
#[must_use]
pub fn canonical_trace_v1(trace: &[ObsEvent]) -> CanonicalTraceV1 {
    CanonicalTraceV1 {
        schema_version: default_serialization_schema_version(),
        events: normalize_trace(trace),
    }
}

/// Canonicalize effect-trace ordering for deterministic replay diffs.
#[must_use]
pub fn canonical_effect_trace(trace: &[EffectTraceEntry]) -> Vec<EffectTraceEntry> {
    let mut out = trace.to_vec();
    out.sort_by(|lhs, rhs| {
        (lhs.ordering_key, lhs.effect_id, &lhs.effect_kind).cmp(&(
            rhs.ordering_key,
            rhs.effect_id,
            &rhs.effect_kind,
        ))
    });
    out
}

/// Build a canonical replay-state fragment from runtime snapshots.
#[must_use]
pub fn canonical_replay_fragment_v1(
    obs_trace: &[ObsEvent],
    effect_trace: &[EffectTraceEntry],
    mut crashed_sites: Vec<String>,
    mut partitioned_edges: Vec<(String, String)>,
    mut corrupted_edges: Vec<((String, String), CorruptionType)>,
    mut timed_out_sites: Vec<(String, u64)>,
    effect_determinism_tier: EffectDeterminismTier,
) -> CanonicalReplayFragmentV1 {
    crashed_sites.sort_unstable();
    crashed_sites.dedup();

    partitioned_edges.sort_unstable();
    partitioned_edges.dedup();

    corrupted_edges.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0));
    corrupted_edges.dedup();

    timed_out_sites.sort_unstable();

    CanonicalReplayFragmentV1 {
        schema_version: default_serialization_schema_version(),
        obs_trace: canonical_trace_v1(obs_trace).events,
        effect_trace: canonical_effect_trace(effect_trace),
        crashed_sites,
        partitioned_edges,
        corrupted_edges,
        timed_out_sites,
        effect_determinism_tier,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session::Edge;

    #[test]
    fn canonical_effect_trace_is_stably_sorted() {
        let trace = vec![
            EffectTraceEntry {
                effect_id: 2,
                effect_kind: "b".to_string(),
                inputs: serde_json::json!({}),
                outputs: serde_json::json!({}),
                handler_identity: "h".to_string(),
                ordering_key: 3,
                topology: None,
            },
            EffectTraceEntry {
                effect_id: 1,
                effect_kind: "a".to_string(),
                inputs: serde_json::json!({}),
                outputs: serde_json::json!({}),
                handler_identity: "h".to_string(),
                ordering_key: 2,
                topology: None,
            },
        ];

        let sorted = canonical_effect_trace(&trace);
        assert_eq!(sorted[0].effect_id, 1);
        assert_eq!(sorted[1].effect_id, 2);
    }

    #[test]
    fn canonical_trace_payload_has_version() {
        let trace = vec![ObsEvent::Sent {
            tick: 1,
            edge: Edge::new(1, "A", "B"),
            session: 1,
            from: "A".to_string(),
            to: "B".to_string(),
            label: "m".to_string(),
        }];
        let payload = canonical_trace_v1(&trace);
        assert_eq!(payload.schema_version, 1);
        assert_eq!(payload.events.len(), 1);
    }
}
