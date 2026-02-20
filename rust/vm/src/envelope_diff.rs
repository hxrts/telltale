//! Envelope differential artifacts for cross-engine conformance.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::determinism::EffectDeterminismTier;
use crate::serialization::CanonicalReplayFragmentV1;
use crate::trace::normalize_trace;
use crate::trace::obs_session;
use crate::verification::{DefaultVerificationModel, HashTag, VerificationModel};
use crate::vm::ObsEvent;

/// Canonical schema version identifier for envelope differential artifacts.
pub const ENVELOPE_DIFF_SCHEMA_VERSION: &str = "vm.envelope_diff.v1";

fn default_schema_version() -> String {
    ENVELOPE_DIFF_SCHEMA_VERSION.to_string()
}

fn normalize_envelope_schema_version(raw: &str) -> String {
    if raw == "1" {
        ENVELOPE_DIFF_SCHEMA_VERSION.to_string()
    } else {
        raw.to_string()
    }
}

fn deserialize_envelope_schema_version<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: serde::Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum SchemaVersionValue {
        String(String),
        Integer(u64),
    }

    let parsed = SchemaVersionValue::deserialize(deserializer)?;
    Ok(match parsed {
        SchemaVersionValue::String(version) => normalize_envelope_schema_version(&version),
        SchemaVersionValue::Integer(version) => {
            normalize_envelope_schema_version(&version.to_string())
        }
    })
}

/// Scheduler-level differential class between two runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SchedulerPermutationClass {
    /// Global event order is identical.
    Exact,
    /// Global order differs but per-session order is preserved.
    SessionNormalizedPermutation,
    /// Differences exceed session-normalized permutation.
    EnvelopeBounded,
}

/// Effect-ordering differential class between two runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EffectOrderingClass {
    /// Effect traces match exactly.
    Exact,
    /// Replay-fragment behavior matches despite effect ordering differences.
    ReplayDeterministic,
    /// Differences are accepted only under an explicit envelope bound.
    EnvelopeBounded,
}

/// Failure-visible differential class between two runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FailureVisibleDiffClass {
    /// Failure-visible snapshots match exactly.
    Exact,
    /// Failure-visible differences are accepted only under an explicit envelope.
    EnvelopeBounded,
}

/// Wave-width bounds recorded for one envelope differential.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveWidthBound {
    /// Observed max wave width in the baseline run.
    pub baseline_max_wave_width: usize,
    /// Observed max wave width in the candidate run.
    pub candidate_max_wave_width: usize,
    /// Declared admissible upper bound for candidate wave width.
    pub declared_upper_bound: usize,
}

impl WaveWidthBound {
    /// Return true when the observed candidate width stays within the declared bound.
    #[must_use]
    pub fn within_declared_bound(&self) -> bool {
        self.candidate_max_wave_width <= self.declared_upper_bound
    }
}

/// Runtime differential envelope emitted by multi-engine runs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnvelopeDiff {
    /// Schema version for this artifact payload.
    #[serde(
        default = "default_schema_version",
        deserialize_with = "deserialize_envelope_schema_version"
    )]
    pub schema_version: String,
    /// Baseline engine identifier.
    pub baseline_engine: String,
    /// Candidate engine identifier.
    pub candidate_engine: String,
    /// Scheduler-permutation differential class.
    pub scheduler_permutation_class: SchedulerPermutationClass,
    /// Wave-width differential dimension.
    pub wave_width_bound: WaveWidthBound,
    /// Effect-ordering differential class.
    pub effect_ordering_class: EffectOrderingClass,
    /// Failure-visible differential class.
    pub failure_visible_diff_class: FailureVisibleDiffClass,
    /// Declared effect determinism tier for the compared runs.
    pub effect_determinism_tier: EffectDeterminismTier,
}

impl EnvelopeDiff {
    /// Construct an `EnvelopeDiff` from canonical replay fragments.
    #[must_use]
    pub fn from_replay_fragments(
        baseline_engine: impl Into<String>,
        candidate_engine: impl Into<String>,
        baseline: &CanonicalReplayFragmentV1,
        candidate: &CanonicalReplayFragmentV1,
        baseline_max_wave_width: usize,
        candidate_max_wave_width: usize,
        declared_upper_bound: usize,
        effect_determinism_tier: EffectDeterminismTier,
    ) -> Self {
        let scheduler_permutation_class =
            classify_scheduler_permutation(&baseline.obs_trace, &candidate.obs_trace);
        let effect_ordering_class =
            classify_effect_ordering(baseline, candidate, scheduler_permutation_class);
        let failure_visible_diff_class = classify_failure_visible(baseline, candidate);

        Self {
            schema_version: default_schema_version(),
            baseline_engine: baseline_engine.into(),
            candidate_engine: candidate_engine.into(),
            scheduler_permutation_class,
            wave_width_bound: WaveWidthBound {
                baseline_max_wave_width,
                candidate_max_wave_width,
                declared_upper_bound,
            },
            effect_ordering_class,
            failure_visible_diff_class,
            effect_determinism_tier,
        }
    }

    /// Stable canonical JSON serialization.
    ///
    /// # Errors
    ///
    /// Returns an error if JSON serialization fails.
    pub fn canonical_json(&self) -> Result<Vec<u8>, serde_json::Error> {
        serde_json::to_vec(self)
    }

    /// Stable hash digest for this envelope differential artifact.
    #[must_use]
    pub fn stable_hash_hex(&self) -> String {
        stable_hash_hex_from_serializable(self)
    }
}

/// Emitted envelope artifact carrying the diff and stable hashes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnvelopeDiffArtifactV1 {
    /// Schema version for this artifact payload.
    #[serde(
        default = "default_schema_version",
        deserialize_with = "deserialize_envelope_schema_version"
    )]
    pub schema_version: String,
    /// Envelope differential payload.
    pub envelope_diff: EnvelopeDiff,
    /// Stable hash of the baseline canonical replay fragment.
    pub baseline_fragment_hash: String,
    /// Stable hash of the candidate canonical replay fragment.
    pub candidate_fragment_hash: String,
    /// Stable hash of the envelope differential payload.
    pub envelope_diff_hash: String,
}

impl EnvelopeDiffArtifactV1 {
    /// Build an artifact from replay fragments and computed envelope dimensions.
    #[must_use]
    pub fn from_replay_fragments(
        baseline_engine: impl Into<String>,
        candidate_engine: impl Into<String>,
        baseline: &CanonicalReplayFragmentV1,
        candidate: &CanonicalReplayFragmentV1,
        baseline_max_wave_width: usize,
        candidate_max_wave_width: usize,
        declared_upper_bound: usize,
        effect_determinism_tier: EffectDeterminismTier,
    ) -> Self {
        let envelope_diff = EnvelopeDiff::from_replay_fragments(
            baseline_engine,
            candidate_engine,
            baseline,
            candidate,
            baseline_max_wave_width,
            candidate_max_wave_width,
            declared_upper_bound,
            effect_determinism_tier,
        );
        let baseline_fragment_hash = stable_hash_hex_from_serializable(baseline);
        let candidate_fragment_hash = stable_hash_hex_from_serializable(candidate);
        let envelope_diff_hash = envelope_diff.stable_hash_hex();
        Self {
            schema_version: default_schema_version(),
            envelope_diff,
            baseline_fragment_hash,
            candidate_fragment_hash,
            envelope_diff_hash,
        }
    }
}

fn classify_scheduler_permutation(
    baseline_trace: &[ObsEvent],
    candidate_trace: &[ObsEvent],
) -> SchedulerPermutationClass {
    if baseline_trace == candidate_trace {
        return SchedulerPermutationClass::Exact;
    }
    let baseline_normalized = normalize_trace(baseline_trace);
    let candidate_normalized = normalize_trace(candidate_trace);
    if per_session_projection(&baseline_normalized) == per_session_projection(&candidate_normalized)
    {
        return SchedulerPermutationClass::SessionNormalizedPermutation;
    }
    SchedulerPermutationClass::EnvelopeBounded
}

fn per_session_projection(trace: &[ObsEvent]) -> BTreeMap<usize, Vec<ObsEvent>> {
    let mut out: BTreeMap<usize, Vec<ObsEvent>> = BTreeMap::new();
    for event in trace {
        if let Some(sid) = obs_session(event) {
            out.entry(sid).or_default().push(event.clone());
        }
    }
    out
}

fn classify_effect_ordering(
    baseline: &CanonicalReplayFragmentV1,
    candidate: &CanonicalReplayFragmentV1,
    scheduler_permutation_class: SchedulerPermutationClass,
) -> EffectOrderingClass {
    if baseline.effect_trace == candidate.effect_trace {
        return EffectOrderingClass::Exact;
    }
    match scheduler_permutation_class {
        SchedulerPermutationClass::Exact
        | SchedulerPermutationClass::SessionNormalizedPermutation => {
            EffectOrderingClass::ReplayDeterministic
        }
        SchedulerPermutationClass::EnvelopeBounded => EffectOrderingClass::EnvelopeBounded,
    }
}

fn classify_failure_visible(
    baseline: &CanonicalReplayFragmentV1,
    candidate: &CanonicalReplayFragmentV1,
) -> FailureVisibleDiffClass {
    if baseline.crashed_sites == candidate.crashed_sites
        && baseline.partitioned_edges == candidate.partitioned_edges
        && baseline.corrupted_edges == candidate.corrupted_edges
        && baseline.timed_out_sites == candidate.timed_out_sites
    {
        FailureVisibleDiffClass::Exact
    } else {
        FailureVisibleDiffClass::EnvelopeBounded
    }
}

fn stable_hash_hex_from_serializable<T: Serialize>(value: &T) -> String {
    let bytes = serde_json::to_vec(value).unwrap_or_else(|_| b"{}".to_vec());
    let digest = DefaultVerificationModel::hash(HashTag::Value, &bytes);
    bytes_to_hex(&digest.0)
}

#[allow(clippy::as_conversions)]
fn bytes_to_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        // Nibble values are always in 0..16, so usize indexing is safe.
        out.push(HEX[(byte >> 4) as usize] as char);
        // Same invariant for the low nibble.
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session::Edge;

    fn sent(session: usize, tick: u64) -> ObsEvent {
        ObsEvent::Sent {
            tick,
            edge: Edge::new(session, "A", "B"),
            session,
            from: "A".to_string(),
            to: "B".to_string(),
            label: "m".to_string(),
        }
    }

    fn fragment(trace: Vec<ObsEvent>) -> CanonicalReplayFragmentV1 {
        CanonicalReplayFragmentV1 {
            schema_version: crate::serialization::SERIALIZATION_SCHEMA_VERSION.to_string(),
            obs_trace: trace,
            effect_trace: Vec::new(),
            crashed_sites: Vec::new(),
            partitioned_edges: Vec::new(),
            corrupted_edges: Vec::new(),
            timed_out_sites: Vec::new(),
            effect_determinism_tier: EffectDeterminismTier::StrictDeterministic,
        }
    }

    #[test]
    fn scheduler_class_detects_session_permutation() {
        let baseline = fragment(vec![sent(1, 1), sent(2, 2)]);
        let candidate = fragment(vec![sent(2, 3), sent(1, 4)]);
        let diff = EnvelopeDiff::from_replay_fragments(
            "canonical",
            "threaded",
            &baseline,
            &candidate,
            1,
            2,
            2,
            EffectDeterminismTier::EnvelopeBoundedNondeterministic,
        );
        assert_eq!(
            diff.scheduler_permutation_class,
            SchedulerPermutationClass::SessionNormalizedPermutation
        );
    }

    #[test]
    fn envelope_hash_is_stable_for_equal_payloads() {
        let baseline = fragment(vec![sent(1, 1)]);
        let candidate = fragment(vec![sent(1, 1)]);
        let left = EnvelopeDiff::from_replay_fragments(
            "a",
            "b",
            &baseline,
            &candidate,
            1,
            1,
            1,
            EffectDeterminismTier::StrictDeterministic,
        );
        let right = EnvelopeDiff::from_replay_fragments(
            "a",
            "b",
            &baseline,
            &candidate,
            1,
            1,
            1,
            EffectDeterminismTier::StrictDeterministic,
        );
        assert_eq!(left.stable_hash_hex(), right.stable_hash_hex());
    }

    #[test]
    fn artifact_hash_tracks_envelope_payload() {
        let baseline = fragment(vec![sent(1, 1)]);
        let candidate = fragment(vec![sent(1, 1)]);
        let artifact = EnvelopeDiffArtifactV1::from_replay_fragments(
            "canonical",
            "threaded",
            &baseline,
            &candidate,
            1,
            1,
            1,
            EffectDeterminismTier::StrictDeterministic,
        );
        assert!(!artifact.envelope_diff_hash.is_empty());
        assert_eq!(
            artifact.envelope_diff_hash,
            artifact.envelope_diff.stable_hash_hex()
        );
    }

    #[test]
    fn legacy_numeric_schema_version_deserializes_to_string_identifier() {
        let payload = serde_json::json!({
            "schema_version": 1,
            "baseline_engine": "lean",
            "candidate_engine": "threaded",
            "scheduler_permutation_class": "Exact",
            "wave_width_bound": {
                "baseline_max_wave_width": 1,
                "candidate_max_wave_width": 1,
                "declared_upper_bound": 1
            },
            "effect_ordering_class": "Exact",
            "failure_visible_diff_class": "Exact",
            "effect_determinism_tier": "strict_deterministic"
        });
        let decoded: EnvelopeDiff =
            serde_json::from_value(payload).expect("legacy schema version should deserialize");
        assert_eq!(decoded.schema_version, ENVELOPE_DIFF_SCHEMA_VERSION);
    }
}
