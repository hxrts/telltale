//! Output-condition commit gating primitives.
//!
//! This module centralizes policy, metadata, and verification records for
//! output-conditioned execution.

use serde::{Deserialize, Serialize};

/// Output-condition policy for deterministic commit gating.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OutputConditionPolicy {
    /// Skip output-condition gating entirely.
    Disabled,
    /// Accept all output-condition checks.
    AllowAll,
    /// Reject all output-condition checks.
    DenyAll,
    /// Accept only listed predicate references.
    PredicateAllowList(Vec<String>),
}

/// Output-condition metadata checked by the VM kernel before committing outputs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OutputConditionMeta {
    /// Stable predicate id/hash.
    pub predicate_ref: String,
    /// Optional opaque witness reference.
    pub witness_ref: Option<String>,
    /// Opaque digest over pending output payload.
    pub output_digest: String,
}

/// Recorded result of one output-condition verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OutputConditionCheck {
    /// Metadata that was checked.
    pub meta: OutputConditionMeta,
    /// Deterministic verifier outcome.
    pub passed: bool,
}

/// Optional output-condition metadata emitted by the host for the current step.
#[derive(Debug, Clone)]
pub struct OutputConditionHint {
    /// Stable predicate identifier (name/hash) for gating output commit.
    pub predicate_ref: String,
    /// Optional opaque witness reference.
    pub witness_ref: Option<String>,
}

impl OutputConditionMeta {
    /// Build metadata from a host hint and a deterministic output digest.
    #[must_use]
    pub fn from_hint(hint: OutputConditionHint, output_digest: String) -> Self {
        Self {
            predicate_ref: hint.predicate_ref,
            witness_ref: hint.witness_ref,
            output_digest,
        }
    }

    /// Default metadata when the host does not provide a hint.
    #[must_use]
    pub fn default_observable(output_digest: String) -> Self {
        Self {
            predicate_ref: "vm.observable_output".to_string(),
            witness_ref: None,
            output_digest,
        }
    }
}

/// Deterministic output-condition verifier.
#[must_use]
pub fn verify_output_condition(policy: &OutputConditionPolicy, meta: &OutputConditionMeta) -> bool {
    match policy {
        OutputConditionPolicy::Disabled | OutputConditionPolicy::AllowAll => true,
        OutputConditionPolicy::DenyAll => false,
        OutputConditionPolicy::PredicateAllowList(allowed) => {
            allowed.iter().any(|p| p == &meta.predicate_ref)
        }
    }
}
