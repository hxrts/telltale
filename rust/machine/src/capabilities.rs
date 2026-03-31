//! Canonical protocol-critical capability taxonomy and boundary ledger.
//!
//! This module is the source-of-truth boundary for Telltale's capability model.
//! It classifies the protocol-critical capability surfaces that already exist
//! across runtime admission, session ownership, semantic evidence/finalization,
//! and explicit transition artifacts.

use serde::{Deserialize, Serialize};

/// Canonical capability class for one protocol-critical surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProtocolCriticalCapabilityClass {
    /// Admission/profile/runtime-mode capability.
    Admission,
    /// Live session or fragment authority.
    Ownership,
    /// Evidence-bearing or finalization-bearing justification object.
    Evidence,
    /// Explicit handoff, cutover, or reconfiguration transition object.
    Transition,
}

/// Lifecycle state shared by first-class capability and evidence objects.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProtocolCriticalCapabilityLifecycleState {
    /// Object was issued and is available for a later semantic step.
    Issued,
    /// Object was consumed exactly once on its sanctioned path.
    Consumed,
    /// Object was rejected as invalid, insufficient, or unauthorized.
    Rejected,
    /// Object became unusable because later semantic state revoked it.
    Invalidated,
    /// Transition object committed and became canonical.
    Committed,
    /// Transition object rolled back and did not become canonical.
    RolledBack,
    /// Object aged out of its validity window.
    Expired,
}

/// Canonical first-class artifact carried by the capability/evidence lifecycle audit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProtocolCriticalCapabilityArtifact {
    /// Live ownership capability for one session or fragment.
    OwnershipCapability(crate::session::OwnershipCapability),
    /// Explicit ownership-transfer receipt.
    OwnershipReceipt(crate::session::OwnershipReceipt),
    /// Readiness witness for one protocol-critical check.
    ReadinessWitness(crate::session::ReadinessWitness),
    /// Cancellation witness for one terminated ownership path.
    CancellationWitness(crate::session::CancellationWitness),
    /// Timeout witness for one topology timeout.
    TimeoutWitness(crate::session::TimeoutWitness),
    /// Explicit delegation/handoff receipt.
    DelegationReceipt(crate::transfer_semantics::DelegationReceipt),
}

impl ProtocolCriticalCapabilityArtifact {
    /// Canonical capability class for this artifact.
    #[must_use]
    pub fn class(&self) -> ProtocolCriticalCapabilityClass {
        match self {
            Self::OwnershipCapability(_) => ProtocolCriticalCapabilityClass::Ownership,
            Self::OwnershipReceipt(_) | Self::DelegationReceipt(_) => {
                ProtocolCriticalCapabilityClass::Transition
            }
            Self::ReadinessWitness(_) | Self::CancellationWitness(_) | Self::TimeoutWitness(_) => {
                ProtocolCriticalCapabilityClass::Evidence
            }
        }
    }
}

/// Stable lifecycle audit record for first-class capability/evidence objects.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProtocolCriticalCapabilityLifecycleRecord {
    /// Runtime tick associated with the lifecycle event, when available.
    pub tick: Option<u64>,
    /// Artifact whose lifecycle changed.
    pub artifact: ProtocolCriticalCapabilityArtifact,
    /// Lifecycle state reached by the artifact.
    pub lifecycle: ProtocolCriticalCapabilityLifecycleState,
    /// Optional rejection/rollback/invalidity reason.
    pub reason: Option<String>,
}

fn from_authority_audit_record(
    record: &crate::session::AuthorityAuditRecord,
) -> ProtocolCriticalCapabilityLifecycleRecord {
    use crate::session::AuthorityArtifact;
    let artifact = match &record.artifact {
        AuthorityArtifact::OwnershipCapability(capability) => {
            ProtocolCriticalCapabilityArtifact::OwnershipCapability(capability.clone())
        }
        AuthorityArtifact::OwnershipReceipt(receipt) => {
            ProtocolCriticalCapabilityArtifact::OwnershipReceipt(receipt.clone())
        }
        AuthorityArtifact::Readiness(witness) => {
            ProtocolCriticalCapabilityArtifact::ReadinessWitness(witness.clone())
        }
        AuthorityArtifact::Cancellation(witness) => {
            ProtocolCriticalCapabilityArtifact::CancellationWitness(witness.clone())
        }
        AuthorityArtifact::Timeout(witness) => {
            ProtocolCriticalCapabilityArtifact::TimeoutWitness(witness.clone())
        }
    };

    ProtocolCriticalCapabilityLifecycleRecord {
        tick: record.tick,
        artifact,
        lifecycle: record.event.into(),
        reason: record.reason.clone(),
    }
}

fn from_delegation_audit_record(
    record: &crate::transfer_semantics::DelegationAuditRecord,
) -> ProtocolCriticalCapabilityLifecycleRecord {
    let lifecycle = match record.status {
        crate::transfer_semantics::DelegationStatus::Committed => {
            ProtocolCriticalCapabilityLifecycleState::Committed
        }
        crate::transfer_semantics::DelegationStatus::RolledBack => {
            ProtocolCriticalCapabilityLifecycleState::RolledBack
        }
    };
    ProtocolCriticalCapabilityLifecycleRecord {
        tick: Some(record.tick),
        artifact: ProtocolCriticalCapabilityArtifact::DelegationReceipt(record.receipt.clone()),
        lifecycle,
        reason: record.reason.clone(),
    }
}

/// Canonical lifecycle audit log for protocol-critical capabilities/evidence.
#[must_use]
pub fn capability_lifecycle_audit_log_v1(
    authority_audit_log: &[crate::session::AuthorityAuditRecord],
    delegation_audit_log: &[crate::transfer_semantics::DelegationAuditRecord],
) -> Vec<ProtocolCriticalCapabilityLifecycleRecord> {
    let mut records: Vec<_> = authority_audit_log
        .iter()
        .map(from_authority_audit_record)
        .chain(
            delegation_audit_log
                .iter()
                .map(from_delegation_audit_record),
        )
        .collect();
    // Preserve the real intra-tick linearization from the underlying runtime
    // logs instead of reconstructing a synthetic lifecycle order.
    records.sort_by_key(|record| record.tick.unwrap_or(0));
    records
}

/// One source-derived row in the protocol-critical capability boundary ledger.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProtocolCriticalCapabilityBoundaryEntry {
    /// Stable surface name used in docs and tests.
    pub surface: String,
    /// Canonical capability class for this surface.
    pub class: ProtocolCriticalCapabilityClass,
    /// Stable lifecycle states relevant to this surface.
    pub lifecycle: Vec<ProtocolCriticalCapabilityLifecycleState>,
    /// Rust module that owns the first-class surface today.
    pub rust_module: String,
    /// Lean module/theorem boundary that models or proves the surface today.
    pub lean_module: String,
    /// Short reason this surface is protocol-critical.
    pub rationale: String,
}

fn entry(
    surface: &str,
    class: ProtocolCriticalCapabilityClass,
    lifecycle: &[ProtocolCriticalCapabilityLifecycleState],
    rust_module: &str,
    lean_module: &str,
    rationale: &str,
) -> ProtocolCriticalCapabilityBoundaryEntry {
    ProtocolCriticalCapabilityBoundaryEntry {
        surface: surface.to_string(),
        class,
        lifecycle: lifecycle.to_vec(),
        rust_module: rust_module.to_string(),
        lean_module: lean_module.to_string(),
        rationale: rationale.to_string(),
    }
}

/// Source-derived protocol-critical capability boundary ledger.
#[must_use]
pub fn protocol_critical_capability_boundary() -> Vec<ProtocolCriticalCapabilityBoundaryEntry> {
    use ProtocolCriticalCapabilityClass::{
        Admission as AdmissionClass, Evidence as EvidenceClass, Ownership as OwnershipClass,
        Transition as TransitionClass,
    };
    use ProtocolCriticalCapabilityLifecycleState::{
        Committed, Consumed, Expired, Invalidated, Issued, Rejected, RolledBack,
    };

    vec![
        entry(
            "runtime_admission",
            AdmissionClass,
            &[Issued, Rejected],
            "rust/machine/src/runtime_contracts.rs",
            "lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean",
            "Admits or rejects runtime/profile execution before protocol-critical execution begins.",
        ),
        entry(
            "theorem_pack_capabilities",
            AdmissionClass,
            &[Issued, Rejected],
            "rust/machine/src/composition.rs",
            "lean/Runtime/Proofs/TheoremPack/API.lean",
            "Carries proof-backed eligibility that higher-level runtime admission consumes.",
        ),
        entry(
            "ownership_capability",
            OwnershipClass,
            &[Issued, Invalidated, Expired, Rejected],
            "rust/machine/src/session/overview.rs",
            "lean/Runtime/Proofs/Conservation/Authority.lean",
            "Proves which actor may currently mutate session-local protocol-critical state.",
        ),
        entry(
            "readiness_witness",
            EvidenceClass,
            &[Issued, Consumed, Rejected, Invalidated, Expired],
            "rust/machine/src/session/overview.rs",
            "lean/Runtime/Proofs/AuthorityMetatheory.lean",
            "Justifies a protocol-critical readiness decision under one live owner generation.",
        ),
        entry(
            "authoritative_read",
            EvidenceClass,
            &[Issued, Consumed, Rejected],
            "rust/machine/src/semantic_objects.rs",
            "lean/Runtime/Proofs/Conservation/Evidence.lean",
            "Carries evidence-bearing protocol input that may author canonical truth.",
        ),
        entry(
            "materialization_proof",
            EvidenceClass,
            &[Issued, Consumed, Rejected],
            "rust/machine/src/semantic_objects.rs",
            "lean/Runtime/Proofs/Conservation/Evidence.lean",
            "Witnesses proof-bearing success on the sanctioned materialization path.",
        ),
        entry(
            "canonical_handle",
            EvidenceClass,
            &[Issued, Consumed, Rejected, Invalidated],
            "rust/machine/src/semantic_objects.rs",
            "lean/Runtime/Proofs/Conservation/Evidence.lean",
            "Provides the strong reference required on parity-critical follow-on paths.",
        ),
        entry(
            "ownership_receipt",
            TransitionClass,
            &[Issued, Committed, RolledBack, Rejected, Invalidated, Expired],
            "rust/machine/src/session/overview.rs",
            "lean/Runtime/Proofs/Conservation/Authority.lean",
            "Stages and commits explicit ownership transfer rather than ambient authority mutation.",
        ),
        entry(
            "semantic_handoff",
            TransitionClass,
            &[Committed, RolledBack, Rejected, Invalidated],
            "rust/machine/src/semantic_objects.rs",
            "lean/Runtime/Proofs/Conservation/Authority.lean",
            "Represents explicit protocol-visible authority transfer and old-owner revocation.",
        ),
        entry(
            "reconfiguration_transition",
            TransitionClass,
            &[Issued, Committed, RolledBack, Rejected],
            "rust/machine/src/composition.rs",
            "lean/Runtime/Proofs/ReconfigurationObserver.lean",
            "Captures protocol-critical cutover and membership/runtime transition artifacts.",
        ),
    ]
}

/// Canonical Rust source-of-truth boundary for the first-class capability model.
#[must_use]
pub fn rust_first_class_capability_module_boundary() -> &'static [&'static str] {
    &[
        "rust/machine/src/capabilities.rs",
        "rust/machine/src/runtime_contracts.rs",
        "rust/machine/src/session/overview.rs",
        "rust/machine/src/semantic_objects.rs",
        "rust/machine/src/composition.rs",
    ]
}

/// Canonical Lean theorem/model boundary for the first-class capability model.
#[must_use]
pub fn lean_first_class_capability_module_boundary() -> &'static [&'static str] {
    &[
        "lean/Runtime/Proofs/Capabilities.lean",
        "lean/Runtime/Proofs/AuthorityMetatheory.lean",
        "lean/Runtime/Proofs/Conservation/Authority.lean",
        "lean/Runtime/Proofs/Conservation/Evidence.lean",
        "lean/Runtime/Proofs/ReconfigurationObserver.lean",
        "lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean",
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capability_boundary_surfaces_are_unique_and_classified() {
        let boundary = protocol_critical_capability_boundary();
        assert!(
            !boundary.is_empty(),
            "protocol-critical capability boundary should not be empty"
        );

        let mut surfaces = std::collections::BTreeSet::new();
        for entry in &boundary {
            assert!(
                surfaces.insert(entry.surface.as_str()),
                "duplicate capability boundary surface: {}",
                entry.surface
            );
            assert!(
                !entry.lifecycle.is_empty(),
                "capability surface must declare lifecycle states: {}",
                entry.surface
            );
            assert!(
                !entry.rust_module.is_empty() && !entry.lean_module.is_empty(),
                "capability surface must declare both Rust and Lean boundaries: {}",
                entry.surface
            );
        }
    }

    #[test]
    fn capability_boundaries_cover_all_four_classes() {
        let classes: std::collections::BTreeSet<_> = protocol_critical_capability_boundary()
            .into_iter()
            .map(|entry| entry.class)
            .collect();
        assert_eq!(
            classes,
            [
                ProtocolCriticalCapabilityClass::Admission,
                ProtocolCriticalCapabilityClass::Ownership,
                ProtocolCriticalCapabilityClass::Evidence,
                ProtocolCriticalCapabilityClass::Transition,
            ]
            .into_iter()
            .collect()
        );
    }
}
