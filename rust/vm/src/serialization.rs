//! Canonical serialization helpers for deterministic replay/testing artifacts.

use crate::communication_replay::{CommunicationConsumptionArtifact, CommunicationReplayMode};
use crate::determinism::EffectDeterminismTier;
use crate::effect::{CorruptionType, EffectTraceEntry};
use crate::output_condition::OutputConditionCheck;
use crate::semantic_objects::{
    protocol_machine_semantic_objects_v1, OperationInstance, OutstandingEffect,
    ProtocolMachineSemanticObjects, TransformationObligation,
};
use crate::session::{
    AuthorityArtifact, AuthorityAuditEvent, AuthorityAuditRecord, AuthorityWitnessId,
    FragmentOwnerId, OwnershipTerminalReason, SessionId,
};
use crate::trace::normalize_trace;
use crate::transfer_semantics::{DelegationAuditRecord, DelegationReceipt, DelegationStatus};
use crate::verification::Hash;
use crate::vm::{ObsEvent, SessionTerminalReason};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::Value as JsonValue;

/// Canonical schema version identifier for VM replay/trace payloads.
pub const SERIALIZATION_SCHEMA_VERSION: &str = "vm.serialization.v1";

fn default_serialization_schema_version() -> String {
    SERIALIZATION_SCHEMA_VERSION.to_string()
}

fn normalize_serialization_schema_version(raw: &str) -> String {
    if raw == "1" {
        SERIALIZATION_SCHEMA_VERSION.to_string()
    } else {
        raw.to_string()
    }
}

/// Serialize one value through the canonical VM binary codec.
///
/// This wrapper keeps binary-serialization policy centralized inside the VM
/// crate instead of scattering direct `bincode` calls through runtime code.
///
/// # Errors
///
/// Returns a `bincode::Error` if the value cannot be serialized by the
/// canonical binary codec.
pub fn binary_encode<T: Serialize + ?Sized>(value: &T) -> Result<Vec<u8>, bincode::Error> {
    bincode::serialize(value)
}

/// Deserialize one value through the canonical VM binary codec.
///
/// This wrapper keeps binary-serialization policy centralized inside the VM
/// crate instead of scattering direct `bincode` calls through runtime code.
///
/// # Errors
///
/// Returns a `bincode::Error` if the bytes do not decode as the requested type
/// under the canonical binary codec.
pub fn binary_decode<T: DeserializeOwned>(bytes: &[u8]) -> Result<T, bincode::Error> {
    bincode::deserialize(bytes)
}

/// Return the binary-encoded size for one value, saturating to `usize`.
#[must_use]
pub fn binary_size<T: Serialize + ?Sized>(value: &T) -> usize {
    bincode::serialized_size(value)
        .ok()
        .and_then(|bytes| usize::try_from(bytes).ok())
        .unwrap_or(0)
}

fn deserialize_serialization_schema_version<'de, D>(deserializer: D) -> Result<String, D::Error>
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
        SchemaVersionValue::String(version) => normalize_serialization_schema_version(&version),
        SchemaVersionValue::Integer(version) => {
            normalize_serialization_schema_version(&version.to_string())
        }
    })
}

/// Versioned canonical trace payload used for cross-target normalization.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CanonicalTraceV1 {
    /// Schema version for canonical trace serialization.
    #[serde(
        default = "default_serialization_schema_version",
        deserialize_with = "deserialize_serialization_schema_version"
    )]
    pub schema_version: String,
    /// Canonically normalized observable events.
    pub events: Vec<ObsEvent>,
}

/// Versioned canonical replay-state fragment used by tests and replay checks.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CanonicalReplayFragmentV1 {
    /// Schema version for canonical replay serialization.
    #[serde(
        default = "default_serialization_schema_version",
        deserialize_with = "deserialize_serialization_schema_version"
    )]
    pub schema_version: String,
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
    /// Active communication replay mode.
    #[serde(default)]
    pub communication_replay_mode: CommunicationReplayMode,
    /// Deterministic communication replay-state root.
    #[serde(default)]
    pub communication_replay_root: Option<Hash>,
    /// Proof-friendly receive consumption artifacts.
    #[serde(default)]
    pub communication_consumption_artifacts: Vec<CommunicationConsumptionArtifact>,
    /// Canonical semantic audit records derived from authority/failure/effect surfaces.
    #[serde(default)]
    pub semantic_audit_log: Vec<SemanticAuditRecord>,
    /// Canonical semantic objects derived from authority, delegation,
    /// effect, and proof surfaces.
    #[serde(default)]
    pub semantic_objects: ProtocolMachineSemanticObjects,
}

/// Replay-stable semantic record derived from authority, delegation, effect, and
/// failure-visible runtime artifacts.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum SemanticAuditRecord {
    /// Authority witness issuance/consumption/rejection.
    Authority {
        /// Scheduler tick associated with the authority artifact, when present.
        tick: Option<u64>,
        /// Session referenced by the authority artifact, when session-scoped.
        session: Option<SessionId>,
        /// Authority witness or receipt artifact carried by the audit record.
        artifact: AuthorityArtifact,
        /// Audit event kind recorded for the authority artifact.
        event: AuthorityAuditEvent,
        /// Optional rejection or failure reason associated with the audit record.
        reason: Option<String>,
    },
    /// Delegation/transfer completion or rollback.
    Delegation {
        /// Scheduler tick at which the delegation audit record was emitted.
        tick: u64,
        /// Session being delegated.
        session: SessionId,
        /// Delegation receipt proving the sanctioned transfer path.
        receipt: DelegationReceipt,
        /// Final delegation status for the receipt.
        status: DelegationStatus,
        /// Optional rollback or rejection reason for the transfer.
        reason: Option<String>,
    },
    /// Transformation-local obligation bundle emitted for one handoff.
    TransformationObligation {
        /// Scheduler tick at which the obligation became canonical.
        tick: u64,
        /// Session whose fragments were transformed.
        session: SessionId,
        /// Explicit obligation bundle tied to the handoff.
        obligation: TransformationObligation,
    },
    /// Explicit typed failure branch entry.
    FailureBranch {
        /// Scheduler tick at which the failure branch became visible.
        tick: u64,
        /// Session containing the failing coroutine.
        session: SessionId,
        /// Coroutine entering the failure branch.
        coro_id: usize,
        /// Typed fault surfaced by the branch.
        fault: crate::coroutine::Fault,
    },
    /// Explicit timeout activation and timeout witness issuance.
    TimeoutIssued {
        /// Scheduler tick at which the timeout became active.
        tick: u64,
        /// Site for which timeout was issued.
        site: String,
        /// Tick horizon until which the timeout remains active.
        until_tick: u64,
        /// Issued timeout witness identifier.
        witness_id: AuthorityWitnessId,
    },
    /// Explicit cancellation request.
    CancellationRequested {
        /// Scheduler tick at which cancellation was requested.
        tick: u64,
        /// Session being cancelled.
        session: SessionId,
        /// Cancellation witness authorizing the request.
        witness_id: AuthorityWitnessId,
        /// Owner capability active when cancellation was requested.
        owner_id: FragmentOwnerId,
        /// Terminal ownership reason causing the cancellation request.
        reason: OwnershipTerminalReason,
    },
    /// Explicit cancellation completion.
    Cancelled {
        /// Scheduler tick at which cancellation completed.
        tick: u64,
        /// Session that was cancelled.
        session: SessionId,
        /// Cancellation witness consumed by completion.
        witness_id: AuthorityWitnessId,
        /// Terminal ownership reason recorded for the cancellation.
        reason: OwnershipTerminalReason,
    },
    /// Explicit session terminal reason.
    SessionTerminal {
        /// Scheduler tick at which terminal state became visible.
        tick: u64,
        /// Session that reached terminal state.
        session: SessionId,
        /// Deterministic terminal reason recorded by the runtime.
        reason: SessionTerminalReason,
    },
    /// Structured effect/interface observation.
    EffectObservation {
        /// Stable effect identifier assigned by the runtime.
        effect_id: u64,
        /// Deterministic ordering key used for canonical replay comparison.
        ordering_key: u64,
        /// Session referenced by the effect observation, when derivable.
        session: Option<SessionId>,
        /// Raw runtime effect kind tag.
        effect_kind: String,
        /// Nominal effect interface classification, when known.
        effect_interface: Option<String>,
        /// Nominal effect operation classification, when known.
        effect_operation: Option<String>,
        /// Stable handler identity attached to the observation.
        handler_identity: String,
        /// Serialized effect inputs.
        inputs: JsonValue,
        /// Serialized effect outputs.
        outputs: JsonValue,
    },
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

fn authority_artifact_session(artifact: &AuthorityArtifact) -> Option<SessionId> {
    match artifact {
        AuthorityArtifact::Readiness(witness) => Some(witness.session_id),
        AuthorityArtifact::Cancellation(witness) => Some(witness.session_id),
        AuthorityArtifact::Timeout(_) => None,
    }
}

fn semantic_rank(record: &SemanticAuditRecord) -> u8 {
    match record {
        SemanticAuditRecord::Authority { .. } => 0,
        SemanticAuditRecord::Delegation { .. } => 1,
        SemanticAuditRecord::TransformationObligation { .. } => 2,
        SemanticAuditRecord::FailureBranch { .. } => 3,
        SemanticAuditRecord::TimeoutIssued { .. } => 4,
        SemanticAuditRecord::CancellationRequested { .. } => 5,
        SemanticAuditRecord::Cancelled { .. } => 6,
        SemanticAuditRecord::SessionTerminal { .. } => 7,
        SemanticAuditRecord::EffectObservation { .. } => 8,
    }
}

fn semantic_tick(record: &SemanticAuditRecord) -> u64 {
    match record {
        SemanticAuditRecord::Authority { tick, .. } => tick.unwrap_or(0),
        SemanticAuditRecord::Delegation { tick, .. }
        | SemanticAuditRecord::TransformationObligation { tick, .. }
        | SemanticAuditRecord::FailureBranch { tick, .. }
        | SemanticAuditRecord::TimeoutIssued { tick, .. }
        | SemanticAuditRecord::CancellationRequested { tick, .. }
        | SemanticAuditRecord::Cancelled { tick, .. }
        | SemanticAuditRecord::SessionTerminal { tick, .. } => *tick,
        SemanticAuditRecord::EffectObservation { ordering_key, .. } => *ordering_key,
    }
}

/// Canonicalize semantic audit ordering for deterministic replay diffs.
#[must_use]
pub fn canonical_semantic_audit_log(records: &[SemanticAuditRecord]) -> Vec<SemanticAuditRecord> {
    let mut out = records.to_vec();
    out.sort_by(|lhs, rhs| {
        let lhs_key = (
            semantic_tick(lhs),
            semantic_rank(lhs),
            serde_json::to_string(lhs).unwrap_or_default(),
        );
        let rhs_key = (
            semantic_tick(rhs),
            semantic_rank(rhs),
            serde_json::to_string(rhs).unwrap_or_default(),
        );
        lhs_key.cmp(&rhs_key)
    });
    out
}

/// Canonicalize semantic-object ordering for deterministic replay diffs.
#[must_use]
pub fn canonicalize_protocol_machine_semantic_objects(
    objects: &ProtocolMachineSemanticObjects,
) -> ProtocolMachineSemanticObjects {
    let mut out = objects.clone();
    out.operation_instances
        .sort_by(|lhs, rhs| lhs.operation_id.cmp(&rhs.operation_id));
    out.outstanding_effects
        .sort_by(|lhs, rhs| lhs.effect_id.cmp(&rhs.effect_id));
    out.semantic_handoffs
        .sort_by(|lhs, rhs| lhs.handoff_id.cmp(&rhs.handoff_id));
    out.authoritative_reads
        .sort_by(|lhs, rhs| lhs.read_id.cmp(&rhs.read_id));
    out.observed_reads
        .sort_by(|lhs, rhs| lhs.read_id.cmp(&rhs.read_id));
    out.materialization_proofs
        .sort_by(|lhs, rhs| lhs.proof_id.cmp(&rhs.proof_id));
    out.canonical_handles
        .sort_by(|lhs, rhs| lhs.handle_id.cmp(&rhs.handle_id));
    out.progress_contracts
        .sort_by(|lhs, rhs| lhs.operation_id.cmp(&rhs.operation_id));
    out
}

/// Build canonical semantic audit records from authority, delegation,
/// failure-visible observable events, and effect/interface observations.
#[must_use]
pub fn semantic_audit_log_v1(
    authority_audit_log: &[AuthorityAuditRecord],
    delegation_audit_log: &[DelegationAuditRecord],
    operation_instances: &[OperationInstance],
    obs_trace: &[ObsEvent],
    outstanding_effects: &[OutstandingEffect],
) -> Vec<SemanticAuditRecord> {
    let mut records = Vec::new();

    records.extend(authority_audit_log.iter().cloned().map(|record| {
        SemanticAuditRecord::Authority {
            tick: record.tick,
            session: authority_artifact_session(&record.artifact),
            artifact: record.artifact,
            event: record.event,
            reason: record.reason,
        }
    }));

    records.extend(delegation_audit_log.iter().cloned().map(|record| {
        SemanticAuditRecord::Delegation {
            tick: record.tick,
            session: record.receipt.session,
            receipt: record.receipt,
            status: record.status,
            reason: record.reason,
        }
    }));

    let obligations = protocol_machine_semantic_objects_v1(
        authority_audit_log,
        delegation_audit_log,
        operation_instances,
        outstanding_effects,
        &[],
    )
    .transformation_obligations;
    records.extend(obligations.into_iter().map(|obligation| {
        SemanticAuditRecord::TransformationObligation {
            tick: obligation.tick,
            session: obligation.session,
            obligation,
        }
    }));

    records.extend(obs_trace.iter().filter_map(|event| match event {
        ObsEvent::FailureBranchEntered {
            tick,
            session,
            coro_id,
            fault,
        } => Some(SemanticAuditRecord::FailureBranch {
            tick: *tick,
            session: *session,
            coro_id: *coro_id,
            fault: fault.clone(),
        }),
        ObsEvent::TimeoutIssued {
            tick,
            site,
            until_tick,
            witness_id,
        } => Some(SemanticAuditRecord::TimeoutIssued {
            tick: *tick,
            site: site.clone(),
            until_tick: *until_tick,
            witness_id: *witness_id,
        }),
        ObsEvent::CancellationRequested {
            tick,
            session,
            witness_id,
            owner_id,
            reason,
        } => Some(SemanticAuditRecord::CancellationRequested {
            tick: *tick,
            session: *session,
            witness_id: *witness_id,
            owner_id: owner_id.clone(),
            reason: reason.clone(),
        }),
        ObsEvent::Cancelled {
            tick,
            session,
            witness_id,
            reason,
        } => Some(SemanticAuditRecord::Cancelled {
            tick: *tick,
            session: *session,
            witness_id: *witness_id,
            reason: reason.clone(),
        }),
        ObsEvent::SessionTerminal {
            tick,
            session,
            reason,
        } => Some(SemanticAuditRecord::SessionTerminal {
            tick: *tick,
            session: *session,
            reason: reason.clone(),
        }),
        _ => None,
    }));

    records.extend(outstanding_effects.iter().cloned().map(|effect| {
        SemanticAuditRecord::EffectObservation {
            effect_id: effect.effect_id,
            ordering_key: effect.ordering_key,
            session: effect.session,
            effect_kind: effect.effect_kind,
            effect_interface: effect.effect_interface,
            effect_operation: effect.effect_operation,
            handler_identity: effect.handler_identity,
            inputs: effect.inputs,
            outputs: effect.outputs,
        }
    }));

    canonical_semantic_audit_log(&records)
}

/// Build a canonical replay-state fragment from runtime snapshots.
#[must_use]
#[allow(clippy::too_many_arguments)]
pub fn canonical_replay_fragment_v1(
    obs_trace: &[ObsEvent],
    effect_trace: &[EffectTraceEntry],
    authority_audit_log: &[AuthorityAuditRecord],
    delegation_audit_log: &[DelegationAuditRecord],
    operation_instances: &[OperationInstance],
    outstanding_effects: &[OutstandingEffect],
    output_condition_checks: &[OutputConditionCheck],
    mut crashed_sites: Vec<String>,
    mut partitioned_edges: Vec<(String, String)>,
    mut corrupted_edges: Vec<((String, String), CorruptionType)>,
    mut timed_out_sites: Vec<(String, u64)>,
    effect_determinism_tier: EffectDeterminismTier,
    communication_replay_mode: CommunicationReplayMode,
    communication_replay_root: Option<Hash>,
    communication_consumption_artifacts: Vec<CommunicationConsumptionArtifact>,
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
        communication_replay_mode,
        communication_replay_root,
        communication_consumption_artifacts,
        semantic_audit_log: semantic_audit_log_v1(
            authority_audit_log,
            delegation_audit_log,
            operation_instances,
            obs_trace,
            outstanding_effects,
        ),
        semantic_objects: canonicalize_protocol_machine_semantic_objects(
            &protocol_machine_semantic_objects_v1(
                authority_audit_log,
                delegation_audit_log,
                operation_instances,
                outstanding_effects,
                output_condition_checks,
            ),
        ),
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
                effect_interface: None,
                effect_operation: None,
                ordering_key: 3,
                topology: None,
            },
            EffectTraceEntry {
                effect_id: 1,
                effect_kind: "a".to_string(),
                inputs: serde_json::json!({}),
                outputs: serde_json::json!({}),
                handler_identity: "h".to_string(),
                effect_interface: None,
                effect_operation: None,
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
        assert_eq!(payload.schema_version, SERIALIZATION_SCHEMA_VERSION);
        assert_eq!(payload.events.len(), 1);
    }

    #[test]
    fn legacy_numeric_schema_version_deserializes_to_string_identifier() {
        let payload = serde_json::json!({
            "schema_version": 1,
            "events": []
        });
        let decoded: CanonicalTraceV1 =
            serde_json::from_value(payload).expect("legacy schema version should deserialize");
        assert_eq!(decoded.schema_version, SERIALIZATION_SCHEMA_VERSION);
    }
}
