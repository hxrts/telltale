//! Canonical semantic objects exported by the protocol machine.
//!
//! These types are the stable runtime-facing object model for ownership,
//! effect, handoff, read, proof, handle, and progress state. They are derived
//! from lower-level audit/effect/output surfaces but should be the primary
//! exported semantic contract consumed by the bridge, replay tooling, and
//! higher-level runtimes.
#![allow(missing_docs)]

use crate::output_condition::OutputConditionCheck;
use crate::session::{
    AuthorityArtifact, AuthorityAuditEvent, AuthorityAuditRecord, AuthorityWitnessId,
    FragmentOwnerId, OwnershipEpoch, OwnershipScope, SessionId,
};
use crate::transfer_semantics::{DelegationAuditRecord, DelegationStatus};
use serde::{Deserialize, Serialize};

/// Canonical schema version identifier for semantic-object exports.
pub const SEMANTIC_OBJECTS_SCHEMA_VERSION: &str = "protocol_machine.semantic_objects.v1";

fn default_semantic_objects_schema_version() -> String {
    SEMANTIC_OBJECTS_SCHEMA_VERSION.to_string()
}

/// Lifecycle phase for one operation instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OperationPhase {
    Pending,
    Blocked,
    Succeeded,
    Failed,
    Cancelled,
    TimedOut,
    HandedOff,
}

/// Canonical status for one effect that is visible on the semantic path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OutstandingEffectStatus {
    Pending,
    Blocked,
    Succeeded,
    Failed,
    Cancelled,
    Invalidated,
}

/// Class of authoritative read/proof surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuthoritativeReadKind {
    Readiness,
    Cancellation,
    Timeout,
    OutputCondition,
}

/// Lifecycle for one authoritative read/proof artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuthoritativeReadLifecycle {
    Issued,
    Consumed,
    Rejected,
    Verified,
}

/// Kind of canonical handle surfaced by the runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CanonicalHandleKind {
    Materialization,
    Handoff,
}

/// Progress state for one operation-level contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProgressState {
    Pending,
    Blocked,
    Succeeded,
    Failed,
    Cancelled,
    TimedOut,
    HandedOff,
}

/// First-class view of one operation instance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationInstance {
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub owner_id: Option<FragmentOwnerId>,
    pub kind: String,
    pub phase: OperationPhase,
    pub handler_identity: Option<String>,
    pub effect_ids: Vec<u64>,
    pub dependent_operation_ids: Vec<String>,
    pub terminal_publication: Option<String>,
    pub budget_ticks: Option<u64>,
    pub requires_proof: bool,
}

/// First-class view of one deferred or completed effect.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct OutstandingEffect {
    pub effect_id: u64,
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub owner_id: Option<FragmentOwnerId>,
    pub effect_interface: Option<String>,
    pub effect_operation: Option<String>,
    pub effect_kind: String,
    pub handler_identity: String,
    pub status: OutstandingEffectStatus,
    pub ordering_key: u64,
    pub budget_ticks: Option<u64>,
    pub retry_policy: String,
    pub invalidation_token: String,
    pub completed_at_tick: Option<u64>,
    pub inputs: serde_json::Value,
    pub outputs: serde_json::Value,
}

/// First-class view of one semantic handoff.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticHandoff {
    pub handoff_id: u64,
    pub session: SessionId,
    pub from_coro: usize,
    pub to_coro: usize,
    pub scope: OwnershipScope,
    pub status: DelegationStatus,
    pub tick: u64,
    pub reason: Option<String>,
}

/// First-class view of one authoritative read/proof-bearing check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthoritativeRead {
    pub read_id: String,
    pub session: Option<SessionId>,
    pub owner_id: Option<FragmentOwnerId>,
    pub kind: AuthoritativeReadKind,
    pub lifecycle: AuthoritativeReadLifecycle,
    pub predicate_ref: Option<String>,
    pub witness_id: Option<AuthorityWitnessId>,
    pub generation: Option<OwnershipEpoch>,
    pub reason: Option<String>,
}

/// First-class view of one observational read.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservedRead {
    pub read_id: String,
    pub session: Option<SessionId>,
    pub effect_id: u64,
    pub effect_interface: Option<String>,
    pub effect_operation: Option<String>,
    pub handler_identity: String,
    pub status: OutstandingEffectStatus,
}

/// First-class view of one materialization proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MaterializationProof {
    pub proof_id: String,
    pub session: Option<SessionId>,
    pub predicate_ref: String,
    pub witness_ref: Option<String>,
    pub output_digest: String,
    pub passed: bool,
}

/// First-class strong handle surfaced from sanctioned semantic paths.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CanonicalHandle {
    pub handle_id: String,
    pub session: Option<SessionId>,
    pub owner_id: Option<FragmentOwnerId>,
    pub kind: CanonicalHandleKind,
    pub proof_ref: Option<String>,
}

/// Explicit progress contract attached to one operation instance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgressContract {
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub state: ProgressState,
    pub last_ordering_key: Option<u64>,
    pub bounded: bool,
}

/// Canonical bundle of semantic objects exported by the protocol machine.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ProtocolMachineSemanticObjects {
    #[serde(default = "default_semantic_objects_schema_version")]
    pub schema_version: String,
    pub operation_instances: Vec<OperationInstance>,
    pub outstanding_effects: Vec<OutstandingEffect>,
    pub semantic_handoffs: Vec<SemanticHandoff>,
    pub authoritative_reads: Vec<AuthoritativeRead>,
    pub observed_reads: Vec<ObservedRead>,
    pub materialization_proofs: Vec<MaterializationProof>,
    pub canonical_handles: Vec<CanonicalHandle>,
    pub progress_contracts: Vec<ProgressContract>,
}

impl Default for ProtocolMachineSemanticObjects {
    fn default() -> Self {
        Self {
            schema_version: default_semantic_objects_schema_version(),
            operation_instances: Vec::new(),
            outstanding_effects: Vec::new(),
            semantic_handoffs: Vec::new(),
            authoritative_reads: Vec::new(),
            observed_reads: Vec::new(),
            materialization_proofs: Vec::new(),
            canonical_handles: Vec::new(),
            progress_contracts: Vec::new(),
        }
    }
}

fn progress_state(status: OutstandingEffectStatus) -> ProgressState {
    match status {
        OutstandingEffectStatus::Pending => ProgressState::Pending,
        OutstandingEffectStatus::Blocked => ProgressState::Blocked,
        OutstandingEffectStatus::Succeeded => ProgressState::Succeeded,
        OutstandingEffectStatus::Failed => ProgressState::Failed,
        OutstandingEffectStatus::Cancelled => ProgressState::Cancelled,
        OutstandingEffectStatus::Invalidated => ProgressState::Failed,
    }
}

fn authority_read_lifecycle(event: AuthorityAuditEvent) -> AuthoritativeReadLifecycle {
    match event {
        AuthorityAuditEvent::Issued => AuthoritativeReadLifecycle::Issued,
        AuthorityAuditEvent::Consumed => AuthoritativeReadLifecycle::Consumed,
        AuthorityAuditEvent::Rejected => AuthoritativeReadLifecycle::Rejected,
    }
}

fn authority_read_from_record(record: &AuthorityAuditRecord) -> AuthoritativeRead {
    match &record.artifact {
        AuthorityArtifact::Readiness(witness) => AuthoritativeRead {
            read_id: format!("readiness:{}:{:?}", witness.witness_id, record.event),
            session: Some(witness.session_id),
            owner_id: Some(witness.owner_id.clone()),
            kind: AuthoritativeReadKind::Readiness,
            lifecycle: authority_read_lifecycle(record.event),
            predicate_ref: Some(witness.predicate_ref.clone()),
            witness_id: Some(witness.witness_id),
            generation: Some(witness.generation),
            reason: record.reason.clone(),
        },
        AuthorityArtifact::Cancellation(witness) => AuthoritativeRead {
            read_id: format!("cancellation:{}:{:?}", witness.witness_id, record.event),
            session: Some(witness.session_id),
            owner_id: Some(witness.owner_id.clone()),
            kind: AuthoritativeReadKind::Cancellation,
            lifecycle: authority_read_lifecycle(record.event),
            predicate_ref: None,
            witness_id: Some(witness.witness_id),
            generation: Some(witness.generation),
            reason: record.reason.clone(),
        },
        AuthorityArtifact::Timeout(witness) => AuthoritativeRead {
            read_id: format!("timeout:{}:{:?}", witness.witness_id, record.event),
            session: None,
            owner_id: None,
            kind: AuthoritativeReadKind::Timeout,
            lifecycle: authority_read_lifecycle(record.event),
            predicate_ref: None,
            witness_id: Some(witness.witness_id),
            generation: None,
            reason: record.reason.clone(),
        },
    }
}

fn proof_id(check: &OutputConditionCheck) -> String {
    format!("{}:{}", check.meta.predicate_ref, check.meta.output_digest)
}

fn canonicalize(mut out: ProtocolMachineSemanticObjects) -> ProtocolMachineSemanticObjects {
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

/// Build the canonical semantic-object bundle from lower-level runtime
/// artifacts.
#[must_use]
pub fn protocol_machine_semantic_objects_v1(
    authority_audit_log: &[AuthorityAuditRecord],
    delegation_audit_log: &[DelegationAuditRecord],
    operation_instances: &[OperationInstance],
    outstanding_effects: &[OutstandingEffect],
    output_condition_checks: &[OutputConditionCheck],
) -> ProtocolMachineSemanticObjects {
    let mut operation_instances = operation_instances.to_vec();
    let outstanding_effects = outstanding_effects.to_vec();

    let semantic_handoffs: Vec<_> = delegation_audit_log
        .iter()
        .map(|record| SemanticHandoff {
            handoff_id: record.receipt.receipt_id,
            session: record.receipt.session,
            from_coro: record.receipt.from_coro,
            to_coro: record.receipt.to_coro,
            scope: record.receipt.scope.clone(),
            status: record.status.clone(),
            tick: record.tick,
            reason: record.reason.clone(),
        })
        .collect();

    operation_instances.extend(semantic_handoffs.iter().map(|handoff| OperationInstance {
        operation_id: format!("handoff:{}", handoff.handoff_id),
        session: Some(handoff.session),
        owner_id: None,
        kind: "semantic_handoff".to_string(),
        phase: OperationPhase::HandedOff,
        handler_identity: None,
        effect_ids: Vec::new(),
        dependent_operation_ids: Vec::new(),
        terminal_publication: Some("handoff.committed".to_string()),
        budget_ticks: Some(1),
        requires_proof: false,
    }));

    let mut authoritative_reads: Vec<_> = authority_audit_log
        .iter()
        .map(authority_read_from_record)
        .collect();
    authoritative_reads.extend(
        output_condition_checks
            .iter()
            .map(|check| AuthoritativeRead {
                read_id: format!("output_condition:{}", proof_id(check)),
                session: None,
                owner_id: None,
                kind: AuthoritativeReadKind::OutputCondition,
                lifecycle: if check.passed {
                    AuthoritativeReadLifecycle::Verified
                } else {
                    AuthoritativeReadLifecycle::Rejected
                },
                predicate_ref: Some(check.meta.predicate_ref.clone()),
                witness_id: None,
                generation: None,
                reason: (!check.passed).then(|| "output condition failed".to_string()),
            }),
    );

    let observed_reads: Vec<_> = outstanding_effects
        .iter()
        .map(|effect| ObservedRead {
            read_id: format!("effect:{}", effect.effect_id),
            session: effect.session,
            effect_id: effect.effect_id,
            effect_interface: effect.effect_interface.clone(),
            effect_operation: effect.effect_operation.clone(),
            handler_identity: effect.handler_identity.clone(),
            status: effect.status,
        })
        .collect();

    let materialization_proofs: Vec<_> = output_condition_checks
        .iter()
        .map(|check| MaterializationProof {
            proof_id: proof_id(check),
            session: None,
            predicate_ref: check.meta.predicate_ref.clone(),
            witness_ref: check.meta.witness_ref.clone(),
            output_digest: check.meta.output_digest.clone(),
            passed: check.passed,
        })
        .collect();

    operation_instances.extend(
        materialization_proofs
            .iter()
            .map(|proof| OperationInstance {
                operation_id: format!("materialization:{}", proof.proof_id),
                session: proof.session,
                owner_id: None,
                kind: "materialization".to_string(),
                phase: if proof.passed {
                    OperationPhase::Succeeded
                } else {
                    OperationPhase::Failed
                },
                handler_identity: None,
                effect_ids: Vec::new(),
                dependent_operation_ids: Vec::new(),
                terminal_publication: Some(if proof.passed {
                    "materialization.succeeded".to_string()
                } else {
                    "materialization.failed".to_string()
                }),
                budget_ticks: Some(1),
                requires_proof: true,
            }),
    );

    let mut canonical_handles: Vec<_> = materialization_proofs
        .iter()
        .filter(|proof| proof.passed)
        .map(|proof| CanonicalHandle {
            handle_id: format!("materialization:{}", proof.output_digest),
            session: proof.session,
            owner_id: None,
            kind: CanonicalHandleKind::Materialization,
            proof_ref: Some(proof.proof_id.clone()),
        })
        .collect();
    canonical_handles.extend(semantic_handoffs.iter().filter_map(|handoff| {
        matches!(handoff.status, DelegationStatus::Committed).then(|| CanonicalHandle {
            handle_id: format!("handoff:{}", handoff.handoff_id),
            session: Some(handoff.session),
            owner_id: None,
            kind: CanonicalHandleKind::Handoff,
            proof_ref: Some(format!("handoff:{}", handoff.handoff_id)),
        })
    }));

    let mut progress_contracts: Vec<_> = outstanding_effects
        .iter()
        .map(|effect| ProgressContract {
            operation_id: effect.operation_id.clone(),
            session: effect.session,
            state: progress_state(effect.status),
            last_ordering_key: Some(effect.ordering_key),
            bounded: true,
        })
        .collect();
    progress_contracts.extend(semantic_handoffs.iter().map(|handoff| ProgressContract {
        operation_id: format!("handoff:{}", handoff.handoff_id),
        session: Some(handoff.session),
        state: ProgressState::HandedOff,
        last_ordering_key: Some(handoff.tick),
        bounded: true,
    }));

    canonicalize(ProtocolMachineSemanticObjects {
        schema_version: default_semantic_objects_schema_version(),
        operation_instances,
        outstanding_effects,
        semantic_handoffs,
        authoritative_reads,
        observed_reads,
        materialization_proofs,
        canonical_handles,
        progress_contracts,
    })
}
