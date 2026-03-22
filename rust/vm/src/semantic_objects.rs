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
use std::collections::BTreeMap;

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

/// Observer/export class for one canonical publication path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PublicationObserverClass {
    Canonical,
    Audit,
}

/// Status for one canonical publication event.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PublicationStatus {
    Published,
    Rejected,
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
    #[serde(default)]
    pub revoked_owner_id: String,
    #[serde(default)]
    pub activated_owner_id: String,
    pub scope: OwnershipScope,
    pub status: DelegationStatus,
    pub tick: u64,
    pub reason: Option<String>,
}

/// Explicit transformation-local obligation bundle carried by one handoff.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransformationObligation {
    pub obligation_id: String,
    pub handoff_id: u64,
    pub session: SessionId,
    pub transformed_fragments: Vec<String>,
    pub affected_operation_ids: Vec<String>,
    pub affected_effect_ids: Vec<u64>,
    pub transported_effect_ids: Vec<u64>,
    pub invalidated_effect_ids: Vec<u64>,
    pub witness_policy: String,
    pub publication_revoked_from: String,
    pub publication_activated_to: String,
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

/// Canonical semantic publication event.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicationEvent {
    pub publication_id: String,
    pub session: Option<SessionId>,
    pub operation_id: String,
    pub owner_id: Option<FragmentOwnerId>,
    pub publication: String,
    pub observer_class: PublicationObserverClass,
    pub status: PublicationStatus,
    pub proof_ref: Option<String>,
    pub handle_ref: Option<String>,
    pub reason: Option<String>,
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
    #[serde(default)]
    pub transformation_obligations: Vec<TransformationObligation>,
    pub authoritative_reads: Vec<AuthoritativeRead>,
    pub observed_reads: Vec<ObservedRead>,
    pub materialization_proofs: Vec<MaterializationProof>,
    pub canonical_handles: Vec<CanonicalHandle>,
    #[serde(default)]
    pub publication_events: Vec<PublicationEvent>,
    pub progress_contracts: Vec<ProgressContract>,
}

impl Default for ProtocolMachineSemanticObjects {
    fn default() -> Self {
        Self {
            schema_version: default_semantic_objects_schema_version(),
            operation_instances: Vec::new(),
            outstanding_effects: Vec::new(),
            semantic_handoffs: Vec::new(),
            transformation_obligations: Vec::new(),
            authoritative_reads: Vec::new(),
            observed_reads: Vec::new(),
            materialization_proofs: Vec::new(),
            canonical_handles: Vec::new(),
            publication_events: Vec::new(),
            progress_contracts: Vec::new(),
        }
    }
}

impl ProtocolMachineSemanticObjects {
    /// Require one semantic-path read to be authoritative rather than observational.
    ///
    /// # Errors
    ///
    /// Returns a descriptive error when the read is observational or unknown.
    pub fn require_authoritative_read(&self, read_id: &str) -> Result<&AuthoritativeRead, String> {
        if let Some(read) = self
            .authoritative_reads
            .iter()
            .find(|read| read.read_id == read_id)
        {
            return Ok(read);
        }
        if self
            .observed_reads
            .iter()
            .any(|read| read.read_id == read_id)
        {
            return Err(format!(
                "observed read `{read_id}` may not be consumed on a semantic path; use an AuthoritativeRead instead"
            ));
        }
        Err(format!("semantic read `{read_id}` is unknown"))
    }

    /// Require one strong canonical handle on a parity-critical path.
    ///
    /// # Errors
    ///
    /// Returns a descriptive error when the handle is missing.
    pub fn require_canonical_handle(&self, handle_id: &str) -> Result<&CanonicalHandle, String> {
        self.canonical_handles
            .iter()
            .find(|handle| handle.handle_id == handle_id)
            .ok_or_else(|| {
                format!("canonical handle `{handle_id}` is required on this parity-critical path")
            })
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

fn coro_owner_id(coro_id: usize) -> String {
    format!("coro:{coro_id}")
}

fn transformed_fragments(scope: &OwnershipScope) -> Vec<String> {
    match scope {
        OwnershipScope::Session => vec!["session".to_string()],
        OwnershipScope::Fragments(fragments) => fragments.iter().cloned().collect(),
    }
}

fn publication_observer_class(publication: &str) -> PublicationObserverClass {
    if publication.starts_with("handoff.") || publication.starts_with("materialization.") {
        PublicationObserverClass::Audit
    } else {
        PublicationObserverClass::Canonical
    }
}

fn canonicalize(mut out: ProtocolMachineSemanticObjects) -> ProtocolMachineSemanticObjects {
    out.operation_instances
        .sort_by(|lhs, rhs| lhs.operation_id.cmp(&rhs.operation_id));
    out.outstanding_effects
        .sort_by(|lhs, rhs| lhs.effect_id.cmp(&rhs.effect_id));
    out.semantic_handoffs
        .sort_by(|lhs, rhs| lhs.handoff_id.cmp(&rhs.handoff_id));
    out.transformation_obligations
        .sort_by(|lhs, rhs| lhs.handoff_id.cmp(&rhs.handoff_id));
    out.authoritative_reads
        .sort_by(|lhs, rhs| lhs.read_id.cmp(&rhs.read_id));
    out.observed_reads
        .sort_by(|lhs, rhs| lhs.read_id.cmp(&rhs.read_id));
    out.materialization_proofs
        .sort_by(|lhs, rhs| lhs.proof_id.cmp(&rhs.proof_id));
    out.canonical_handles
        .sort_by(|lhs, rhs| lhs.handle_id.cmp(&rhs.handle_id));
    out.publication_events
        .sort_by(|lhs, rhs| lhs.publication_id.cmp(&rhs.publication_id));
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
            revoked_owner_id: coro_owner_id(record.receipt.from_coro),
            activated_owner_id: coro_owner_id(record.receipt.to_coro),
            scope: record.receipt.scope.clone(),
            status: record.status.clone(),
            tick: record.tick,
            reason: record.reason.clone(),
        })
        .collect();

    let transformation_obligations: Vec<_> = delegation_audit_log
        .iter()
        .map(|record| {
            let affected_operation_ids: Vec<_> = operation_instances
                .iter()
                .filter(|operation| operation.session == Some(record.receipt.session))
                .map(|operation| operation.operation_id.clone())
                .collect();
            let affected_effect_ids: Vec<_> = outstanding_effects
                .iter()
                .filter(|effect| effect.session == Some(record.receipt.session))
                .map(|effect| effect.effect_id)
                .collect();
            let transported_effect_ids: Vec<_> = outstanding_effects
                .iter()
                .filter(|effect| {
                    effect.session == Some(record.receipt.session)
                        && matches!(effect.status, OutstandingEffectStatus::Pending)
                })
                .map(|effect| effect.effect_id)
                .collect();
            let invalidated_effect_ids: Vec<_> = outstanding_effects
                .iter()
                .filter(|effect| {
                    effect.session == Some(record.receipt.session)
                        && matches!(effect.status, OutstandingEffectStatus::Invalidated)
                })
                .map(|effect| effect.effect_id)
                .collect();

            TransformationObligation {
                obligation_id: format!("handoff:{}", record.receipt.receipt_id),
                handoff_id: record.receipt.receipt_id,
                session: record.receipt.session,
                transformed_fragments: transformed_fragments(&record.receipt.scope),
                affected_operation_ids,
                affected_effect_ids,
                transported_effect_ids,
                invalidated_effect_ids,
                witness_policy: if matches!(record.status, DelegationStatus::Committed) {
                    "transport_pending_invalidate_blocked".to_string()
                } else {
                    "rollback".to_string()
                },
                publication_revoked_from: coro_owner_id(record.receipt.from_coro),
                publication_activated_to: coro_owner_id(record.receipt.to_coro),
                scope: record.receipt.scope.clone(),
                status: record.status.clone(),
                tick: record.tick,
                reason: record.reason.clone(),
            }
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

    let proof_by_operation: BTreeMap<String, String> = materialization_proofs
        .iter()
        .filter(|proof| proof.passed)
        .map(|proof| {
            (
                format!("materialization:{}", proof.proof_id),
                proof.proof_id.clone(),
            )
        })
        .collect();
    let handle_by_proof: BTreeMap<String, String> = canonical_handles
        .iter()
        .filter_map(|handle| {
            handle
                .proof_ref
                .as_ref()
                .map(|proof_ref| (proof_ref.clone(), handle.handle_id.clone()))
        })
        .collect();
    let mut publication_events = BTreeMap::<String, PublicationEvent>::new();
    for operation in &operation_instances {
        let Some(publication) = operation.terminal_publication.as_ref() else {
            continue;
        };
        let proof_ref = proof_by_operation
            .get(&operation.operation_id)
            .cloned()
            .or_else(|| {
                operation
                    .operation_id
                    .strip_prefix("handoff:")
                    .map(|suffix| format!("handoff:{suffix}"))
            });
        let handle_ref = proof_ref
            .as_ref()
            .and_then(|proof_ref| handle_by_proof.get(proof_ref).cloned());
        let (status, reason) = if operation.requires_proof && handle_ref.is_none() {
            (
                PublicationStatus::Rejected,
                Some("proof-bearing success required".to_string()),
            )
        } else {
            (PublicationStatus::Published, None)
        };
        let publication_id = format!("{}:{publication}", operation.operation_id);
        publication_events
            .entry(publication_id.clone())
            .or_insert(PublicationEvent {
                publication_id,
                session: operation.session,
                operation_id: operation.operation_id.clone(),
                owner_id: operation.owner_id.clone(),
                publication: publication.clone(),
                observer_class: publication_observer_class(publication),
                status,
                proof_ref,
                handle_ref,
                reason,
            });
    }

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
        transformation_obligations,
        authoritative_reads,
        observed_reads,
        materialization_proofs,
        canonical_handles,
        publication_events: publication_events.into_values().collect(),
        progress_contracts,
    })
}
