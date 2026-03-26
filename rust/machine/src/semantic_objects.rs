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
    FragmentOwnerId, OwnershipEpoch, SessionId,
};
use crate::transfer_semantics::DelegationAuditRecord;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Canonical schema version identifier for semantic-object exports.
pub const SEMANTIC_OBJECTS_SCHEMA_VERSION: &str = "protocol_machine.semantic_objects.v1";

fn canonical_semantic_objects_schema_version() -> String {
    SEMANTIC_OBJECTS_SCHEMA_VERSION.to_string()
}

fn deserialize_semantic_objects_schema_version<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let version = String::deserialize(deserializer)?;
    if version == SEMANTIC_OBJECTS_SCHEMA_VERSION {
        Ok(version)
    } else {
        Err(serde::de::Error::custom(format!(
            "unsupported schema_version '{version}'; expected '{SEMANTIC_OBJECTS_SCHEMA_VERSION}'"
        )))
    }
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
    NoProgress,
    Degraded,
    Succeeded,
    Failed,
    Cancelled,
    TimedOut,
    HandedOff,
}

/// Visibility timing for one semantic operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OperationVisibility {
    Immediate,
    Pending,
    BlockedUntilFinalized,
}

/// Agreement grade reached for one operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AgreementLevel {
    None,
    Provisional,
    SoftSafe,
    Finalized,
}

/// Decision rule attached to one agreement contract.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AgreementRule {
    NoAgreement,
    AnyParticipant,
    Unanimous,
    Threshold { required_participants: u64 },
    Named { rule_name: String },
}

/// Evidence class attached to one agreement path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AgreementEvidenceKind {
    Witness,
    Certificate,
    CommitFact,
    Publication,
    Materialization,
}

/// Terminal outcome for one agreement/finalization path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FinalizationOutcome {
    Finalized,
    Aborted,
    Rejected,
    TimedOut,
}

/// Ownership scope carried by the canonical semantic-object family.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OwnershipScope {
    Session,
    Fragments(Vec<String>),
}

/// Delegation outcome carried by the canonical semantic-object family.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum DelegationStatus {
    Committed,
    RolledBack,
}

fn default_progress_contract_last_progress_tick() -> Option<u64> {
    None
}

fn default_progress_contract_escalated_at_tick() -> Option<u64> {
    None
}

fn default_progress_contract_reason() -> Option<String> {
    None
}

impl AgreementLevel {
    #[must_use]
    pub const fn rank(self) -> u8 {
        match self {
            Self::None => 0,
            Self::Provisional => 1,
            Self::SoftSafe => 2,
            Self::Finalized => 3,
        }
    }

    #[must_use]
    pub const fn at_least(self, required: Self) -> bool {
        self.rank() >= required.rank()
    }
}

impl OperationVisibility {
    #[must_use]
    pub const fn permits_use_at(self, level: AgreementLevel) -> bool {
        match self {
            Self::Immediate => true,
            Self::Pending => level.at_least(AgreementLevel::Provisional),
            Self::BlockedUntilFinalized => level.at_least(AgreementLevel::Finalized),
        }
    }
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

/// Stable prestate binding for one agreement-sensitive operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrestateBinding {
    pub binding_id: String,
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub state_digest: String,
    pub epoch_ref: Option<String>,
    pub participant_digest: Option<String>,
}

/// Reusable named agreement profile over the generic semantic core.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgreementProfile {
    pub profile_name: String,
    pub visibility: OperationVisibility,
    pub rule: AgreementRule,
    pub usable_at: AgreementLevel,
    pub finalized_at: AgreementLevel,
    pub required_evidence_kind: AgreementEvidenceKind,
}

/// Attached agreement contract for one operation instance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgreementContract {
    pub contract_name: String,
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub owner_id: Option<FragmentOwnerId>,
    pub profile_name: Option<String>,
    pub visibility: OperationVisibility,
    pub rule: AgreementRule,
    pub usable_at: AgreementLevel,
    pub finalized_at: AgreementLevel,
    pub required_evidence_kind: AgreementEvidenceKind,
}

/// Explicit evidence object carried on one agreement path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgreementEvidence {
    pub evidence_id: String,
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub owner_id: Option<FragmentOwnerId>,
    pub level: AgreementLevel,
    pub kind: AgreementEvidenceKind,
    pub reference: String,
    pub authoritative: bool,
}

/// Replay-visible agreement/finalization state for one operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgreementState {
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub owner_id: Option<FragmentOwnerId>,
    pub contract_name: String,
    pub level: AgreementLevel,
    pub finalization: Option<FinalizationOutcome>,
    pub evidence_ids: Vec<String>,
    pub last_updated_tick: Option<u64>,
    pub reason: Option<String>,
}

/// Canonical framing and locality domain for one session-scoped semantic slice.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Region {
    pub region_id: String,
    pub session: Option<SessionId>,
    pub owner_id: Option<FragmentOwnerId>,
    pub scope: OwnershipScope,
    pub operation_ids: Vec<String>,
    pub effect_ids: Vec<u64>,
    pub authoritative_read_ids: Vec<String>,
    pub handle_ids: Vec<String>,
    pub publication_ids: Vec<String>,
}

/// Explicit progress contract attached to one operation instance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgressContract {
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub state: ProgressState,
    pub last_ordering_key: Option<u64>,
    pub bounded: bool,
    #[serde(default)]
    pub budget_ticks: Option<u64>,
    #[serde(default = "default_progress_contract_last_progress_tick")]
    pub last_progress_tick: Option<u64>,
    #[serde(default = "default_progress_contract_escalated_at_tick")]
    pub escalated_at_tick: Option<u64>,
    #[serde(default = "default_progress_contract_reason")]
    pub reason: Option<String>,
}

/// Replay-visible progress transition for one operation-level contract.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgressTransition {
    pub operation_id: String,
    pub session: Option<SessionId>,
    pub from_state: ProgressState,
    pub to_state: ProgressState,
    pub tick: u64,
    pub reason: Option<String>,
}

impl PrestateBinding {
    #[must_use]
    pub fn binds_operation(&self, operation: &OperationInstance) -> bool {
        self.operation_id == operation.operation_id && self.session == operation.session
    }
}

impl AgreementProfile {
    #[must_use]
    pub fn supports_contract(&self, contract: &AgreementContract) -> bool {
        contract.profile_name.as_deref() == Some(self.profile_name.as_str())
            && contract.visibility == self.visibility
            && contract.rule == self.rule
            && contract.usable_at == self.usable_at
            && contract.finalized_at == self.finalized_at
            && contract.required_evidence_kind == self.required_evidence_kind
    }
}

impl AgreementContract {
    #[must_use]
    pub fn tracks_operation(&self, operation: &OperationInstance) -> bool {
        self.operation_id == operation.operation_id
            && self.session == operation.session
            && self.owner_id == operation.owner_id
    }

    #[must_use]
    pub fn provisional_usable(&self, state: &AgreementState) -> bool {
        state.tracks_contract(self)
            && state.level.at_least(self.usable_at)
            && self.visibility.permits_use_at(state.level)
            && !matches!(
                state.finalization,
                Some(FinalizationOutcome::Aborted)
                    | Some(FinalizationOutcome::Rejected)
                    | Some(FinalizationOutcome::TimedOut)
            )
    }

    #[must_use]
    pub fn finalization_admissible(
        &self,
        binding: &PrestateBinding,
        evidence: &AgreementEvidence,
        state: &AgreementState,
    ) -> bool {
        state.tracks_contract(self)
            && binding.operation_id == self.operation_id
            && binding.session == self.session
            && evidence.satisfies_contract(self)
            && evidence.level.at_least(self.finalized_at)
            && state.level == self.finalized_at
            && state.finalization == Some(FinalizationOutcome::Finalized)
    }

    #[must_use]
    pub fn aborted_state(&self, state: &AgreementState) -> bool {
        state.tracks_contract(self) && state.finalization == Some(FinalizationOutcome::Aborted)
    }
}

impl AgreementEvidence {
    #[must_use]
    pub fn satisfies_contract(&self, contract: &AgreementContract) -> bool {
        self.operation_id == contract.operation_id
            && self.session == contract.session
            && self.owner_id == contract.owner_id
            && self.kind == contract.required_evidence_kind
            && self.authoritative
    }
}

impl AgreementState {
    #[must_use]
    pub fn tracks_contract(&self, contract: &AgreementContract) -> bool {
        self.operation_id == contract.operation_id
            && self.session == contract.session
            && self.owner_id == contract.owner_id
            && self.contract_name == contract.contract_name
    }

    #[must_use]
    pub fn is_terminal(&self) -> bool {
        self.finalization.is_some()
    }
}

impl PublicationEvent {
    #[must_use]
    pub fn supports_agreement_evidence(&self, evidence: &AgreementEvidence) -> bool {
        evidence.kind == AgreementEvidenceKind::Publication
            && evidence.reference == self.publication_id
            && evidence.operation_id == self.operation_id
            && evidence.session == self.session
            && evidence.owner_id == self.owner_id
            && evidence.authoritative == (self.proof_ref.is_some() && self.handle_ref.is_some())
    }
}

impl MaterializationProof {
    #[must_use]
    pub fn supports_agreement_evidence(&self, evidence: &AgreementEvidence) -> bool {
        evidence.kind == AgreementEvidenceKind::Materialization
            && evidence.reference == self.proof_id
            && evidence.session == self.session
            && evidence.authoritative == self.passed
    }
}

impl CanonicalHandle {
    #[must_use]
    pub fn supports_agreement_evidence(&self, evidence: &AgreementEvidence) -> bool {
        evidence.reference == self.handle_id
            && evidence.session == self.session
            && evidence.owner_id == self.owner_id
    }
}

impl SemanticHandoff {
    #[must_use]
    pub fn relocates_agreement_state(&self, state: &AgreementState) -> bool {
        state.session == Some(self.session)
            && state.owner_id.as_deref() == Some(self.activated_owner_id.as_str())
    }
}

impl OperationInstance {
    /// Whether the operation is parity-critical.
    #[must_use]
    pub fn is_parity_critical(&self) -> bool {
        self.requires_proof || self.terminal_publication.is_some()
    }

    /// Whether commitment state and agreement state align on terminal truth.
    #[must_use]
    pub fn commitment_aligned_with_agreement_state(&self, state: &AgreementState) -> bool {
        self.operation_id == state.operation_id
            && self.session == state.session
            && (self.phase != OperationPhase::Succeeded
                || state.finalization == Some(FinalizationOutcome::Finalized))
            && (state.finalization != Some(FinalizationOutcome::Finalized)
                || matches!(
                    self.phase,
                    OperationPhase::Succeeded | OperationPhase::HandedOff
                ))
            && (state.finalization != Some(FinalizationOutcome::Aborted)
                || matches!(
                    self.phase,
                    OperationPhase::Failed | OperationPhase::Cancelled | OperationPhase::TimedOut
                ))
    }
}

impl ProgressState {
    /// Whether the progress state is terminal.
    #[must_use]
    pub fn is_terminal(self) -> bool {
        matches!(
            self,
            Self::Succeeded | Self::Failed | Self::Cancelled | Self::TimedOut | Self::HandedOff
        )
    }

    /// Expected operation phase for this progress state.
    #[must_use]
    pub fn expected_operation_phase(self) -> OperationPhase {
        match self {
            Self::Pending => OperationPhase::Pending,
            Self::Blocked | Self::NoProgress | Self::Degraded => OperationPhase::Blocked,
            Self::Succeeded => OperationPhase::Succeeded,
            Self::Failed => OperationPhase::Failed,
            Self::Cancelled => OperationPhase::Cancelled,
            Self::TimedOut => OperationPhase::TimedOut,
            Self::HandedOff => OperationPhase::HandedOff,
        }
    }
}

impl ProgressContract {
    /// Whether the contract is terminal.
    #[must_use]
    pub fn is_terminal(&self) -> bool {
        self.state.is_terminal()
    }

    /// Whether the contract carries bounded-wait discipline.
    #[must_use]
    pub fn has_budget_discipline(&self) -> bool {
        !self.bounded || self.budget_ticks.is_some()
    }

    /// Whether the contract tracks the given operation.
    #[must_use]
    pub fn tracks_operation(&self, operation: &OperationInstance) -> bool {
        self.operation_id == operation.operation_id
            && self.session == operation.session
            && operation.phase == self.state.expected_operation_phase()
    }

    /// Weighted progress measure aligned with the Lean synthetic-step model.
    #[must_use]
    pub fn progress_measure(&self) -> u64 {
        match self.state {
            ProgressState::Pending => 4,
            ProgressState::Blocked => 3,
            ProgressState::NoProgress => 2,
            ProgressState::Degraded => 1,
            ProgressState::Succeeded
            | ProgressState::Failed
            | ProgressState::Cancelled
            | ProgressState::TimedOut
            | ProgressState::HandedOff => 0,
        }
    }

    /// Synthetic progress escalation step used by the proof-aligned runtime model.
    #[must_use]
    pub fn synthetic_step(&self) -> Option<Self> {
        match self.state {
            ProgressState::Pending => Some(Self {
                state: ProgressState::Blocked,
                ..self.clone()
            }),
            ProgressState::Blocked => Some(Self {
                state: ProgressState::NoProgress,
                escalated_at_tick: self.escalated_at_tick.or(self.last_progress_tick),
                ..self.clone()
            }),
            ProgressState::NoProgress => Some(Self {
                state: ProgressState::Degraded,
                escalated_at_tick: self.escalated_at_tick.or(self.last_progress_tick),
                ..self.clone()
            }),
            ProgressState::Degraded => Some(Self {
                state: if self.bounded {
                    ProgressState::TimedOut
                } else {
                    ProgressState::Failed
                },
                escalated_at_tick: self.escalated_at_tick.or(self.last_progress_tick),
                ..self.clone()
            }),
            ProgressState::Succeeded
            | ProgressState::Failed
            | ProgressState::Cancelled
            | ProgressState::TimedOut
            | ProgressState::HandedOff => None,
        }
    }
}

/// Canonical bundle of semantic objects exported by the protocol machine.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ProtocolMachineSemanticObjects {
    #[serde(deserialize_with = "deserialize_semantic_objects_schema_version")]
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
    #[serde(default)]
    pub prestate_bindings: Vec<PrestateBinding>,
    #[serde(default)]
    pub agreement_profiles: Vec<AgreementProfile>,
    #[serde(default)]
    pub agreement_contracts: Vec<AgreementContract>,
    #[serde(default)]
    pub agreement_evidence: Vec<AgreementEvidence>,
    #[serde(default)]
    pub agreement_states: Vec<AgreementState>,
    pub regions: Vec<Region>,
    pub progress_contracts: Vec<ProgressContract>,
    #[serde(default)]
    pub progress_transitions: Vec<ProgressTransition>,
}

impl Default for ProtocolMachineSemanticObjects {
    fn default() -> Self {
        Self {
            schema_version: canonical_semantic_objects_schema_version(),
            operation_instances: Vec::new(),
            outstanding_effects: Vec::new(),
            semantic_handoffs: Vec::new(),
            transformation_obligations: Vec::new(),
            authoritative_reads: Vec::new(),
            observed_reads: Vec::new(),
            materialization_proofs: Vec::new(),
            canonical_handles: Vec::new(),
            publication_events: Vec::new(),
            prestate_bindings: Vec::new(),
            agreement_profiles: Vec::new(),
            agreement_contracts: Vec::new(),
            agreement_evidence: Vec::new(),
            agreement_states: Vec::new(),
            regions: Vec::new(),
            progress_contracts: Vec::new(),
            progress_transitions: Vec::new(),
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

    /// Whether every parity-critical operation has a matching progress contract.
    #[must_use]
    pub fn parity_critical_operations_have_progress_contracts(&self) -> bool {
        self.operation_instances
            .iter()
            .filter(|operation| operation.is_parity_critical())
            .all(|operation| {
                self.progress_contracts
                    .iter()
                    .any(|contract| contract.tracks_operation(operation))
            })
    }

    /// Whether one named agreement profile is present in the semantic bundle.
    #[must_use]
    pub fn named_agreement_profile_available(&self, profile_name: &str) -> bool {
        self.agreement_profiles
            .iter()
            .any(|profile| profile.profile_name == profile_name)
    }

    /// Whether one operation has a matching agreement contract.
    #[must_use]
    pub fn agreement_contract_for_operation(&self, operation: &OperationInstance) -> bool {
        self.agreement_contracts
            .iter()
            .any(|contract| contract.tracks_operation(operation))
    }

    /// Whether one operation has a matching agreement state.
    #[must_use]
    pub fn agreement_state_for_operation(&self, operation: &OperationInstance) -> bool {
        self.agreement_states.iter().any(|state| {
            state.operation_id == operation.operation_id && state.session == operation.session
        })
    }

    /// Whether one operation has a stable prestate binding.
    #[must_use]
    pub fn prestate_binding_for_operation(&self, operation: &OperationInstance) -> bool {
        self.prestate_bindings
            .iter()
            .any(|binding| binding.binds_operation(operation))
    }

    /// Whether one operation has explicit agreement evidence.
    #[must_use]
    pub fn agreement_evidence_for_operation(&self, operation: &OperationInstance) -> bool {
        self.agreement_evidence.iter().any(|evidence| {
            evidence.operation_id == operation.operation_id && evidence.session == operation.session
        })
    }

    /// Whether one operation is usable under its current agreement state.
    #[must_use]
    pub fn provisional_agreement_usable(&self, operation: &OperationInstance) -> bool {
        self.agreement_contracts.iter().any(|contract| {
            contract.tracks_operation(operation)
                && self
                    .agreement_states
                    .iter()
                    .any(|state| contract.provisional_usable(state))
        })
    }

    /// Whether one operation has explicit finalization backing.
    #[must_use]
    pub fn finalization_backed(&self, operation: &OperationInstance) -> bool {
        self.agreement_contracts.iter().any(|contract| {
            contract.tracks_operation(operation)
                && self.prestate_bindings.iter().any(|binding| {
                    self.agreement_evidence.iter().any(|evidence| {
                        self.agreement_states
                            .iter()
                            .any(|state| contract.finalization_admissible(binding, evidence, state))
                    })
                })
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
        OutstandingEffectStatus::Invalidated => ProgressState::TimedOut,
    }
}

fn progress_state_for_operation_phase(phase: OperationPhase) -> ProgressState {
    match phase {
        OperationPhase::Pending => ProgressState::Pending,
        OperationPhase::Blocked => ProgressState::Blocked,
        OperationPhase::Succeeded => ProgressState::Succeeded,
        OperationPhase::Failed => ProgressState::Failed,
        OperationPhase::Cancelled => ProgressState::Cancelled,
        OperationPhase::TimedOut => ProgressState::TimedOut,
        OperationPhase::HandedOff => ProgressState::HandedOff,
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
        OwnershipScope::Fragments(fragments) => fragments.clone(),
    }
}

fn semantic_ownership_scope(scope: &crate::session::OwnershipScope) -> OwnershipScope {
    match scope {
        crate::session::OwnershipScope::Session => OwnershipScope::Session,
        crate::session::OwnershipScope::Fragments(fragments) => {
            OwnershipScope::Fragments(fragments.iter().cloned().collect())
        }
    }
}

fn semantic_delegation_status(
    status: &crate::transfer_semantics::DelegationStatus,
) -> DelegationStatus {
    match status {
        crate::transfer_semantics::DelegationStatus::Committed => DelegationStatus::Committed,
        crate::transfer_semantics::DelegationStatus::RolledBack => DelegationStatus::RolledBack,
    }
}

fn publication_observer_class(publication: &str) -> PublicationObserverClass {
    if publication.starts_with("handoff.") || publication.starts_with("materialization.") {
        PublicationObserverClass::Audit
    } else {
        PublicationObserverClass::Canonical
    }
}

fn progress_state_rank(state: ProgressState) -> u8 {
    match state {
        ProgressState::Pending => 0,
        ProgressState::Blocked => 1,
        ProgressState::NoProgress => 2,
        ProgressState::Degraded => 3,
        ProgressState::Succeeded => 4,
        ProgressState::Failed => 5,
        ProgressState::Cancelled => 6,
        ProgressState::TimedOut => 7,
        ProgressState::HandedOff => 8,
    }
}

fn agreement_level_rank(level: AgreementLevel) -> u8 {
    level.rank()
}

fn operation_visibility(operation: &OperationInstance) -> OperationVisibility {
    if operation.requires_proof {
        OperationVisibility::BlockedUntilFinalized
    } else if operation.terminal_publication.is_some() {
        OperationVisibility::Pending
    } else {
        OperationVisibility::Immediate
    }
}

fn agreement_rule(operation: &OperationInstance) -> AgreementRule {
    if operation.requires_proof {
        AgreementRule::Named {
            rule_name: "proof_finalization".to_string(),
        }
    } else if !operation.dependent_operation_ids.is_empty() {
        AgreementRule::Named {
            rule_name: "dependent_work".to_string(),
        }
    } else {
        AgreementRule::NoAgreement
    }
}

fn agreement_profile_name(operation: &OperationInstance) -> String {
    if operation.requires_proof {
        "ProofFinalization".to_string()
    } else if !operation.dependent_operation_ids.is_empty() {
        "DependentWork".to_string()
    } else if operation.terminal_publication.is_some() {
        "PendingPublication".to_string()
    } else {
        "ImmediateLocal".to_string()
    }
}

fn required_agreement_evidence_kind(operation: &OperationInstance) -> AgreementEvidenceKind {
    if operation.requires_proof || operation.terminal_publication.is_some() {
        AgreementEvidenceKind::Publication
    } else {
        AgreementEvidenceKind::Witness
    }
}

fn usable_agreement_level(operation: &OperationInstance) -> AgreementLevel {
    match operation_visibility(operation) {
        OperationVisibility::Immediate => AgreementLevel::None,
        OperationVisibility::Pending => AgreementLevel::Provisional,
        OperationVisibility::BlockedUntilFinalized => AgreementLevel::Finalized,
    }
}

fn finalized_agreement_level(operation: &OperationInstance) -> AgreementLevel {
    match operation_visibility(operation) {
        OperationVisibility::Immediate => AgreementLevel::None,
        OperationVisibility::Pending | OperationVisibility::BlockedUntilFinalized => {
            AgreementLevel::Finalized
        }
    }
}

fn push_unique<T: PartialEq>(items: &mut Vec<T>, item: T) {
    if !items.iter().any(|existing| existing == &item) {
        items.push(item);
    }
}

fn absorb_region_owner(region: &mut Region, owner_id: Option<&FragmentOwnerId>) {
    if region.owner_id.is_none() {
        region.owner_id = owner_id.cloned();
    }
}

fn derive_regions(
    operation_instances: &[OperationInstance],
    outstanding_effects: &[OutstandingEffect],
    authoritative_reads: &[AuthoritativeRead],
    canonical_handles: &[CanonicalHandle],
    publication_events: &BTreeMap<String, PublicationEvent>,
    progress_contracts: &[ProgressContract],
) -> Vec<Region> {
    fn region_entry(regions: &mut BTreeMap<SessionId, Region>, session: SessionId) -> &mut Region {
        regions.entry(session).or_insert_with(|| Region {
            region_id: format!("session:{session}"),
            session: Some(session),
            owner_id: None,
            scope: OwnershipScope::Session,
            operation_ids: Vec::new(),
            effect_ids: Vec::new(),
            authoritative_read_ids: Vec::new(),
            handle_ids: Vec::new(),
            publication_ids: Vec::new(),
        })
    }

    let mut regions = BTreeMap::<SessionId, Region>::new();

    for operation in operation_instances {
        let Some(session) = operation.session else {
            continue;
        };
        let region = region_entry(&mut regions, session);
        absorb_region_owner(region, operation.owner_id.as_ref());
        push_unique(&mut region.operation_ids, operation.operation_id.clone());
    }

    for effect in outstanding_effects {
        let Some(session) = effect.session else {
            continue;
        };
        let region = region_entry(&mut regions, session);
        absorb_region_owner(region, effect.owner_id.as_ref());
        push_unique(&mut region.effect_ids, effect.effect_id);
        push_unique(&mut region.operation_ids, effect.operation_id.clone());
    }

    for read in authoritative_reads {
        let Some(session) = read.session else {
            continue;
        };
        let region = region_entry(&mut regions, session);
        absorb_region_owner(region, read.owner_id.as_ref());
        push_unique(&mut region.authoritative_read_ids, read.read_id.clone());
    }

    for handle in canonical_handles {
        let Some(session) = handle.session else {
            continue;
        };
        let region = region_entry(&mut regions, session);
        absorb_region_owner(region, handle.owner_id.as_ref());
        push_unique(&mut region.handle_ids, handle.handle_id.clone());
    }

    for publication in publication_events.values() {
        let Some(session) = publication.session else {
            continue;
        };
        let region = region_entry(&mut regions, session);
        absorb_region_owner(region, publication.owner_id.as_ref());
        push_unique(
            &mut region.publication_ids,
            publication.publication_id.clone(),
        );
        push_unique(&mut region.operation_ids, publication.operation_id.clone());
    }

    for contract in progress_contracts {
        let Some(session) = contract.session else {
            continue;
        };
        let region = region_entry(&mut regions, session);
        push_unique(&mut region.operation_ids, contract.operation_id.clone());
    }

    regions.into_values().collect()
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
    out.prestate_bindings
        .sort_by(|lhs, rhs| lhs.binding_id.cmp(&rhs.binding_id));
    out.agreement_profiles
        .sort_by(|lhs, rhs| lhs.profile_name.cmp(&rhs.profile_name));
    out.agreement_contracts
        .sort_by(|lhs, rhs| lhs.contract_name.cmp(&rhs.contract_name));
    out.agreement_evidence
        .sort_by(|lhs, rhs| lhs.evidence_id.cmp(&rhs.evidence_id));
    out.agreement_states.sort_by(|lhs, rhs| {
        (
            &lhs.operation_id,
            &lhs.contract_name,
            agreement_level_rank(lhs.level),
            lhs.last_updated_tick.unwrap_or(0),
        )
            .cmp(&(
                &rhs.operation_id,
                &rhs.contract_name,
                agreement_level_rank(rhs.level),
                rhs.last_updated_tick.unwrap_or(0),
            ))
    });
    out.regions
        .sort_by(|lhs, rhs| lhs.region_id.cmp(&rhs.region_id));
    for region in &mut out.regions {
        region.operation_ids.sort();
        region.operation_ids.dedup();
        region.effect_ids.sort();
        region.effect_ids.dedup();
        region.authoritative_read_ids.sort();
        region.authoritative_read_ids.dedup();
        region.handle_ids.sort();
        region.handle_ids.dedup();
        region.publication_ids.sort();
        region.publication_ids.dedup();
    }
    out.progress_contracts
        .sort_by(|lhs, rhs| lhs.operation_id.cmp(&rhs.operation_id));
    out.progress_transitions.sort_by(|lhs, rhs| {
        (
            lhs.tick,
            &lhs.operation_id,
            progress_state_rank(lhs.from_state),
            progress_state_rank(lhs.to_state),
        )
            .cmp(&(
                rhs.tick,
                &rhs.operation_id,
                progress_state_rank(rhs.from_state),
                progress_state_rank(rhs.to_state),
            ))
    });
    out
}

/// Build the canonical semantic-object bundle from lower-level runtime
/// artifacts.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn protocol_machine_semantic_objects(
    authority_audit_log: &[AuthorityAuditRecord],
    delegation_audit_log: &[DelegationAuditRecord],
    operation_instances: &[OperationInstance],
    outstanding_effects: &[OutstandingEffect],
    output_condition_checks: &[OutputConditionCheck],
    progress_contracts: &[ProgressContract],
    progress_transitions: &[ProgressTransition],
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
            scope: semantic_ownership_scope(&record.receipt.scope),
            status: semantic_delegation_status(&record.status),
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
                transformed_fragments: transformed_fragments(&semantic_ownership_scope(
                    &record.receipt.scope,
                )),
                affected_operation_ids,
                affected_effect_ids,
                transported_effect_ids,
                invalidated_effect_ids,
                witness_policy: if matches!(
                    semantic_delegation_status(&record.status),
                    DelegationStatus::Committed
                ) {
                    "transport_pending_invalidate_blocked".to_string()
                } else {
                    "rollback".to_string()
                },
                publication_revoked_from: coro_owner_id(record.receipt.from_coro),
                publication_activated_to: coro_owner_id(record.receipt.to_coro),
                scope: semantic_ownership_scope(&record.receipt.scope),
                status: semantic_delegation_status(&record.status),
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
    canonical_handles.extend(
        semantic_handoffs
            .iter()
            .filter(|handoff| matches!(handoff.status, DelegationStatus::Committed))
            .map(|handoff| CanonicalHandle {
                handle_id: format!("handoff:{}", handoff.handoff_id),
                session: Some(handoff.session),
                owner_id: None,
                kind: CanonicalHandleKind::Handoff,
                proof_ref: Some(format!("handoff:{}", handoff.handoff_id)),
            }),
    );

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

    let mut agreement_evidence: Vec<_> = publication_events
        .values()
        .map(|event| AgreementEvidence {
            evidence_id: format!("publication:{}", event.publication_id),
            operation_id: event.operation_id.clone(),
            session: event.session,
            owner_id: event.owner_id.clone(),
            level: if event.proof_ref.is_some() && event.handle_ref.is_some() {
                AgreementLevel::Finalized
            } else {
                AgreementLevel::Provisional
            },
            kind: AgreementEvidenceKind::Publication,
            reference: event.publication_id.clone(),
            authoritative: event.owner_id.is_some()
                && event.proof_ref.is_some()
                && event.handle_ref.is_some(),
        })
        .collect();
    agreement_evidence.extend(
        materialization_proofs
            .iter()
            .map(|proof| AgreementEvidence {
                evidence_id: format!("materialization:{}", proof.proof_id),
                operation_id: format!("materialization:{}", proof.proof_id),
                session: proof.session,
                owner_id: None,
                level: if proof.passed {
                    AgreementLevel::Finalized
                } else {
                    AgreementLevel::Provisional
                },
                kind: AgreementEvidenceKind::Materialization,
                reference: proof.proof_id.clone(),
                authoritative: proof.passed,
            }),
    );

    let mut agreement_profiles_by_name = BTreeMap::<String, AgreementProfile>::new();
    let mut agreement_contracts = Vec::new();
    let mut agreement_states = Vec::new();
    let mut prestate_bindings = Vec::new();

    for operation in &operation_instances {
        let visibility = operation_visibility(operation);
        let rule = agreement_rule(operation);
        let profile_name = agreement_profile_name(operation);
        let usable_at = usable_agreement_level(operation);
        let finalized_at = finalized_agreement_level(operation);
        let required_evidence_kind = required_agreement_evidence_kind(operation);

        agreement_profiles_by_name
            .entry(profile_name.clone())
            .or_insert_with(|| AgreementProfile {
                profile_name: profile_name.clone(),
                visibility,
                rule: rule.clone(),
                usable_at,
                finalized_at,
                required_evidence_kind,
            });

        let contract_name = format!("agreement:{}", operation.operation_id);
        agreement_contracts.push(AgreementContract {
            contract_name: contract_name.clone(),
            operation_id: operation.operation_id.clone(),
            session: operation.session,
            owner_id: operation.owner_id.clone(),
            profile_name: Some(profile_name),
            visibility,
            rule,
            usable_at,
            finalized_at,
            required_evidence_kind,
        });

        prestate_bindings.push(PrestateBinding {
            binding_id: format!("prestate:{}", operation.operation_id),
            operation_id: operation.operation_id.clone(),
            session: operation.session,
            state_digest: format!(
                "{}:{:?}:{}",
                operation.kind,
                operation.phase,
                operation.terminal_publication.as_deref().unwrap_or("none")
            ),
            epoch_ref: operation.budget_ticks.map(|ticks| format!("ticks:{ticks}")),
            participant_digest: operation.owner_id.clone(),
        });

        let evidence_ids: Vec<_> = agreement_evidence
            .iter()
            .filter(|evidence| {
                evidence.operation_id == operation.operation_id
                    && evidence.session == operation.session
            })
            .map(|evidence| evidence.evidence_id.clone())
            .collect();
        let finalized = agreement_evidence.iter().any(|evidence| {
            evidence.operation_id == operation.operation_id
                && evidence.session == operation.session
                && evidence.level.at_least(finalized_at)
                && evidence.authoritative
        });
        let (level, finalization) = match operation.phase {
            OperationPhase::Pending => (AgreementLevel::None, None),
            OperationPhase::Blocked => (AgreementLevel::Provisional, None),
            OperationPhase::Succeeded => {
                if finalized {
                    (
                        AgreementLevel::Finalized,
                        Some(FinalizationOutcome::Finalized),
                    )
                } else if matches!(visibility, OperationVisibility::Immediate) {
                    (AgreementLevel::None, None)
                } else {
                    (AgreementLevel::SoftSafe, None)
                }
            }
            OperationPhase::Failed | OperationPhase::Cancelled => (
                AgreementLevel::Provisional,
                Some(FinalizationOutcome::Aborted),
            ),
            OperationPhase::TimedOut => (
                AgreementLevel::Provisional,
                Some(FinalizationOutcome::TimedOut),
            ),
            OperationPhase::HandedOff => (AgreementLevel::SoftSafe, None),
        };

        agreement_states.push(AgreementState {
            operation_id: operation.operation_id.clone(),
            session: operation.session,
            owner_id: operation.owner_id.clone(),
            contract_name,
            level,
            finalization,
            evidence_ids,
            last_updated_tick: operation.budget_ticks,
            reason: None,
        });
    }

    let agreement_profiles = agreement_profiles_by_name.into_values().collect();

    let mut progress_contracts: Vec<_> = progress_contracts.to_vec();
    for effect in &outstanding_effects {
        if progress_contracts
            .iter()
            .any(|contract| contract.operation_id == effect.operation_id)
        {
            continue;
        }
        progress_contracts.push(ProgressContract {
            operation_id: effect.operation_id.clone(),
            session: effect.session,
            state: progress_state(effect.status),
            last_ordering_key: Some(effect.ordering_key),
            bounded: true,
            budget_ticks: effect.budget_ticks,
            last_progress_tick: Some(effect.ordering_key),
            escalated_at_tick: None,
            reason: None,
        });
    }
    for handoff in &semantic_handoffs {
        let operation_id = format!("handoff:{}", handoff.handoff_id);
        if progress_contracts
            .iter()
            .any(|contract| contract.operation_id == operation_id)
        {
            continue;
        }
        progress_contracts.push(ProgressContract {
            operation_id,
            session: Some(handoff.session),
            state: ProgressState::HandedOff,
            last_ordering_key: Some(handoff.tick),
            bounded: true,
            budget_ticks: Some(1),
            last_progress_tick: Some(handoff.tick),
            escalated_at_tick: None,
            reason: handoff.reason.clone(),
        });
    }
    for operation in &operation_instances {
        if !operation.is_parity_critical()
            || progress_contracts
                .iter()
                .any(|contract| contract.tracks_operation(operation))
        {
            continue;
        }
        progress_contracts.push(ProgressContract {
            operation_id: operation.operation_id.clone(),
            session: operation.session,
            state: progress_state_for_operation_phase(operation.phase),
            last_ordering_key: None,
            bounded: operation.budget_ticks.is_some(),
            budget_ticks: operation.budget_ticks,
            last_progress_tick: None,
            escalated_at_tick: None,
            reason: None,
        });
    }

    let regions = derive_regions(
        &operation_instances,
        &outstanding_effects,
        &authoritative_reads,
        &canonical_handles,
        &publication_events,
        &progress_contracts,
    );

    canonicalize(ProtocolMachineSemanticObjects {
        schema_version: canonical_semantic_objects_schema_version(),
        operation_instances,
        outstanding_effects,
        semantic_handoffs,
        transformation_obligations,
        authoritative_reads,
        observed_reads,
        materialization_proofs,
        canonical_handles,
        publication_events: publication_events.into_values().collect(),
        prestate_bindings,
        agreement_profiles,
        agreement_contracts,
        agreement_evidence,
        agreement_states,
        regions,
        progress_contracts,
        progress_transitions: progress_transitions.to_vec(),
    })
}

#[cfg(test)]
mod semantic_object_tests {
    use super::*;

    fn agreement_semantics_fixture() -> ProtocolMachineSemanticObjects {
        let output_condition = OutputConditionCheck {
            meta: crate::output_condition::OutputConditionMeta {
                predicate_ref: "agreement.ready".to_string(),
                witness_ref: Some("accepted".to_string()),
                output_digest: "digest:ready".to_string(),
            },
            passed: true,
        };
        let operations = vec![
            operation_fixture("cancelled:op", "cancelled", OperationPhase::Cancelled)
                .with_publication("cancelled"),
            operation_fixture("timed_out:op", "timed_out", OperationPhase::TimedOut)
                .with_publication("timed_out")
                .with_budget(5),
            operation_fixture("degraded:op", "degraded", OperationPhase::Blocked)
                .with_publication("degraded")
                .with_budget(8)
                .with_dependencies(&["child:1"]),
        ];
        let progress_contracts = vec![ProgressContract {
            operation_id: "degraded:op".to_string(),
            session: Some(1),
            state: ProgressState::Degraded,
            last_ordering_key: Some(8),
            bounded: true,
            budget_ticks: Some(8),
            last_progress_tick: Some(6),
            escalated_at_tick: Some(8),
            reason: Some("timeout witness escalated".to_string()),
        }];
        let progress_transitions = vec![ProgressTransition {
            operation_id: "degraded:op".to_string(),
            session: Some(1),
            from_state: ProgressState::Blocked,
            to_state: ProgressState::Degraded,
            tick: 8,
            reason: Some("timeout witness escalated".to_string()),
        }];

        protocol_machine_semantic_objects(
            &[],
            &[],
            &operations,
            &[],
            &[output_condition],
            &progress_contracts,
            &progress_transitions,
        )
    }

    fn operation_fixture(
        operation_id: &str,
        kind: &str,
        phase: OperationPhase,
    ) -> OperationInstance {
        OperationInstance {
            operation_id: operation_id.to_string(),
            session: Some(1),
            owner_id: Some("owner/A".to_string()),
            kind: kind.to_string(),
            phase,
            handler_identity: None,
            effect_ids: Vec::new(),
            dependent_operation_ids: Vec::new(),
            terminal_publication: None,
            budget_ticks: Some(3),
            requires_proof: false,
        }
    }

    trait OperationFixtureExt {
        fn with_publication(self, publication: &str) -> Self;
        fn with_budget(self, budget_ticks: u64) -> Self;
        fn with_dependencies(self, deps: &[&str]) -> Self;
    }

    impl OperationFixtureExt for OperationInstance {
        fn with_publication(mut self, publication: &str) -> Self {
            self.terminal_publication = Some(publication.to_string());
            self
        }

        fn with_budget(mut self, budget_ticks: u64) -> Self {
            self.budget_ticks = Some(budget_ticks);
            self
        }

        fn with_dependencies(mut self, deps: &[&str]) -> Self {
            self.dependent_operation_ids = deps.iter().map(ToString::to_string).collect();
            self
        }
    }

    fn agreement_state<'a>(
        objects: &'a ProtocolMachineSemanticObjects,
        operation_id: &str,
    ) -> &'a AgreementState {
        objects
            .agreement_states
            .iter()
            .find(|state| state.operation_id == operation_id)
            .expect("agreement state")
    }

    #[test]
    fn parity_critical_operations_synthesize_progress_contracts() {
        let objects = protocol_machine_semantic_objects(
            &[],
            &[],
            &[OperationInstance {
                operation_id: "materialization:proof".to_string(),
                session: Some(1),
                owner_id: None,
                kind: "materialization".to_string(),
                phase: OperationPhase::Succeeded,
                handler_identity: None,
                effect_ids: Vec::new(),
                dependent_operation_ids: Vec::new(),
                terminal_publication: Some("materialization.succeeded".to_string()),
                budget_ticks: Some(1),
                requires_proof: true,
            }],
            &[],
            &[],
            &[],
            &[],
        );

        assert!(objects.parity_critical_operations_have_progress_contracts());
        assert!(objects
            .progress_contracts
            .iter()
            .any(|contract| contract.operation_id == "materialization:proof"
                && contract.state == ProgressState::Succeeded));
        assert_eq!(objects.regions.len(), 1);
        assert_eq!(objects.regions[0].region_id, "session:1");
    }

    #[test]
    fn synthetic_step_descends_progress_measure() {
        let contract = ProgressContract {
            operation_id: "effect:1".to_string(),
            session: Some(1),
            state: ProgressState::Blocked,
            last_ordering_key: Some(1),
            bounded: true,
            budget_ticks: Some(1),
            last_progress_tick: Some(1),
            escalated_at_tick: None,
            reason: None,
        };

        let next = contract
            .synthetic_step()
            .expect("blocked contract should take a synthetic step");
        assert_eq!(next.state, ProgressState::NoProgress);
        assert!(next.progress_measure() < contract.progress_measure());
    }

    #[test]
    fn agreement_and_progress_semantics_cover_finalized_timeout_cancelled_and_degraded_paths() {
        let objects = agreement_semantics_fixture();

        let finalized = objects
            .agreement_states
            .iter()
            .find(|state| state.operation_id.starts_with("materialization:"))
            .expect("materialization agreement state");
        assert_eq!(finalized.level, AgreementLevel::Finalized);
        assert_eq!(finalized.finalization, Some(FinalizationOutcome::Finalized));

        let cancelled = agreement_state(&objects, "cancelled:op");
        assert_eq!(cancelled.level, AgreementLevel::Provisional);
        assert_eq!(cancelled.finalization, Some(FinalizationOutcome::Aborted));

        let timed_out = agreement_state(&objects, "timed_out:op");
        assert_eq!(timed_out.level, AgreementLevel::Provisional);
        assert_eq!(timed_out.finalization, Some(FinalizationOutcome::TimedOut));

        let degraded = objects
            .progress_contracts
            .iter()
            .find(|contract| contract.operation_id == "degraded:op")
            .expect("degraded progress contract");
        assert_eq!(degraded.state, ProgressState::Degraded);
        assert_eq!(
            degraded.reason.as_deref(),
            Some("timeout witness escalated")
        );
        assert!(objects.progress_transitions.iter().any(|transition| {
            transition.operation_id == "degraded:op"
                && transition.to_state == ProgressState::Degraded
        }));
    }
}
