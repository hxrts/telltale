//! Original source-operation continuation, distinct from one child host effect.
//!
//! A declaration and its serialized outcome are observations. Only a resident
//! continuation carrying the original issued owner can advance this transaction.

use std::num::NonZeroU64;

use crate::coroutine::Value;
use crate::effect::{EffectFailure, EffectOutcome, EffectOutcomeStatus};
use crate::owned::OwnedSession;
use crate::semantic_objects::{
    AgreementProfile, OperationInstance, OperationPhase, OutstandingEffect,
    OutstandingEffectStatus, ProgressContract, ProgressState,
};
use crate::session::{OwnershipError, SessionState};

/// Exact required source child slot, checked against its installed executable call.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct DeclaredOperationChild {
    /// Instruction PC in this original role program.
    pub pc: usize,
    /// Exact typed call, including selected policy/window and continuations.
    pub call: crate::nominal_command::NominalCommandCall,
}

/// Static policy selected by a source operation, never an issued authority.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct OperationDeclaration {
    /// Exact declared operation name.
    pub name: String,
    /// Explicit role which begins the original continuation.
    pub role: String,
    /// Selected agreement contract, without profile fallback.
    pub agreement_profile: AgreementProfile,
    /// Selected progress contract name.
    pub progress_contract: String,
    /// Selected original window name.
    pub progress_window: String,
    /// Logical round budget; never physical time.
    pub budget_ticks: NonZeroU64,
    /// Whether canonical success requires actual proof-bearing finalization.
    pub requires_proof: bool,
    /// Required original source child slots; an empty admitted list cannot erase them.
    pub required_children: Vec<DeclaredOperationChild>,
}

impl OperationDeclaration {
    /// Check this static descriptor against the selected executable contract.
    /// This read-only check never issues an owner or a live continuation.
    #[must_use]
    pub fn supported(&self) -> bool {
        use crate::semantic_objects::{
            AgreementEvidenceKind, AgreementLevel, AgreementRule, OperationVisibility,
        };
        !self.name.is_empty()
            && !self.role.is_empty()
            && !self.progress_contract.is_empty()
            && !self.progress_window.is_empty()
            && self.requires_proof
            && !self.agreement_profile.profile_name.is_empty()
            && self.agreement_profile.visibility == OperationVisibility::Immediate
            && self.agreement_profile.rule == AgreementRule::NoAgreement
            && self.agreement_profile.usable_at == AgreementLevel::None
            && self.agreement_profile.finalized_at == AgreementLevel::None
            && self.agreement_profile.required_evidence_kind == AgreementEvidenceKind::Witness
    }
}

/// Typed executable operation-lifecycle action; never a generic named host call.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "operation_lifecycle", rename_all = "snake_case")]
pub enum OperationAction {
    /// Start the original operation context on this coroutine.
    Begin {
        /// Exact static operation policy and required child-call manifest.
        declaration: OperationDeclaration,
    },
    /// Await exactly the children admitted by that original operation.
    Await {
        /// Name identifying the already-issued original operation, not authorizing it.
        operation: String,
    },
    /// Propose the explicit typed application resolution.
    Resolve {
        /// Name bound to the actual resident original operation continuation.
        operation: String,
        /// Explicit application outcome to stage under the original owner/window gates.
        outcome: OperationResolution,
    },
    /// Revoke original semantic admission; this never acknowledges host teardown.
    Invalidate {
        /// Name of the resident operation whose semantic admission is revoked.
        operation: String,
    },
}

/// Register operands for an explicit application outcome.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum OperationResolution {
    /// Successful application value, distinct from genuine finalization proof.
    Success(Option<crate::instr::Reg>),
    /// Explicit application failure, distinct from original host error.
    Failure(Option<crate::instr::Reg>),
    /// Timeout branch value within the original selected logical-time contract.
    Timeout(Option<crate::instr::Reg>),
    /// Explicit cancellation branch.
    Cancelled,
}

/// An explicitly resolved application outcome, not host cleanup acknowledgment.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum OperationOutcome {
    /// An application result; this alone does not issue proof or publication.
    Success(Option<Value>),
    /// Explicit application failure; original host child failures remain separate.
    Failure(Option<Value>),
    /// The operation reached its explicitly selected timeout branch.
    Timeout(Option<Value>),
    /// The operation reached its explicit cancellation branch.
    Cancelled,
}

/// Failure of an actual operation transition, retaining typed original causes.
#[derive(Debug, thiserror::Error)]
pub enum OperationTransitionError {
    /// Original canonical host-ownership refusal.
    #[error(transparent)]
    Ownership(#[from] OwnershipError),
    /// The resident operation or its exact child/continuation contract mismatched.
    #[error("operation transition refused: {0}")]
    Contract(&'static str),
    /// An original admitted child failed; an absent record is never substituted.
    #[error("original operation child failed: {0}")]
    Child(#[source] EffectFailure),
}

/// Result of observing the original, explicitly admitted child set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperationAwait {
    /// At least one original admitted child remains live.
    Pending,
    /// Every explicitly admitted child has a successful terminal observation.
    Ready,
    /// Original semantic child failure, distinct from an application failure value.
    Failed(EffectFailure),
}

/// Nonserialized continuation retained on the original canonical coroutine.
/// It is not an additional operation registry or a host resource owner.
#[derive(Debug, Clone)]
pub(crate) struct OriginalOperationContinuation {
    pub(crate) owner: OwnedSession,
    pub(crate) declaration: OperationDeclaration,
    pub(crate) operation_id: String,
    pub(crate) issued_at: u64,
    pub(crate) original_pc: usize,
    pub(crate) children: Vec<u64>,
    pub(crate) admitted_slots: Vec<usize>,
    pub(crate) outcome: Option<OperationOutcome>,
    pub(crate) resolved: bool,
    pub(crate) completed_children: Vec<(u64, EffectOutcome)>,
    pub(crate) invalidated: bool,
    pub(crate) validation_failure: Option<std::sync::Arc<OperationTransitionError>>,
    pub(crate) execution_failure: Option<crate::coroutine::Fault>,
}

impl OriginalOperationContinuation {
    pub(crate) fn begin(
        owner: OwnedSession,
        declaration: OperationDeclaration,
        coroutine: usize,
        pc: usize,
        tick: u64,
        session: &SessionState,
    ) -> Result<(Self, OperationInstance, ProgressContract), OperationTransitionError> {
        SessionState::validate_current_owner(session, owner.capability())?;
        if owner.session_id() != session.sid
            || !declaration.supported()
            || declaration.name.is_empty()
            || declaration.role.is_empty()
            || declaration.progress_contract.is_empty()
            || declaration.progress_window.is_empty()
            || tick.checked_add(declaration.budget_ticks.get()).is_none()
        {
            return Err(OperationTransitionError::Contract(
                "invalid original declaration/window",
            ));
        }
        let id = format!("operation:{}:{coroutine}:{pc}:{tick}", session.sid);
        let record = OperationInstance {
            operation_id: id.clone(),
            session: Some(session.sid),
            owner_id: Some(owner.capability().owner_id.clone()),
            kind: declaration.name.clone(),
            phase: OperationPhase::Pending,
            handler_identity: None,
            effect_ids: Vec::new(),
            dependent_operation_ids: Vec::new(),
            terminal_publication: None,
            budget_ticks: Some(declaration.budget_ticks.get()),
            requires_proof: declaration.requires_proof,
            agreement_profile: Some(declaration.agreement_profile.clone()),
        };
        let progress = ProgressContract {
            operation_id: id.clone(),
            session: Some(session.sid),
            state: ProgressState::Pending,
            last_ordering_key: Some(tick),
            bounded: true,
            budget_ticks: Some(declaration.budget_ticks.get()),
            last_progress_tick: Some(tick),
            escalated_at_tick: None,
            reason: None,
        };
        Ok((
            Self {
                owner,
                declaration,
                operation_id: id,
                issued_at: tick,
                original_pc: pc,
                children: Vec::new(),
                admitted_slots: Vec::new(),
                outcome: None,
                resolved: false,
                completed_children: Vec::new(),
                invalidated: false,
                validation_failure: None,
                execution_failure: None,
            },
            record,
            progress,
        ))
    }

    fn validate_identity(
        &self,
        session: &SessionState,
        record: &OperationInstance,
        progress: &ProgressContract,
    ) -> Result<(), OperationTransitionError> {
        SessionState::validate_current_owner(session, self.owner.capability())?;
        if session.sid != self.owner.session_id()
            || !matches!(session.status, crate::session::SessionStatus::Active)
            || self.invalidated
            || self.resolved
            || record.operation_id != self.operation_id
            || record.session != Some(session.sid)
            || record.owner_id.as_deref() != Some(self.owner.capability().owner_id.as_str())
            || record.kind != self.declaration.name
            || record.agreement_profile.as_ref() != Some(&self.declaration.agreement_profile)
            || record.requires_proof != self.declaration.requires_proof
            || record.budget_ticks != Some(self.declaration.budget_ticks.get())
            || record.effect_ids != self.children
            || !matches!(
                record.phase,
                OperationPhase::Pending | OperationPhase::Blocked
            )
            || progress.operation_id != self.operation_id
            || progress.session != Some(session.sid)
            || progress.budget_ticks != Some(self.declaration.budget_ticks.get())
            || progress.last_ordering_key != Some(self.issued_at)
        {
            return Err(OperationTransitionError::Contract(
                "original continuation, policy or window mismatch",
            ));
        }
        Ok(())
    }

    pub(crate) fn validate(
        &self,
        session: &SessionState,
        record: &OperationInstance,
        progress: &ProgressContract,
        tick: u64,
    ) -> Result<(), OperationTransitionError> {
        self.validate_identity(session, record, progress)?;
        if self.validation_failure.is_some()
            || self
                .issued_at
                .checked_add(self.declaration.budget_ticks.get())
                .is_none_or(|end| tick > end)
        {
            return Err(OperationTransitionError::Contract(
                "original operation window expired or validation was refused",
            ));
        }
        Ok(())
    }

    pub(crate) fn admit_child(
        &mut self,
        child: &OutstandingEffect,
        record: &mut OperationInstance,
        pc: usize,
        call: &crate::nominal_command::NominalCommandCall,
    ) -> Result<(), OperationTransitionError> {
        if self.invalidated
            || self.resolved
            || record.operation_id != self.operation_id
            || record.effect_ids != self.children
            || self.children.contains(&child.effect_id)
            || self.admitted_slots.contains(&pc)
            || self
                .declaration
                .required_children
                .iter()
                .filter(|slot| slot.pc == pc && slot.call == *call)
                .count()
                != 1
            || child.session != Some(self.owner.session_id())
            || child.owner_id.as_deref() != Some(self.owner.capability().owner_id.as_str())
            || !matches!(
                child.status,
                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
            )
        {
            return Err(OperationTransitionError::Contract(
                "child admission is not the original live occurrence",
            ));
        }
        self.children.push(child.effect_id);
        self.admitted_slots.push(pc);
        record.effect_ids.push(child.effect_id);
        record
            .dependent_operation_ids
            .push(child.operation_id.clone());
        Ok(())
    }

    pub(crate) fn observe_children(
        &self,
        effects: &[OutstandingEffect],
    ) -> Result<OperationAwait, OperationTransitionError> {
        if self.admitted_slots.len() != self.declaration.required_children.len()
            || self
                .declaration
                .required_children
                .iter()
                .any(|slot| !self.admitted_slots.contains(&slot.pc))
        {
            return Err(OperationTransitionError::Contract(
                "required original source child was never admitted",
            ));
        }
        let mut pending = false;
        let mut original_failure = None;
        for id in &self.children {
            let mut matches = effects.iter().filter(|effect| effect.effect_id == *id);
            let child = matches.next().ok_or(OperationTransitionError::Contract(
                "original admitted child is missing",
            ))?;
            if matches.next().is_some()
                || child.session != Some(self.owner.session_id())
                || child.owner_id.as_deref() != Some(self.owner.capability().owner_id.as_str())
            {
                return Err(OperationTransitionError::Contract(
                    "original admitted child is ambiguous or revoked",
                ));
            }
            let mut child_has_failure = false;
            if let Some((_, outcome)) = self
                .completed_children
                .iter()
                .find(|(actual, _)| actual == id)
            {
                if child.status == OutstandingEffectStatus::Succeeded
                    && !matches!(outcome.status, EffectOutcomeStatus::Success)
                {
                    return Err(OperationTransitionError::Contract(
                        "successful child record has no successful original outcome",
                    ));
                }
                if let EffectOutcomeStatus::Failure { failure } = &outcome.status {
                    child_has_failure = true;
                    if original_failure.is_none() {
                        original_failure = Some(failure.clone());
                    }
                }
            } else if matches!(
                child.status,
                OutstandingEffectStatus::Succeeded | OutstandingEffectStatus::Failed
            ) {
                return Err(OperationTransitionError::Contract(
                    "original terminal child outcome is missing",
                ));
            }
            match child.status {
                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked => {
                    pending = true
                }
                OutstandingEffectStatus::Succeeded => {}
                OutstandingEffectStatus::Failed
                | OutstandingEffectStatus::Cancelled
                | OutstandingEffectStatus::Invalidated => {
                    if !child_has_failure {
                        return Err(OperationTransitionError::Contract(
                            "original unsuccessful child has no retained failure outcome",
                        ));
                    }
                }
            }
        }
        Ok(if pending {
            OperationAwait::Pending
        } else if let Some(failure) = original_failure {
            OperationAwait::Failed(failure)
        } else {
            OperationAwait::Ready
        })
    }

    pub(crate) fn retain_child_outcome(
        &mut self,
        id: u64,
        outcome: EffectOutcome,
    ) -> Result<(), OperationTransitionError> {
        if !self.children.contains(&id)
            || self
                .completed_children
                .iter()
                .any(|(actual, _)| *actual == id)
            || matches!(outcome.status, EffectOutcomeStatus::Blocked)
        {
            return Err(OperationTransitionError::Contract(
                "unknown, duplicate or nonterminal child completion",
            ));
        }
        self.completed_children.push((id, outcome));
        Ok(())
    }

    pub(crate) fn stage_resolution(
        &mut self,
        outcome: OperationOutcome,
    ) -> Result<(), OperationTransitionError> {
        if self.invalidated || self.resolved || self.outcome.is_some() {
            return Err(OperationTransitionError::Contract(
                "duplicate or revoked resolution",
            ));
        }
        self.outcome = Some(outcome);
        Ok(())
    }

    pub(crate) fn commit_resolution(
        &mut self,
        session: &SessionState,
        record: &mut OperationInstance,
        progress: &mut ProgressContract,
        effects: &[OutstandingEffect],
        tick: u64,
    ) -> Result<(), OperationTransitionError> {
        self.validate(session, record, progress, tick)?;
        let children = self.observe_children(effects)?;
        if children == OperationAwait::Pending {
            return Err(OperationTransitionError::Contract(
                "original admitted children remain pending",
            ));
        }
        let outcome = self
            .outcome
            .as_ref()
            .ok_or(OperationTransitionError::Contract(
                "no actual original resolution",
            ))?;
        if matches!(outcome, OperationOutcome::Success(_)) {
            if let OperationAwait::Failed(failure) = children {
                return Err(OperationTransitionError::Child(failure));
            }
        }
        let (phase, state) = match outcome {
            OperationOutcome::Success(_) => (OperationPhase::Succeeded, ProgressState::Succeeded),
            OperationOutcome::Failure(_) => (OperationPhase::Failed, ProgressState::Failed),
            OperationOutcome::Timeout(_) => (OperationPhase::TimedOut, ProgressState::TimedOut),
            OperationOutcome::Cancelled => (OperationPhase::Cancelled, ProgressState::Cancelled),
        };
        // This is application execution status only. Proof policy stays intact;
        // no publication, materialization or canonical handle is issued here.
        record.phase = phase;
        progress.state = state;
        progress.last_progress_tick = Some(tick);
        self.resolved = true;
        Ok(())
    }

    pub(crate) fn invalidate(
        &mut self,
        session: &SessionState,
        record: &mut OperationInstance,
        progress: &mut ProgressContract,
        effects: &mut [OutstandingEffect],
        tick: u64,
    ) -> Result<(), OperationTransitionError> {
        self.validate_identity(session, record, progress)?;
        // Validate the whole admitted set before changing any canonical child.
        for id in &self.children {
            let count = effects
                .iter()
                .filter(|effect| {
                    effect.effect_id == *id
                        && effect.session == Some(self.owner.session_id())
                        && effect.owner_id.as_deref()
                            == Some(self.owner.capability().owner_id.as_str())
                })
                .count();
            if count != 1 {
                return Err(OperationTransitionError::Contract(
                    "missing or ambiguous original child during invalidation",
                ));
            }
        }
        for effect in effects
            .iter_mut()
            .filter(|effect| self.children.contains(&effect.effect_id))
        {
            if matches!(
                effect.status,
                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
            ) {
                effect.status = OutstandingEffectStatus::Invalidated;
                effect.completed_at_tick = Some(tick);
            }
        }
        record.phase = OperationPhase::Failed;
        progress.state = ProgressState::Failed;
        progress.reason = Some("explicit original operation invalidation".into());
        self.invalidated = true;
        Ok(())
    }
}

pub(crate) enum OperationExecution {
    Advance,
    AwaitPending,
    Begun(OperationInstance, ProgressContract),
}

fn begin_source_operation(
    coroutine: &mut crate::coroutine::Coroutine,
    session: &SessionState,
    records: &[OperationInstance],
    progress: &[ProgressContract],
    tick: u64,
    declaration: OperationDeclaration,
) -> Result<OperationExecution, OperationTransitionError> {
    if coroutine
        .operation_continuation
        .as_ref()
        .is_some_and(|original| !original.resolved && !original.invalidated)
        || coroutine.role != declaration.role
        || coroutine.session_id != session.sid
        || !coroutine.owned_endpoints.contains(&crate::instr::Endpoint {
            sid: session.sid,
            role: coroutine.role.clone(),
        })
        || !matches!(session.status, crate::session::SessionStatus::Active)
    {
        return Err(OperationTransitionError::Contract(
            "operation begin has no original exclusive role context",
        ));
    }
    let owner = coroutine
        .nominal_owner
        .clone()
        .ok_or(OperationTransitionError::Contract(
            "begin requires the original issued owner",
        ))?;
    if !matches!(
        owner.capability().scope,
        crate::session::OwnershipScope::Session
    ) {
        return Err(OperationTransitionError::Contract(
            "session operation requires actual session scope",
        ));
    }
    let (original, record, contract) = OriginalOperationContinuation::begin(
        owner,
        declaration,
        coroutine.id,
        coroutine.pc,
        tick,
        session,
    )?;
    if records
        .iter()
        .any(|current| current.operation_id == record.operation_id)
        || progress
            .iter()
            .any(|current| current.operation_id == record.operation_id)
    {
        return Err(OperationTransitionError::Contract(
            "duplicate original operation occurrence",
        ));
    }
    coroutine.operation_continuation = Some(original);
    Ok(OperationExecution::Begun(record, contract))
}

fn read_operation_resolution(
    coroutine: &crate::coroutine::Coroutine,
    outcome: &OperationResolution,
) -> Result<OperationOutcome, OperationTransitionError> {
    let read =
        |reg: &Option<crate::instr::Reg>| -> Result<Option<Value>, OperationTransitionError> {
            reg.map(|reg| {
                coroutine.regs.get(usize::from(reg)).cloned().ok_or(
                    OperationTransitionError::Contract("resolution register is absent"),
                )
            })
            .transpose()
        };
    let value = match outcome {
        OperationResolution::Success(reg) => OperationOutcome::Success(read(reg)?),
        OperationResolution::Failure(reg) => OperationOutcome::Failure(read(reg)?),
        OperationResolution::Timeout(_) => {
            return Err(OperationTransitionError::Contract(
                "timeout resolution requires actual original escalation lowering",
            ));
        }
        OperationResolution::Cancelled => OperationOutcome::Cancelled,
    };
    Ok(value)
}

/// Execute against the actual canonical records selected by the runtime adapter.
/// The caller publishes returned Begin records in its existing canonical fields.
pub(crate) fn execute_operation_action(
    coroutine: &mut crate::coroutine::Coroutine,
    session: &SessionState,
    records: &mut [OperationInstance],
    progress: &mut [ProgressContract],
    effects: &mut [OutstandingEffect],
    tick: u64,
    action: OperationAction,
) -> Result<OperationExecution, OperationTransitionError> {
    if let OperationAction::Begin { declaration } = action {
        return begin_source_operation(coroutine, session, records, progress, tick, declaration);
    }
    let (name, resolution) = match &action {
        OperationAction::Await { operation } | OperationAction::Invalidate { operation } => {
            (operation, None)
        }
        OperationAction::Resolve { operation, outcome } => {
            let value = read_operation_resolution(coroutine, outcome)?;
            (operation, Some(value))
        }
        OperationAction::Begin { .. } => unreachable!("begin handled above"),
    };
    let original =
        coroutine
            .operation_continuation
            .as_mut()
            .ok_or(OperationTransitionError::Contract(
                "no original begun operation continuation",
            ))?;
    if original.declaration.name != *name {
        return Err(OperationTransitionError::Contract(
            "operation name does not identify the original begun continuation",
        ));
    }
    if records
        .iter()
        .filter(|record| record.operation_id == original.operation_id)
        .count()
        != 1
        || progress
            .iter()
            .filter(|record| record.operation_id == original.operation_id)
            .count()
            != 1
    {
        return Err(OperationTransitionError::Contract(
            "original operation/progress record is missing or ambiguous",
        ));
    }
    let record = records
        .iter_mut()
        .find(|record| record.operation_id == original.operation_id)
        .ok_or(OperationTransitionError::Contract(
            "original operation record is missing",
        ))?;
    let contract = progress
        .iter_mut()
        .find(|record| record.operation_id == original.operation_id)
        .ok_or(OperationTransitionError::Contract(
            "original progress record is missing",
        ))?;
    if matches!(action, OperationAction::Invalidate { .. }) {
        original.validate_identity(session, record, contract)?;
    } else {
        original.validate(session, record, contract, tick)?;
    }
    match action {
        OperationAction::Await { .. } => match original.observe_children(effects)? {
            OperationAwait::Pending => {
                record.phase = OperationPhase::Blocked;
                contract.state = ProgressState::Blocked;
                Ok(OperationExecution::AwaitPending)
            }
            OperationAwait::Ready => Ok(OperationExecution::Advance),
            OperationAwait::Failed(failure) => Err(OperationTransitionError::Child(failure)),
        },
        OperationAction::Resolve { .. } => {
            let resolution = resolution.ok_or(OperationTransitionError::Contract(
                "missing proposed resolution",
            ))?;
            if let Some(actual) = &original.outcome {
                if actual != &resolution {
                    return Err(OperationTransitionError::Contract(
                        "cannot replace the original retained proposed result",
                    ));
                }
            } else {
                original.stage_resolution(resolution)?;
            }
            original.commit_resolution(session, record, contract, effects, tick)?;
            Ok(OperationExecution::Advance)
        }
        OperationAction::Invalidate { .. } => {
            original.invalidate(session, record, contract, effects, tick)?;
            Ok(OperationExecution::Advance)
        }
        OperationAction::Begin { .. } => unreachable!("begin handled above"),
    }
}

pub(crate) fn transition_fault(error: OperationTransitionError) -> crate::coroutine::Fault {
    match error {
        OperationTransitionError::Ownership(error) => {
            crate::coroutine::Fault::OperationOwnership { error }
        }
        OperationTransitionError::Child(failure) => crate::coroutine::Fault::Invoke { failure },
        OperationTransitionError::Contract(reason) => crate::coroutine::Fault::Invoke {
            failure: EffectFailure::contract_violation(reason),
        },
    }
}

/// The existing scheduler's unblock phase observes canonical state only; it does
/// not poll or reissue a host callback, nor advance the retained original PC.
pub(crate) fn await_should_wake(
    original: Option<&OriginalOperationContinuation>,
    operation_id: &str,
    effects: &[OutstandingEffect],
    tick: u64,
) -> bool {
    let Some(original) = original else {
        return true;
    };
    if original.operation_id != operation_id
        || original.invalidated
        || original.resolved
        || original
            .issued_at
            .checked_add(original.declaration.budget_ticks.get())
            .is_none_or(|end| tick > end)
    {
        return true;
    }
    !matches!(
        original.observe_children(effects),
        Ok(OperationAwait::Pending)
    )
}

pub(crate) fn validate_enclosing_operation(
    coroutine: &crate::coroutine::Coroutine,
    session: &SessionState,
    records: &[OperationInstance],
    progress: &[ProgressContract],
    tick: u64,
) -> Result<(), OperationTransitionError> {
    let Some(original) = coroutine.operation_continuation.as_ref() else {
        return Ok(());
    };
    if original.resolved {
        return Ok(());
    }
    if original.declaration.role != coroutine.role
        || coroutine.session_id != original.owner.session_id()
        || !coroutine.owned_endpoints.contains(&crate::instr::Endpoint {
            sid: coroutine.session_id,
            role: coroutine.role.clone(),
        })
    {
        return Err(OperationTransitionError::Contract(
            "original source role/endpoint placement changed",
        ));
    }
    let record = records
        .iter()
        .find(|record| record.operation_id == original.operation_id)
        .ok_or(OperationTransitionError::Contract(
            "original enclosing operation record is missing",
        ))?;
    let contract = progress
        .iter()
        .find(|record| record.operation_id == original.operation_id)
        .ok_or(OperationTransitionError::Contract(
            "original enclosing progress record is missing",
        ))?;
    if records
        .iter()
        .filter(|record| record.operation_id == original.operation_id)
        .count()
        != 1
        || progress
            .iter()
            .filter(|record| record.operation_id == original.operation_id)
            .count()
            != 1
    {
        return Err(OperationTransitionError::Contract(
            "original enclosing operation is ambiguous",
        ));
    }
    original.validate(session, record, contract, tick)
}

pub(crate) fn admit_source_child(
    coroutine: &mut crate::coroutine::Coroutine,
    records: &mut [OperationInstance],
    child: &OutstandingEffect,
    call: &crate::nominal_command::NominalCommandCall,
) -> Result<(), OperationTransitionError> {
    let Some(original) = coroutine.operation_continuation.as_mut() else {
        return Ok(());
    };
    if original.resolved {
        return Ok(());
    }
    let record = records
        .iter_mut()
        .find(|record| record.operation_id == original.operation_id)
        .ok_or(OperationTransitionError::Contract(
            "original source operation record disappeared",
        ))?;
    original.admit_child(child, record, coroutine.pc, call)
}

pub(crate) fn retain_source_child_outcome(
    coroutine: &mut crate::coroutine::Coroutine,
    id: u64,
    outcome: &EffectOutcome,
) {
    let Some(original) = coroutine.operation_continuation.as_mut() else {
        return;
    };
    if !original.children.contains(&id) || matches!(outcome.status, EffectOutcomeStatus::Blocked) {
        return;
    }
    if let Err(error) = original.retain_child_outcome(id, outcome.clone()) {
        original
            .validation_failure
            .get_or_insert_with(|| std::sync::Arc::new(error));
    }
}

pub(crate) fn requires_operation_context(program: &[crate::instr::Instr], pc: usize) -> bool {
    let Some(crate::instr::Instr::Invoke {
        action: crate::instr::InvokeAction::NominalCommand(call),
    }) = program.get(pc)
    else {
        return false;
    };
    program.iter().take(pc).any(|instruction| matches!(instruction,
        crate::instr::Instr::Invoke { action: crate::instr::InvokeAction::OperationLifecycle(action) }
        if matches!(action.as_ref(), OperationAction::Begin { declaration } if declaration.name == call.enclosing_operation)))
}

pub(crate) fn fail_active_operation(
    coroutine: &mut crate::coroutine::Coroutine,
    records: &mut [OperationInstance],
    progress: &mut [ProgressContract],
    effects: &mut [OutstandingEffect],
    fault: &crate::coroutine::Fault,
    tick: u64,
) {
    let Some(original) = coroutine.operation_continuation.as_mut() else {
        return;
    };
    if original.resolved || original.invalidated {
        return;
    }
    original
        .execution_failure
        .get_or_insert_with(|| fault.clone());
    original.invalidated = true;
    if let Some(record) = records
        .iter_mut()
        .find(|record| record.operation_id == original.operation_id)
    {
        if matches!(
            record.phase,
            OperationPhase::Pending | OperationPhase::Blocked
        ) {
            record.phase = OperationPhase::Failed;
        }
    }
    if let Some(contract) = progress
        .iter_mut()
        .find(|record| record.operation_id == original.operation_id)
    {
        if !contract.state.is_terminal() {
            contract.state = ProgressState::Failed;
        }
        contract.reason = Some("original source operation execution failed".into());
    }
    for effect in effects
        .iter_mut()
        .filter(|effect| original.children.contains(&effect.effect_id))
    {
        if matches!(
            effect.status,
            OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
        ) {
            effect.status = OutstandingEffectStatus::Invalidated;
            effect.completed_at_tick = Some(tick);
        }
    }
}

/// Readonly observation of the actual resident source operation. It deliberately
/// contains no issued session owner and has no deserialization/restore API.
#[derive(Debug, Clone, PartialEq, serde::Serialize)]
pub struct OperationContinuationView {
    /// Exact canonical operation occurrence.
    pub operation_id: String,
    /// Original owner observation; this cannot recreate the actual opaque owner.
    pub owner: crate::session::OwnershipCapability,
    /// Original selected declaration and policy.
    pub declaration: OperationDeclaration,
    /// Original beginning instruction, not an authorization token.
    pub original_pc: usize,
    /// Original logical issuance tick.
    pub issued_at: u64,
    /// Exact admitted source child occurrences.
    pub children: Vec<u64>,
    /// Exact installed source slots admitted by the original producer.
    pub admitted_slots: Vec<usize>,
    /// Actual terminal child outcomes retained independently of diagnostics.
    pub completed_children: Vec<(u64, EffectOutcome)>,
    /// Proposed original application resolution, retained before final gates.
    pub outcome: Option<OperationOutcome>,
    /// Whether the original explicit resolution committed.
    pub resolved: bool,
    /// Whether original semantic continuation admission has been revoked.
    pub invalidated: bool,
    /// Actual original execution fault, never a cleanup acknowledgment.
    pub execution_failure: Option<crate::coroutine::Fault>,
}

impl crate::coroutine::Coroutine {
    /// Observe the actual original operation without issuing or restoring its owner.
    #[must_use]
    pub fn operation_continuation_view(&self) -> Option<OperationContinuationView> {
        self.operation_continuation
            .as_ref()
            .map(|original| OperationContinuationView {
                operation_id: original.operation_id.clone(),
                owner: original.owner.capability().clone(),
                declaration: original.declaration.clone(),
                original_pc: original.original_pc,
                issued_at: original.issued_at,
                children: original.children.clone(),
                admitted_slots: original.admitted_slots.clone(),
                completed_children: original.completed_children.clone(),
                outcome: original.outcome.clone(),
                resolved: original.resolved,
                invalidated: original.invalidated,
                execution_failure: original.execution_failure.clone(),
            })
    }

    /// Borrow the same retained transition refusal through a resource-free shared
    /// diagnostic owner. This cannot construct the private continuation.
    #[must_use]
    pub fn operation_transition_failure(&self) -> Option<std::sync::Arc<OperationTransitionError>> {
        self.operation_continuation
            .as_ref()
            .and_then(|original| original.validation_failure.clone())
    }
}

/// A terminal instruction cannot abandon a live original operation. Explicit
/// semantic invalidation is a terminal branch, not physical host cleanup.
pub(crate) fn require_operation_terminal(
    coroutine: &crate::coroutine::Coroutine,
) -> Result<(), crate::coroutine::Fault> {
    if coroutine
        .operation_continuation
        .as_ref()
        .is_some_and(|original| !original.resolved && !original.invalidated)
    {
        return Err(crate::coroutine::Fault::Invoke {
            failure: EffectFailure::contract_violation(
                "source operation reached halt without original resolution or invalidation",
            ),
        });
    }
    Ok(())
}
