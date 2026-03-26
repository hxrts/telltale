impl ProtocolMachine {
    fn coro_owner_id(coro_id: usize) -> FragmentOwnerId {
        format!("coro:{coro_id}")
    }

    fn ensure_effect_request_allowed(&self, request: &EffectRequest) -> Result<(), EffectFailure> {
        request.metadata.validate()?;
        let incoming = crate::effect::EffectResponsibilityDomain {
            footprint_key: request
                .session
                .map(|session| format!("session:{session}"))
                .unwrap_or_else(|| request.metadata.interface_name.clone()),
            operation_id: request.operation_id.clone(),
            fragment_id: request.session.map(|session| format!("session:{session}")),
            owner_id: None,
        };
        for effect in self.outstanding_effects.as_slice().iter().filter(|effect| {
            matches!(
                effect.status,
                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
            )
        }) {
            let active = crate::effect::EffectResponsibilityDomain {
                footprint_key: effect
                    .session
                    .map(|session| format!("session:{session}"))
                    .unwrap_or_else(|| effect.handler_identity.clone()),
                operation_id: Some(effect.operation_id.clone()),
                fragment_id: effect.session.map(|session| format!("session:{session}")),
                owner_id: effect.owner_id.clone(),
            };
            if !request.metadata.reentrancy_admissible(&active, &incoming) {
                return Err(EffectFailure::contract_violation(format!(
                    "reentrancy rejected for effect {} on footprint {}",
                    effect.effect_id, active.footprint_key
                )));
            }
        }
        Ok(())
    }

    fn record_effect_exchange(
        &mut self,
        request: &EffectRequest,
        outcome: &EffectOutcome,
        handler_identity: &str,
        effect_id: u64,
    ) {
        let mut request = request.clone();
        request.effect_id = Some(effect_id);
        self.effect_exchanges.push(
            EffectExchangeRecord {
                effect_id,
                handler_identity: handler_identity.to_string(),
                ordering_key: self.clock.tick,
                request,
                outcome: outcome.clone(),
            },
            &self.config.observability_retention,
        );
    }

    fn current_operation_owner(&self, session: Option<SessionId>) -> Option<FragmentOwnerId> {
        session.and_then(|sid| {
            self.sessions
                .current_ownership(sid)
                .map(|capability| capability.owner_id.clone())
        })
    }

    fn effect_operation_id(effect_id: u64) -> String {
        format!("effect:{effect_id}")
    }

    fn effect_invalidation_token(effect_id: u64) -> String {
        format!("effect:{effect_id}:live")
    }

    fn effect_status_phase(status: OutstandingEffectStatus) -> OperationPhase {
        match status {
            OutstandingEffectStatus::Pending => OperationPhase::Pending,
            OutstandingEffectStatus::Blocked => OperationPhase::Blocked,
            OutstandingEffectStatus::Succeeded => OperationPhase::Succeeded,
            OutstandingEffectStatus::Failed => OperationPhase::Failed,
            OutstandingEffectStatus::Cancelled => OperationPhase::Cancelled,
            OutstandingEffectStatus::Invalidated => OperationPhase::Failed,
        }
    }

    fn effect_terminal_publication(status: OutstandingEffectStatus) -> Option<String> {
        match status {
            OutstandingEffectStatus::Pending => None,
            OutstandingEffectStatus::Blocked => Some("effect.blocked".to_string()),
            OutstandingEffectStatus::Succeeded => Some("effect.succeeded".to_string()),
            OutstandingEffectStatus::Failed => Some("effect.failed".to_string()),
            OutstandingEffectStatus::Cancelled => Some("effect.cancelled".to_string()),
            OutstandingEffectStatus::Invalidated => Some("effect.invalidated".to_string()),
        }
    }

    fn progress_state_for_effect_status(status: OutstandingEffectStatus) -> ProgressState {
        match status {
            OutstandingEffectStatus::Pending => ProgressState::Pending,
            OutstandingEffectStatus::Blocked => ProgressState::Blocked,
            OutstandingEffectStatus::Succeeded => ProgressState::Succeeded,
            OutstandingEffectStatus::Failed => ProgressState::Failed,
            OutstandingEffectStatus::Cancelled => ProgressState::Cancelled,
            OutstandingEffectStatus::Invalidated => ProgressState::TimedOut,
        }
    }

    fn set_progress_contract_state(
        &mut self,
        operation_id: &str,
        session: Option<SessionId>,
        state: ProgressState,
        budget_ticks: Option<u64>,
        reason: Option<String>,
        refresh_progress_tick: bool,
    ) {
        let ordering_key = Some(self.clock.tick);
        let retention = &self.config.observability_retention;
        if let Some(contract) = self
            .progress_contracts
            .as_mut_slice()
            .iter_mut()
            .find(|contract| contract.operation_id == operation_id)
        {
            let previous = contract.state;
            contract.session = session.or(contract.session);
            contract.last_ordering_key = ordering_key;
            contract.bounded = budget_ticks.is_some();
            contract.budget_ticks = budget_ticks;
            if refresh_progress_tick || contract.last_progress_tick.is_none() {
                contract.last_progress_tick = ordering_key;
            }
            if previous != state
                && matches!(
                    state,
                    ProgressState::Blocked
                        | ProgressState::NoProgress
                        | ProgressState::Degraded
                        | ProgressState::TimedOut
                )
            {
                contract.escalated_at_tick = ordering_key;
            }
            contract.reason = reason.clone();
            contract.state = state;
            if previous != state {
                self.progress_transitions.push(
                    ProgressTransition {
                        operation_id: operation_id.to_string(),
                        session,
                        from_state: previous,
                        to_state: state,
                        tick: self.clock.tick,
                        reason,
                    },
                    retention,
                );
            }
            return;
        }

        self.progress_contracts.push(
            ProgressContract {
                operation_id: operation_id.to_string(),
                session,
                state,
                last_ordering_key: ordering_key,
                bounded: budget_ticks.is_some(),
                budget_ticks,
                last_progress_tick: ordering_key,
                escalated_at_tick: matches!(
                    state,
                    ProgressState::Blocked
                        | ProgressState::NoProgress
                        | ProgressState::Degraded
                        | ProgressState::TimedOut
                )
                .then_some(self.clock.tick),
                reason,
            },
            retention,
        );
    }

    #[allow(clippy::too_many_lines)]
    fn evaluate_progress_contracts(&mut self) -> Result<(), ProtocolMachineError> {
        let active_effect_ids: Vec<_> = self
            .outstanding_effects
            .as_slice()
            .iter()
            .filter(|effect| {
                matches!(
                    effect.status,
                    OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
                )
            })
            .map(|effect| effect.effect_id)
            .collect();

        for effect_id in active_effect_ids {
            let Some(effect_index) = self
                .outstanding_effects
                .as_slice()
                .iter()
                .position(|effect| effect.effect_id == effect_id)
            else {
                continue;
            };
            let effect = self.outstanding_effects.as_slice()[effect_index].clone();
            let budget = effect.budget_ticks.ok_or_else(|| {
                ProtocolMachineError::HandlerError(EffectFailure::contract_violation(format!(
                    "[host-contract] semantic-path effect {} requires a bounded wait budget",
                    effect.effect_id
                )))
            })?;
            let Some(contract) = self
                .progress_contracts
                .as_slice()
                .iter()
                .find(|contract| contract.operation_id == effect.operation_id)
            else {
                return Err(ProtocolMachineError::HandlerError(
                    EffectFailure::contract_violation(format!(
                        "[host-contract] outstanding effect {} requires a live progress contract",
                        effect.effect_id
                    )),
                ));
            };
            let since = contract
                .escalated_at_tick
                .or(contract.last_progress_tick)
                .unwrap_or(effect.ordering_key);
            let elapsed = self.clock.tick.saturating_sub(since);
            let target_state = match contract.state {
                ProgressState::Pending if elapsed < budget => ProgressState::Pending,
                ProgressState::Pending => ProgressState::Blocked,
                ProgressState::Blocked if elapsed < budget => ProgressState::Blocked,
                ProgressState::Blocked => ProgressState::NoProgress,
                ProgressState::NoProgress if elapsed < budget => ProgressState::NoProgress,
                ProgressState::NoProgress => ProgressState::Degraded,
                ProgressState::Degraded if elapsed < budget => ProgressState::Degraded,
                ProgressState::Degraded => ProgressState::TimedOut,
                ProgressState::Succeeded
                | ProgressState::Failed
                | ProgressState::Cancelled
                | ProgressState::TimedOut
                | ProgressState::HandedOff => continue,
            };

            let reason = match target_state {
                ProgressState::Pending => None,
                ProgressState::Blocked => {
                    Some("waiting on bounded semantic-path effect".to_string())
                }
                ProgressState::NoProgress => {
                    Some("no progress observed within bounded wait budget".to_string())
                }
                ProgressState::Degraded => {
                    Some("bounded wait degraded after repeated no-progress windows".to_string())
                }
                ProgressState::TimedOut => {
                    Some("bounded wait exhausted; late results are invalid".to_string())
                }
                ProgressState::Succeeded
                | ProgressState::Failed
                | ProgressState::Cancelled
                | ProgressState::HandedOff => None,
            };

            if matches!(target_state, ProgressState::Blocked)
                && effect.status == OutstandingEffectStatus::Pending
            {
                if let Some(effect_mut) = self
                    .outstanding_effects
                    .as_mut_slice()
                    .iter_mut()
                    .find(|effect_mut| effect_mut.effect_id == effect_id)
                {
                    effect_mut.status = OutstandingEffectStatus::Blocked;
                    effect_mut.outputs = json!({
                        "status": "blocked",
                        "reason": reason.clone().unwrap_or_default(),
                    });
                    effect_mut.ordering_key = self.clock.tick;
                }
                if let Some(operation) = self
                    .operation_instances
                    .as_mut_slice()
                    .iter_mut()
                    .find(|operation| operation.operation_id == effect.operation_id)
                {
                    operation.phase = OperationPhase::Blocked;
                    operation.terminal_publication = Some("effect.blocked".to_string());
                }
            }

            if matches!(
                target_state,
                ProgressState::NoProgress | ProgressState::Degraded
            ) {
                if let Some(operation) = self
                    .operation_instances
                    .as_mut_slice()
                    .iter_mut()
                    .find(|operation| operation.operation_id == effect.operation_id)
                {
                    operation.phase = OperationPhase::Blocked;
                    operation.terminal_publication = Some(match target_state {
                        ProgressState::NoProgress => "effect.no_progress".to_string(),
                        ProgressState::Degraded => "effect.degraded".to_string(),
                        _ => unreachable!(),
                    });
                }
            }

            if target_state == ProgressState::TimedOut {
                if let Some(effect_mut) = self
                    .outstanding_effects
                    .as_mut_slice()
                    .iter_mut()
                    .find(|effect_mut| effect_mut.effect_id == effect_id)
                {
                    effect_mut.status = OutstandingEffectStatus::Invalidated;
                    effect_mut.outputs = json!({
                        "status": "invalidated",
                        "reason": reason.clone().unwrap_or_default(),
                    });
                    effect_mut.completed_at_tick = Some(self.clock.tick);
                    effect_mut.ordering_key = self.clock.tick;
                }
                if let Some(operation) = self
                    .operation_instances
                    .as_mut_slice()
                    .iter_mut()
                    .find(|operation| operation.operation_id == effect.operation_id)
                {
                    operation.phase = OperationPhase::TimedOut;
                    operation.terminal_publication = Some("effect.timed_out".to_string());
                }
            }

            self.set_progress_contract_state(
                &effect.operation_id,
                effect.session,
                target_state,
                Some(budget),
                reason,
                false,
            );
        }

        Ok(())
    }

    fn issue_runtime_effect(
        &mut self,
        effect_kind: &str,
        session: Option<SessionId>,
        handler_identity: &str,
        inputs: serde_json::Value,
    ) -> u64 {
        let effect_id = self.next_effect_id;
        self.next_effect_id = self.next_effect_id.saturating_add(1);
        let operation_id = Self::effect_operation_id(effect_id);
        let (effect_interface, effect_operation) =
            infer_effect_interface_and_operation(effect_kind);
        let owner_id = self.current_operation_owner(session);
        let budget_ticks = Some(1);

        self.outstanding_effects.push(
            OutstandingEffect {
                effect_id,
                operation_id: operation_id.clone(),
                session,
                owner_id: owner_id.clone(),
                effect_interface: effect_interface.clone(),
                effect_operation: effect_operation.clone(),
                effect_kind: effect_kind.to_string(),
                handler_identity: handler_identity.to_string(),
                status: OutstandingEffectStatus::Pending,
                ordering_key: self.clock.tick,
                budget_ticks,
                retry_policy: "forbid_late_results".to_string(),
                invalidation_token: Self::effect_invalidation_token(effect_id),
                completed_at_tick: None,
                inputs,
                outputs: json!({ "status": "pending" }),
            },
            &self.config.observability_retention,
        );
        self.operation_instances.push(
            OperationInstance {
                operation_id: operation_id.clone(),
                session,
                owner_id,
                kind: effect_operation.unwrap_or_else(|| effect_kind.to_string()),
                phase: OperationPhase::Pending,
                handler_identity: Some(handler_identity.to_string()),
                effect_ids: vec![effect_id],
                dependent_operation_ids: Vec::new(),
                terminal_publication: None,
                budget_ticks,
                requires_proof: false,
            },
            &self.config.observability_retention,
        );
        self.set_progress_contract_state(
            &operation_id,
            session,
            ProgressState::Pending,
            budget_ticks,
            None,
            true,
        );
        effect_id
    }

    fn sync_runtime_effect_from_trace_entry(&mut self, entry: &EffectTraceEntry) {
        if self
            .outstanding_effects
            .as_slice()
            .iter()
            .any(|effect| effect.effect_id == entry.effect_id)
        {
            return;
        }

        let session = entry
            .inputs
            .get("session")
            .and_then(serde_json::Value::as_u64)
            .and_then(|sid| usize::try_from(sid).ok())
            .or_else(|| {
                entry
                    .inputs
                    .get("sid")
                    .and_then(serde_json::Value::as_u64)
                    .and_then(|sid| usize::try_from(sid).ok())
            });
        let owner_id = self.current_operation_owner(session);
        let operation_id = Self::effect_operation_id(entry.effect_id);
        let status = match entry
            .outputs
            .get("status")
            .and_then(serde_json::Value::as_str)
        {
            Some("blocked") => OutstandingEffectStatus::Blocked,
            Some("failure") => OutstandingEffectStatus::Failed,
            Some("cancelled") => OutstandingEffectStatus::Cancelled,
            Some("invalidated") => OutstandingEffectStatus::Invalidated,
            _ => OutstandingEffectStatus::Succeeded,
        };
        let budget_ticks = Some(1);

        self.outstanding_effects.push(
            OutstandingEffect {
                effect_id: entry.effect_id,
                operation_id: operation_id.clone(),
                session,
                owner_id: owner_id.clone(),
                effect_interface: entry.effect_interface.clone(),
                effect_operation: entry.effect_operation.clone(),
                effect_kind: entry.effect_kind.clone(),
                handler_identity: entry.handler_identity.clone(),
                status,
                ordering_key: entry.ordering_key,
                budget_ticks,
                retry_policy: "forbid_late_results".to_string(),
                invalidation_token: Self::effect_invalidation_token(entry.effect_id),
                completed_at_tick: Some(self.clock.tick),
                inputs: entry.inputs.clone(),
                outputs: entry.outputs.clone(),
            },
            &self.config.observability_retention,
        );
        self.operation_instances.push(
            OperationInstance {
                operation_id: operation_id.clone(),
                session,
                owner_id,
                kind: entry
                    .effect_operation
                    .clone()
                    .unwrap_or_else(|| entry.effect_kind.clone()),
                phase: Self::effect_status_phase(status),
                handler_identity: Some(entry.handler_identity.clone()),
                effect_ids: vec![entry.effect_id],
                dependent_operation_ids: Vec::new(),
                terminal_publication: Self::effect_terminal_publication(status),
                budget_ticks,
                requires_proof: false,
            },
            &self.config.observability_retention,
        );
        self.set_progress_contract_state(
            &operation_id,
            session,
            Self::progress_state_for_effect_status(status),
            budget_ticks,
            entry
                .outputs
                .get("reason")
                .and_then(serde_json::Value::as_str)
                .map(ToString::to_string),
            true,
        );
    }

    fn complete_runtime_effect(
        &mut self,
        effect_id: u64,
        status: OutstandingEffectStatus,
        outputs: serde_json::Value,
    ) -> Result<(), ProtocolMachineError> {
        let Some(effect_index) = self
            .outstanding_effects
            .as_slice()
            .iter()
            .position(|effect| effect.effect_id == effect_id)
        else {
            return Err(ProtocolMachineError::HandlerError(EffectFailure::contract_violation(
                format!(
                    "[host-contract] completion for effect {effect_id} requires a live outstanding-effect record"
                ),
            )));
        };
        if !matches!(
            self.outstanding_effects.as_slice()[effect_index].status,
            OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
        ) {
            return Err(ProtocolMachineError::HandlerError(
                EffectFailure::contract_violation(format!(
                    "[host-contract] late result for effect {effect_id} rejected after {:?}",
                    self.outstanding_effects.as_slice()[effect_index].status
                )),
            ));
        }

        let operation_id;
        let session;
        let budget_ticks;
        let reason;
        {
            let effect = &mut self.outstanding_effects.as_mut_slice()[effect_index];
            effect.status = status;
            effect.outputs = outputs;
            effect.completed_at_tick = Some(self.clock.tick);
            effect.ordering_key = self.clock.tick;
            operation_id = effect.operation_id.clone();
            session = effect.session;
            budget_ticks = effect.budget_ticks;
            reason = effect
                .outputs
                .get("reason")
                .and_then(serde_json::Value::as_str)
                .map(ToString::to_string);
        }

        if let Some(operation) = self
            .operation_instances
            .as_mut_slice()
            .iter_mut()
            .find(|operation| operation.operation_id == operation_id)
        {
            operation.phase = Self::effect_status_phase(status);
            operation.terminal_publication = Self::effect_terminal_publication(status);
        }

        self.set_progress_contract_state(
            &operation_id,
            session,
            Self::progress_state_for_effect_status(status),
            budget_ticks,
            reason,
            true,
        );

        Ok(())
    }

    fn invalidate_outstanding_effects_for_session(&mut self, session: SessionId, reason: &str) {
        let mut invalidated = Vec::new();
        for effect in self.outstanding_effects.as_mut_slice().iter_mut() {
            if effect.session != Some(session) {
                continue;
            }
            if !matches!(
                effect.status,
                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
            ) {
                continue;
            }
            effect.status = OutstandingEffectStatus::Invalidated;
            effect.outputs = json!({
                "status": "invalidated",
                "reason": reason,
            });
            effect.completed_at_tick = Some(self.clock.tick);
            effect.ordering_key = self.clock.tick;
            invalidated.push(effect.operation_id.clone());
        }

        for operation in self.operation_instances.as_mut_slice().iter_mut() {
            if invalidated.contains(&operation.operation_id) {
                operation.phase = OperationPhase::Failed;
                operation.terminal_publication = Some("effect.invalidated".to_string());
            }
        }
        for operation_id in invalidated {
            self.set_progress_contract_state(
                &operation_id,
                Some(session),
                ProgressState::Failed,
                Some(1),
                Some(reason.to_string()),
                true,
            );
        }
    }

    fn apply_semantic_handoff_obligations(&mut self, receipt: &DelegationReceipt) {
        let handoff_operation_id = format!("handoff:{}", receipt.receipt_id);
        let old_owner = Self::coro_owner_id(receipt.from_coro);
        let new_owner = Self::coro_owner_id(receipt.to_coro);
        let mut invalidated_operations = Vec::new();

        for effect in self.outstanding_effects.as_mut_slice().iter_mut() {
            if effect.session != Some(receipt.session) {
                continue;
            }
            match effect.status {
                OutstandingEffectStatus::Pending => {
                    effect.owner_id = Some(new_owner.clone());
                }
                OutstandingEffectStatus::Blocked => {
                    effect.status = OutstandingEffectStatus::Invalidated;
                    effect.owner_id = Some(new_owner.clone());
                    effect.outputs = json!({
                        "status": "invalidated",
                        "reason": "semantic handoff invalidated blocked effect",
                        "revoked_owner_id": old_owner,
                        "activated_owner_id": new_owner,
                        "handoff_id": receipt.receipt_id,
                    });
                    effect.completed_at_tick = Some(self.clock.tick);
                    effect.ordering_key = self.clock.tick;
                    invalidated_operations.push(effect.operation_id.clone());
                }
                OutstandingEffectStatus::Succeeded
                | OutstandingEffectStatus::Failed
                | OutstandingEffectStatus::Cancelled
                | OutstandingEffectStatus::Invalidated => {}
            }
        }

        for operation in self.operation_instances.as_mut_slice().iter_mut() {
            if operation.session != Some(receipt.session) {
                continue;
            }
            if !operation
                .dependent_operation_ids
                .iter()
                .any(|id| id == &handoff_operation_id)
            {
                operation
                    .dependent_operation_ids
                    .push(handoff_operation_id.clone());
            }
            match operation.phase {
                OperationPhase::Pending | OperationPhase::Blocked => {
                    operation.owner_id = Some(new_owner.clone());
                }
                OperationPhase::Succeeded
                | OperationPhase::Failed
                | OperationPhase::Cancelled
                | OperationPhase::TimedOut
                | OperationPhase::HandedOff => {}
            }
            if invalidated_operations.contains(&operation.operation_id) {
                operation.phase = OperationPhase::Failed;
                operation.terminal_publication = Some("effect.invalidated".to_string());
            }
        }
        for operation_id in invalidated_operations {
            self.set_progress_contract_state(
                &operation_id,
                Some(receipt.session),
                ProgressState::Failed,
                Some(1),
                Some("semantic handoff invalidated blocked effect".to_string()),
                true,
            );
        }
        self.set_progress_contract_state(
            &handoff_operation_id,
            Some(receipt.session),
            ProgressState::HandedOff,
            Some(1),
            Some("semantic handoff committed".to_string()),
            true,
        );
    }
}

#[cfg(test)]
mod runtime_effect_state_tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    use crate::instr::Endpoint;
    use crate::loader::CodeImage;
    use crate::output_condition::{OutputConditionCheck, OutputConditionMeta};
    use crate::owned::OwnedSession;
    use crate::transfer_semantics::{DelegationAuditRecord, DelegationStatus};
    use crate::PublicationStatus;
    use telltale_types::{GlobalType, Label, LocalTypeR};

    fn test_vm() -> ProtocolMachine {
        ProtocolMachine::new(ProtocolMachineConfig::default())
    }

    fn lifecycle_image() -> CodeImage {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".to_string(),
                branches: vec![(Label::new("m"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".to_string(),
                branches: vec![(Label::new("m"), None, LocalTypeR::End)],
            },
        );
        let global = GlobalType::send("A", "B", Label::new("m"), GlobalType::End);
        CodeImage::from_local_types(&local_types, &global)
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    enum LifecycleAction {
        OpenOwnedSession,
        IssueEffect,
        CompleteEffect,
        DuplicateCompletion,
        LateCancel,
        InvalidateSession,
        TimeoutEffect,
        CancelEffect,
        Handoff,
        OwnerCrash,
        PublicationWithoutProof,
        DuplicatePublication,
        MaterializeSuccess,
        BindCanonicalHandle,
        RejectObservedRead,
        RequireMissingCanonicalHandle,
        ImmediateEffectMisuse,
        ReplaySemanticObjects,
    }

    impl LifecycleAction {
        fn name(self) -> &'static str {
            match self {
                Self::OpenOwnedSession => "open_owned_session",
                Self::IssueEffect => "issue_effect",
                Self::CompleteEffect => "complete_effect",
                Self::DuplicateCompletion => "duplicate_completion",
                Self::LateCancel => "late_cancel",
                Self::InvalidateSession => "invalidate_session",
                Self::TimeoutEffect => "timeout_effect",
                Self::CancelEffect => "cancel_effect",
                Self::Handoff => "handoff",
                Self::OwnerCrash => "owner_crash",
                Self::PublicationWithoutProof => "publication_without_proof",
                Self::DuplicatePublication => "duplicate_publication",
                Self::MaterializeSuccess => "materialize_success",
                Self::BindCanonicalHandle => "bind_canonical_handle",
                Self::RejectObservedRead => "reject_observed_read",
                Self::RequireMissingCanonicalHandle => "require_missing_canonical_handle",
                Self::ImmediateEffectMisuse => "immediate_effect_misuse",
                Self::ReplaySemanticObjects => "replay_semantic_objects",
            }
        }
    }

    #[derive(Debug, Clone)]
    enum ScheduledEffectEvent {
        IssueEffect,
        CompleteEffect,
        DuplicateCompletion,
        LateCancel,
        TimeoutEffect,
        CancelEffect,
        PublicationWithoutProof,
        DuplicatePublication,
        MaterializeSuccess,
        RejectObservedRead,
        RequireMissingCanonicalHandle,
        ImmediateEffectMisuse,
    }

    #[derive(Debug, Clone)]
    enum ScheduledTopologyPerturbation {
        OpenOwnedSession,
        InvalidateSession,
        Handoff,
        OwnerCrash,
    }

    #[derive(Debug, Clone)]
    enum ScheduledFaultSurface {
        LateResultRejected,
        ProofRequired,
        ObservedReadRejected,
        MissingCanonicalHandle,
        UnknownEffectRejected,
    }

    #[derive(Debug, Clone)]
    struct LifecycleScenario {
        name: &'static str,
        seed: u64,
        actions: Vec<LifecycleAction>,
        effect_schedule: Vec<ScheduledEffectEvent>,
        topology_perturbations: Vec<ScheduledTopologyPerturbation>,
        fault_surfaces: Vec<ScheduledFaultSurface>,
        terminal_classification: &'static str,
    }

    struct LifecycleHarness {
        seed: u64,
        machine: ProtocolMachine,
        owned: Option<OwnedSession>,
        session_id: Option<SessionId>,
        active_owner: Option<String>,
        action_log: Vec<String>,
        action_counts: BTreeMap<&'static str, usize>,
        late_result_rejections: BTreeSet<u64>,
        proof_gap_operations: BTreeSet<String>,
        last_handoff_id: Option<u64>,
        last_bound_handle: Option<String>,
        materialization_count: u64,
        proof_gap_count: u64,
    }

    impl LifecycleHarness {
        fn new(seed: u64) -> Self {
            Self {
                seed,
                machine: test_vm(),
                owned: None,
                session_id: None,
                active_owner: None,
                action_log: Vec::new(),
                action_counts: BTreeMap::new(),
                late_result_rejections: BTreeSet::new(),
                proof_gap_operations: BTreeSet::new(),
                last_handoff_id: None,
                last_bound_handle: None,
                materialization_count: 0,
                proof_gap_count: 0,
            }
        }

        fn run_scenario(&mut self, scenario: &LifecycleScenario) {
            self.assert_declared_impurity_surfaces(scenario);
            for action in &scenario.actions {
                self.execute(*action);
                self.assert_invariants(scenario);
            }
        }

        fn execute(&mut self, action: LifecycleAction) {
            self.action_log
                .push(format!("tick={} {}", self.machine.clock.tick, action.name()));
            *self.action_counts.entry(action.name()).or_insert(0) += 1;
            match action {
                LifecycleAction::OpenOwnedSession => self.open_owned_session(),
                LifecycleAction::IssueEffect => self.issue_effect(),
                LifecycleAction::CompleteEffect => self.complete_latest_effect(),
                LifecycleAction::DuplicateCompletion => self.duplicate_latest_completion(),
                LifecycleAction::LateCancel => self.reject_late_cancel(),
                LifecycleAction::InvalidateSession => self.invalidate_session(),
                LifecycleAction::TimeoutEffect => self.timeout_latest_effect(),
                LifecycleAction::CancelEffect => self.cancel_latest_effect(),
                LifecycleAction::Handoff => self.handoff_session(),
                LifecycleAction::OwnerCrash => self.owner_crash(),
                LifecycleAction::PublicationWithoutProof => self.inject_proof_gap_operation(),
                LifecycleAction::DuplicatePublication => self.inject_duplicate_publication(),
                LifecycleAction::MaterializeSuccess => self.materialize_success(),
                LifecycleAction::BindCanonicalHandle => self.bind_latest_canonical_handle(),
                LifecycleAction::RejectObservedRead => self.reject_observed_read(),
                LifecycleAction::RequireMissingCanonicalHandle => self.require_missing_handle(),
                LifecycleAction::ImmediateEffectMisuse => self.reject_immediate_effect_misuse(),
                LifecycleAction::ReplaySemanticObjects => self.replay_semantic_objects(),
            }
        }

        fn open_owned_session(&mut self) {
            let image = lifecycle_image();
            let owned = self
                .machine
                .load_choreography_owned(&image, format!("runtime/owner/{}", self.seed))
                .expect("owned open should succeed");
            self.active_owner = Some(owned.capability().owner_id.clone());
            self.session_id = Some(owned.session_id());
            self.owned = Some(owned);
        }

        fn issue_effect(&mut self) {
            let sid = self.session_id.expect("session must be opened");
            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            let effect_id = self.machine.issue_runtime_effect(
                "invoke_step",
                Some(sid),
                "host/runtime",
                serde_json::json!({
                    "session": sid,
                    "seed": self.seed,
                    "ordering_key": self.machine.clock.tick,
                }),
            );
            let effect = self
                .machine
                .outstanding_effects
                .as_slice()
                .iter()
                .find(|effect| effect.effect_id == effect_id)
                .expect("issued effect should be retained");
            assert_eq!(
                effect.owner_id.as_deref(),
                self.active_owner.as_deref(),
                "{}",
                self.context("issued effect owner should match active owner"),
            );
        }

        fn complete_latest_effect(&mut self) {
            let effect_id = self.latest_active_effect_id();
            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            self.machine
                .complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Succeeded,
                    serde_json::json!({
                        "status": "success",
                        "seed": self.seed,
                    }),
                )
                .expect("live effect completion should succeed");
        }

        fn duplicate_latest_completion(&mut self) {
            let effect_id = self.latest_terminal_effect_id();
            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            let err = self
                .machine
                .complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Succeeded,
                    serde_json::json!({ "status": "success" }),
                )
                .expect_err("duplicate completion must be rejected");
            assert!(
                err.to_string().contains("late result"),
                "{}",
                self.context("duplicate completion should report a late result"),
            );
            self.late_result_rejections.insert(effect_id);
        }

        fn reject_late_cancel(&mut self) {
            let effect_id = self.latest_terminal_effect_id();
            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            let err = self
                .machine
                .complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Cancelled,
                    serde_json::json!({
                        "status": "cancelled",
                        "reason": "late cancellation",
                    }),
                )
                .expect_err("late cancellation must be rejected");
            assert!(
                err.to_string().contains("late result"),
                "{}",
                self.context("late cancellation should be rejected as a stale result"),
            );
            self.late_result_rejections.insert(effect_id);
        }

        fn invalidate_session(&mut self) {
            let sid = self.session_id.expect("session must be opened");
            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            self.machine
                .invalidate_outstanding_effects_for_session(sid, "manual lifecycle invalidation");
        }

        fn timeout_latest_effect(&mut self) {
            for _ in 0..4 {
                self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
                self.machine
                    .evaluate_progress_contracts()
                    .expect("progress escalation should remain deterministic");
            }
            let effect = self
                .machine
                .outstanding_effects
                .as_slice()
                .iter()
                .find(|effect| {
                    matches!(effect.status, OutstandingEffectStatus::Invalidated)
                        && effect
                            .outputs
                            .get("reason")
                            .and_then(serde_json::Value::as_str)
                            == Some("bounded wait exhausted; late results are invalid")
                })
                .expect("timeout should invalidate one effect");
            let contract = self
                .machine
                .progress_contracts
                .as_slice()
                .iter()
                .find(|contract| contract.operation_id == effect.operation_id)
                .expect("timeout should retain a progress contract");
            assert_eq!(contract.state, ProgressState::TimedOut);
            let escalations: Vec<_> = self
                .machine
                .progress_transitions
                .as_slice()
                .iter()
                .filter(|transition| transition.operation_id == effect.operation_id)
                .map(|transition| transition.to_state)
                .collect();
            assert_eq!(
                escalations,
                vec![
                    ProgressState::Blocked,
                    ProgressState::NoProgress,
                    ProgressState::Degraded,
                    ProgressState::TimedOut,
                ],
                "{}",
                self.context("timeout path should expose deterministic escalation windows"),
            );
        }

        fn cancel_latest_effect(&mut self) {
            let effect_id = self.latest_active_effect_id();
            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            self.machine
                .complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Cancelled,
                    serde_json::json!({
                        "status": "cancelled",
                        "reason": "deterministic cancellation",
                    }),
                )
                .expect("cancellation should succeed");
        }

        fn handoff_session(&mut self) {
            let sid = self.session_id.expect("session must be opened");
            let effect_id = self.latest_active_effect_id();
            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            self.machine
                .evaluate_progress_contracts()
                .expect("handoff setup should deterministically block the effect");
            let blocked = self
                .machine
                .outstanding_effects
                .as_slice()
                .iter()
                .find(|effect| effect.effect_id == effect_id)
                .expect("blocked effect");
            assert_eq!(blocked.status, OutstandingEffectStatus::Blocked);

            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            let receipt_id = 100 + u64::try_from(self.action_log.len()).expect("log length fits");
            let receipt = delegation_receipt(
                receipt_id,
                Endpoint {
                    sid,
                    role: "A".to_string(),
                },
                0,
                1,
            );
            self.machine.apply_semantic_handoff_obligations(&receipt);
            self.machine.delegation_audit_log.push(
                DelegationAuditRecord {
                    tick: self.machine.clock.tick,
                    receipt,
                    status: DelegationStatus::Committed,
                    reason: Some("deterministic semantic handoff committed".to_string()),
                },
                &self.machine.config.observability_retention,
            );
            self.active_owner = Some("coro:1".to_string());
            self.last_handoff_id = Some(receipt_id);
        }

        fn owner_crash(&mut self) {
            let owned = self
                .owned
                .clone()
                .expect("owner crash requires a live owned session");
            self.machine.clock.tick = self.machine.clock.tick.saturating_add(1);
            let witness = owned
                .mark_owner_died(&mut self.machine)
                .expect("owner crash should emit a cancellation witness");
            assert!(
                witness.witness_id > 0,
                "{}",
                self.context("owner crash should emit a stable cancellation witness"),
            );
            self.active_owner = None;
        }

        fn inject_proof_gap_operation(&mut self) {
            let sid = self.session_id.expect("session must be opened");
            self.proof_gap_count = self.proof_gap_count.saturating_add(1);
            let operation_id = format!("proof_gap:{}:{}", self.seed, self.proof_gap_count);
            self.push_proof_gap_operation(&operation_id, sid);
            self.proof_gap_operations.insert(operation_id);
        }

        fn push_proof_gap_operation(&mut self, operation_id: &str, sid: SessionId) {
            self.machine.operation_instances.push(
                OperationInstance {
                    operation_id: operation_id.to_string(),
                    session: Some(sid),
                    owner_id: self.active_owner.clone(),
                    kind: "proof_gap".to_string(),
                    phase: OperationPhase::Succeeded,
                    handler_identity: Some("host/runtime".to_string()),
                    effect_ids: Vec::new(),
                    dependent_operation_ids: Vec::new(),
                    terminal_publication: Some("proof_gap.succeeded".to_string()),
                    budget_ticks: Some(1),
                    requires_proof: true,
                },
                &self.machine.config.observability_retention,
            );
            self.machine.set_progress_contract_state(
                operation_id,
                Some(sid),
                ProgressState::Succeeded,
                Some(1),
                Some("proof-bearing success requires materialization".to_string()),
                true,
            );
        }

        fn inject_duplicate_publication(&mut self) {
            let sid = self.session_id.expect("session must be opened");
            let operation_id = format!("duplicate_publication:{}", self.seed);
            self.push_proof_gap_operation(&operation_id, sid);
            self.push_proof_gap_operation(&operation_id, sid);
            self.proof_gap_operations.insert(operation_id);
        }

        fn materialize_success(&mut self) {
            self.materialization_count = self.materialization_count.saturating_add(1);
            let check = OutputConditionCheck {
                meta: OutputConditionMeta {
                    predicate_ref: "session.ready".to_string(),
                    witness_ref: Some(format!("seed:{}", self.seed)),
                    output_digest: format!("digest:{}:{}", self.seed, self.materialization_count),
                },
                passed: true,
            };
            self.machine.output_condition_checks.push(
                check.clone(),
                &self.machine.config.observability_retention,
            );
            self.last_bound_handle = Some(format!("materialization:{}", check.meta.output_digest));
        }

        fn bind_latest_canonical_handle(&mut self) {
            let handle_id = self
                .last_bound_handle
                .clone()
                .expect("materialization must run before canonical handle binding");
            let handle = self
                .machine
                .require_canonical_handle(&handle_id)
                .expect("bound canonical handle should exist");
            assert_eq!(handle.handle_id, handle_id);
        }

        fn reject_observed_read(&mut self) {
            let observed = self
                .machine
                .semantic_objects()
                .observed_reads
                .first()
                .cloned()
                .expect("scenario should surface one observed read");
            let err = self
                .machine
                .require_authoritative_read(&observed.read_id)
                .expect_err("observed reads must be rejected on semantic paths");
            assert!(
                err.to_string().contains("observed read"),
                "{}",
                self.context("observed read must be rejected on authoritative path"),
            );
        }

        fn require_missing_handle(&mut self) {
            let err = self
                .machine
                .require_canonical_handle("materialization:missing")
                .expect_err("missing canonical handle must be rejected");
            assert!(
                err.to_string().contains("canonical handle"),
                "{}",
                self.context("missing canonical handle should fail closed"),
            );
        }

        fn reject_immediate_effect_misuse(&mut self) {
            let err = self
                .machine
                .complete_runtime_effect(
                    999_999,
                    OutstandingEffectStatus::Succeeded,
                    serde_json::json!({ "status": "success" }),
                )
                .expect_err("completing an unknown semantic-path effect must fail");
            assert!(
                err.to_string().contains("live outstanding-effect record"),
                "{}",
                self.context("semantic-path effect misuse should fail closed"),
            );
        }

        fn replay_semantic_objects(&mut self) {
            let semantic_objects = self.machine.semantic_objects();
            let encoded =
                serde_json::to_string(&semantic_objects).expect("semantic objects serialize");
            let decoded: ProtocolMachineSemanticObjects =
                serde_json::from_str(&encoded).expect("semantic objects deserialize");
            assert_eq!(
                decoded,
                semantic_objects,
                "{}",
                self.context("semantic object replay roundtrip must remain stable"),
            );
        }

        fn latest_active_effect_id(&self) -> u64 {
            self.machine
                .outstanding_effects
                .as_slice()
                .iter()
                .rev()
                .find(|effect| {
                    matches!(
                        effect.status,
                        OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
                    )
                })
                .map(|effect| effect.effect_id)
                .expect("expected one active effect")
        }

        fn latest_terminal_effect_id(&self) -> u64 {
            self.machine
                .outstanding_effects
                .as_slice()
                .iter()
                .rev()
                .find(|effect| {
                    !matches!(
                        effect.status,
                        OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
                    )
                })
                .map(|effect| effect.effect_id)
                .expect("expected one terminal effect")
        }

        fn context(&self, message: &str) -> String {
            format!(
                "{message}; seed={}; actions={:?}",
                self.seed, self.action_log
            )
        }

        fn assert_declared_impurity_surfaces(&self, scenario: &LifecycleScenario) {
            let mut declared = BTreeSet::new();

            for event in &scenario.effect_schedule {
                declared.insert(match event {
                    ScheduledEffectEvent::IssueEffect => LifecycleAction::IssueEffect,
                    ScheduledEffectEvent::CompleteEffect => LifecycleAction::CompleteEffect,
                    ScheduledEffectEvent::DuplicateCompletion => LifecycleAction::DuplicateCompletion,
                    ScheduledEffectEvent::LateCancel => LifecycleAction::LateCancel,
                    ScheduledEffectEvent::TimeoutEffect => LifecycleAction::TimeoutEffect,
                    ScheduledEffectEvent::CancelEffect => LifecycleAction::CancelEffect,
                    ScheduledEffectEvent::PublicationWithoutProof => {
                        LifecycleAction::PublicationWithoutProof
                    }
                    ScheduledEffectEvent::DuplicatePublication => {
                        LifecycleAction::DuplicatePublication
                    }
                    ScheduledEffectEvent::MaterializeSuccess => LifecycleAction::MaterializeSuccess,
                    ScheduledEffectEvent::RejectObservedRead => LifecycleAction::RejectObservedRead,
                    ScheduledEffectEvent::RequireMissingCanonicalHandle => {
                        LifecycleAction::RequireMissingCanonicalHandle
                    }
                    ScheduledEffectEvent::ImmediateEffectMisuse => {
                        LifecycleAction::ImmediateEffectMisuse
                    }
                });
            }

            for event in &scenario.topology_perturbations {
                declared.insert(match event {
                    ScheduledTopologyPerturbation::OpenOwnedSession => {
                        LifecycleAction::OpenOwnedSession
                    }
                    ScheduledTopologyPerturbation::InvalidateSession => {
                        LifecycleAction::InvalidateSession
                    }
                    ScheduledTopologyPerturbation::Handoff => LifecycleAction::Handoff,
                    ScheduledTopologyPerturbation::OwnerCrash => LifecycleAction::OwnerCrash,
                });
            }

            let expected: BTreeSet<_> = scenario
                .actions
                .iter()
                .copied()
                .filter(|action| {
                    !matches!(
                        action,
                        LifecycleAction::ReplaySemanticObjects
                            | LifecycleAction::BindCanonicalHandle
                    )
                })
                .collect();

            assert_eq!(
                declared, expected,
                "{}",
                self.context(
                    "all semantic impurity must be declared through effect schedules, topology perturbations, or fault surfaces"
                ),
            );

            if scenario.actions.iter().any(|action| {
                matches!(
                    action,
                    LifecycleAction::DuplicateCompletion
                        | LifecycleAction::LateCancel
                        | LifecycleAction::PublicationWithoutProof
                        | LifecycleAction::DuplicatePublication
                        | LifecycleAction::RejectObservedRead
                        | LifecycleAction::RequireMissingCanonicalHandle
                        | LifecycleAction::ImmediateEffectMisuse
                )
            }) {
                assert!(
                    !scenario.fault_surfaces.is_empty(),
                    "{}",
                    self.context("fault-driven adversarial scenarios must declare fault surfaces"),
                );
            }

            assert!(
                !scenario.terminal_classification.is_empty(),
                "{}",
                self.context("scenario must declare a terminal classification"),
            );
        }

        #[allow(clippy::too_many_lines)]
        fn assert_invariants(&self, scenario: &LifecycleScenario) {
            let semantic_objects = self.machine.semantic_objects();
            let context = self.context(scenario.name);

            assert!(
                semantic_objects.parity_critical_operations_have_progress_contracts(),
                "{}",
                context,
            );

            let mut publication_ids = BTreeSet::new();
            for publication in &semantic_objects.publication_events {
                assert!(
                    publication_ids.insert(publication.publication_id.clone()),
                    "{}",
                    self.context("publication ids must remain canonical"),
                );
            }

            for operation_id in &self.proof_gap_operations {
                let publication = semantic_objects
                    .publication_events
                    .iter()
                    .find(|event| event.operation_id == *operation_id)
                    .expect("proof-gap operation should emit a publication event");
                assert_eq!(
                    publication.status,
                    PublicationStatus::Rejected,
                    "{}",
                    self.context("proof-gap publication must be rejected"),
                );
                assert_eq!(
                    publication.reason.as_deref(),
                    Some("proof-bearing success required"),
                    "{}",
                    self.context("proof-gap rejection reason must stay stable"),
                );
            }

            if let Some(active_owner) = self.active_owner.as_deref() {
                for effect in self.machine.outstanding_effects.as_slice().iter().filter(|effect| {
                    matches!(
                        effect.status,
                        OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
                    )
                }) {
                    assert_eq!(
                        effect.owner_id.as_deref(),
                        Some(active_owner),
                        "{}",
                        self.context("active effects must have one semantic owner"),
                    );
                }
                for operation in self
                    .machine
                    .operation_instances
                    .as_slice()
                    .iter()
                    .filter(|operation| {
                        matches!(operation.phase, OperationPhase::Pending | OperationPhase::Blocked)
                    })
                {
                    assert_eq!(
                        operation.owner_id.as_deref(),
                        Some(active_owner),
                        "{}",
                        self.context("active operations must have one semantic owner"),
                    );
                }
            }

            if let Some(handoff_id) = self.last_handoff_id {
                let handoff = semantic_objects
                    .semantic_handoffs
                    .iter()
                    .find(|handoff| handoff.handoff_id == handoff_id)
                    .expect("handoff should surface in semantic objects");
                assert_eq!(handoff.revoked_owner_id, "coro:0", "{context}");
                assert_eq!(handoff.activated_owner_id, "coro:1", "{context}");
                assert!(
                    semantic_objects.progress_contracts.iter().any(|contract| {
                        contract.operation_id == format!("handoff:{handoff_id}")
                            && contract.state == ProgressState::HandedOff
                    }),
                    "{}",
                    self.context("handoff must export a handed-off progress contract"),
                );
            }

            for effect in self.machine.outstanding_effects.as_slice() {
                assert!(
                    effect.ordering_key <= self.machine.clock.tick,
                    "{}",
                    self.context("effect ordering keys must be deterministic"),
                );
            }

            if let Some(handle_id) = &self.last_bound_handle {
                assert!(
                    semantic_objects
                        .canonical_handles
                        .iter()
                        .any(|handle| handle.handle_id == *handle_id),
                    "{}",
                    self.context("materialization should export a canonical handle"),
                );
            }

            for operation_id in &self.proof_gap_operations {
                let publication_count = semantic_objects
                    .publication_events
                    .iter()
                    .filter(|publication| publication.operation_id == *operation_id)
                    .count();
                assert_eq!(
                    publication_count,
                    1,
                    "{}",
                    self.context("duplicate publication roots must collapse canonically"),
                );
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn lifecycle_scenarios() -> Vec<LifecycleScenario> {
        vec![
            LifecycleScenario {
                name: "complete_then_reject_duplicate",
                seed: 7,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::CompleteEffect,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::CompleteEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "late_result_rejected",
            },
            LifecycleScenario {
                name: "cancel_then_reject_duplicate",
                seed: 11,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::CancelEffect,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::CancelEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "late_result_rejected",
            },
            LifecycleScenario {
                name: "timeout_then_reject_duplicate",
                seed: 23,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::TimeoutEffect,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::TimeoutEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "timed_out_then_rejected",
            },
            LifecycleScenario {
                name: "handoff_invalidates_blocked_effects",
                seed: 29,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::Handoff,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![
                    ScheduledTopologyPerturbation::OpenOwnedSession,
                    ScheduledTopologyPerturbation::Handoff,
                ],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "handoff_invalidated",
            },
            LifecycleScenario {
                name: "session_invalidation_rejects_late_results",
                seed: 31,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::InvalidateSession,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![
                    ScheduledTopologyPerturbation::OpenOwnedSession,
                    ScheduledTopologyPerturbation::InvalidateSession,
                ],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "session_invalidated",
            },
            LifecycleScenario {
                name: "owner_crash_invalidates_effects",
                seed: 37,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::OwnerCrash,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![
                    ScheduledTopologyPerturbation::OpenOwnedSession,
                    ScheduledTopologyPerturbation::OwnerCrash,
                ],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "owner_crash_invalidated",
            },
            LifecycleScenario {
                name: "proof_gap_and_materialization",
                seed: 41,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::PublicationWithoutProof,
                    LifecycleAction::MaterializeSuccess,
                    LifecycleAction::BindCanonicalHandle,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::PublicationWithoutProof,
                    ScheduledEffectEvent::MaterializeSuccess,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::ProofRequired],
                terminal_classification: "proof_gap_rejected",
            },
        ]
    }

    #[allow(clippy::too_many_lines)]
    fn adversarial_scenarios() -> Vec<LifecycleScenario> {
        vec![
            LifecycleScenario {
                name: "stale_late_result_after_handoff",
                seed: 53,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::Handoff,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![
                    ScheduledTopologyPerturbation::OpenOwnedSession,
                    ScheduledTopologyPerturbation::Handoff,
                ],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "late_result_rejected",
            },
            LifecycleScenario {
                name: "owner_crash_before_handoff",
                seed: 59,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::OwnerCrash,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![
                    ScheduledTopologyPerturbation::OpenOwnedSession,
                    ScheduledTopologyPerturbation::OwnerCrash,
                ],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "owner_crash_invalidated",
            },
            LifecycleScenario {
                name: "owner_crash_after_handoff",
                seed: 61,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::Handoff,
                    LifecycleAction::OwnerCrash,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![
                    ScheduledTopologyPerturbation::OpenOwnedSession,
                    ScheduledTopologyPerturbation::Handoff,
                    ScheduledTopologyPerturbation::OwnerCrash,
                ],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "handoff_then_owner_crash",
            },
            LifecycleScenario {
                name: "timeout_vs_cancellation_race",
                seed: 67,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::TimeoutEffect,
                    LifecycleAction::LateCancel,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::TimeoutEffect,
                    ScheduledEffectEvent::LateCancel,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "timed_out_then_rejected",
            },
            LifecycleScenario {
                name: "retry_after_terminalization",
                seed: 71,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::CompleteEffect,
                    LifecycleAction::DuplicateCompletion,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::CompleteEffect,
                    ScheduledEffectEvent::DuplicateCompletion,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "terminalized_then_rejected",
            },
            LifecycleScenario {
                name: "duplicate_publication_attempt",
                seed: 73,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::DuplicatePublication,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![ScheduledEffectEvent::DuplicatePublication],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::ProofRequired],
                terminal_classification: "publication_collapsed",
            },
            LifecycleScenario {
                name: "observed_read_use_on_authoritative_path",
                seed: 79,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::CompleteEffect,
                    LifecycleAction::RejectObservedRead,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::CompleteEffect,
                    ScheduledEffectEvent::RejectObservedRead,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::ObservedReadRejected],
                terminal_classification: "observed_read_rejected",
            },
            LifecycleScenario {
                name: "missing_canonical_handle_on_parity_critical_path",
                seed: 83,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::PublicationWithoutProof,
                    LifecycleAction::RequireMissingCanonicalHandle,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::PublicationWithoutProof,
                    ScheduledEffectEvent::RequireMissingCanonicalHandle,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![
                    ScheduledFaultSurface::ProofRequired,
                    ScheduledFaultSurface::MissingCanonicalHandle,
                ],
                terminal_classification: "missing_handle_rejected",
            },
            LifecycleScenario {
                name: "blocked_progress_escalation",
                seed: 89,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::IssueEffect,
                    LifecycleAction::TimeoutEffect,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![
                    ScheduledEffectEvent::IssueEffect,
                    ScheduledEffectEvent::TimeoutEffect,
                ],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::LateResultRejected],
                terminal_classification: "timed_out",
            },
            LifecycleScenario {
                name: "immediate_effect_misuse",
                seed: 97,
                actions: vec![
                    LifecycleAction::OpenOwnedSession,
                    LifecycleAction::ImmediateEffectMisuse,
                    LifecycleAction::ReplaySemanticObjects,
                ],
                effect_schedule: vec![ScheduledEffectEvent::ImmediateEffectMisuse],
                topology_perturbations: vec![ScheduledTopologyPerturbation::OpenOwnedSession],
                fault_surfaces: vec![ScheduledFaultSurface::UnknownEffectRejected],
                terminal_classification: "invalid_effect_rejected",
            },
        ]
    }

    #[test]
    fn runtime_reentrancy_rejects_same_operation_requests() {
        let mut machine = test_vm();
        machine.outstanding_effects.push(
            OutstandingEffect {
                effect_id: 1,
                operation_id: "effect:1".to_string(),
                session: Some(7),
                owner_id: Some("owner/a".to_string()),
                effect_interface: Some("Runtime".to_string()),
                effect_operation: Some("invoke".to_string()),
                effect_kind: "invoke_step".to_string(),
                handler_identity: "host/runtime".to_string(),
                status: OutstandingEffectStatus::Pending,
                ordering_key: 1,
                budget_ticks: Some(1),
                retry_policy: "forbid_late_results".to_string(),
                invalidation_token: "effect:1:live".to_string(),
                completed_at_tick: None,
                inputs: serde_json::json!({ "session": 7 }),
                outputs: serde_json::json!({ "status": "pending" }),
            },
            &machine.config.observability_retention,
        );

        let mut request =
            EffectRequest::invoke_step(5, Some(7), Some("effect:1".to_string()), "A", &[]);
        request.metadata.reentrancy_policy =
            crate::effect::EffectReentrancyPolicy::RejectSameOperation;

        let err = machine
            .ensure_effect_request_allowed(&request)
            .expect_err("same operation reentrancy must fail");
        assert!(err.message.contains("reentrancy rejected"));
    }

    #[test]
    fn runtime_reentrancy_rejects_same_fragment_requests() {
        let mut machine = test_vm();
        machine.outstanding_effects.push(
            OutstandingEffect {
                effect_id: 2,
                operation_id: "effect:2".to_string(),
                session: Some(9),
                owner_id: Some("owner/b".to_string()),
                effect_interface: Some("Guard".to_string()),
                effect_operation: Some("acquire".to_string()),
                effect_kind: "handle_acquire".to_string(),
                handler_identity: "host/runtime".to_string(),
                status: OutstandingEffectStatus::Blocked,
                ordering_key: 2,
                budget_ticks: Some(1),
                retry_policy: "forbid_late_results".to_string(),
                invalidation_token: "effect:2:live".to_string(),
                completed_at_tick: None,
                inputs: serde_json::json!({ "session": 9 }),
                outputs: serde_json::json!({ "status": "blocked" }),
            },
            &machine.config.observability_retention,
        );

        let mut request =
            EffectRequest::acquire(6, 9, Some("effect:3".to_string()), "A", "Guard", &[]);
        request.metadata.reentrancy_policy =
            crate::effect::EffectReentrancyPolicy::RejectSameFragment;

        let err = machine
            .ensure_effect_request_allowed(&request)
            .expect_err("same fragment reentrancy must fail");
        assert!(err.message.contains("footprint session:9"));
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn runtime_semantic_handoff_transfers_pending_effects_and_invalidates_blocked_effects() {
        let mut machine = test_vm();
        machine.clock.tick = 7;
        machine.outstanding_effects.push(
            OutstandingEffect {
                effect_id: 11,
                operation_id: "effect:11".to_string(),
                session: Some(5),
                owner_id: Some("coro:0".to_string()),
                effect_interface: Some("Runtime".to_string()),
                effect_operation: Some("invoke".to_string()),
                effect_kind: "invoke_step".to_string(),
                handler_identity: "host/runtime".to_string(),
                status: OutstandingEffectStatus::Pending,
                ordering_key: 1,
                budget_ticks: Some(1),
                retry_policy: "forbid_late_results".to_string(),
                invalidation_token: "effect:11:live".to_string(),
                completed_at_tick: None,
                inputs: serde_json::json!({ "session": 5 }),
                outputs: serde_json::json!({ "status": "pending" }),
            },
            &machine.config.observability_retention,
        );
        machine.outstanding_effects.push(
            OutstandingEffect {
                effect_id: 12,
                operation_id: "effect:12".to_string(),
                session: Some(5),
                owner_id: Some("coro:0".to_string()),
                effect_interface: Some("Runtime".to_string()),
                effect_operation: Some("receive".to_string()),
                effect_kind: "handle_recv".to_string(),
                handler_identity: "host/runtime".to_string(),
                status: OutstandingEffectStatus::Blocked,
                ordering_key: 2,
                budget_ticks: Some(1),
                retry_policy: "forbid_late_results".to_string(),
                invalidation_token: "effect:12:live".to_string(),
                completed_at_tick: None,
                inputs: serde_json::json!({ "session": 5 }),
                outputs: serde_json::json!({ "status": "blocked" }),
            },
            &machine.config.observability_retention,
        );
        machine.operation_instances.push(
            OperationInstance {
                operation_id: "effect:11".to_string(),
                session: Some(5),
                owner_id: Some("coro:0".to_string()),
                kind: "invoke".to_string(),
                phase: OperationPhase::Pending,
                handler_identity: Some("host/runtime".to_string()),
                effect_ids: vec![11],
                dependent_operation_ids: Vec::new(),
                terminal_publication: None,
                budget_ticks: Some(1),
                requires_proof: false,
            },
            &machine.config.observability_retention,
        );
        machine.operation_instances.push(
            OperationInstance {
                operation_id: "effect:12".to_string(),
                session: Some(5),
                owner_id: Some("coro:0".to_string()),
                kind: "receive".to_string(),
                phase: OperationPhase::Blocked,
                handler_identity: Some("host/runtime".to_string()),
                effect_ids: vec![12],
                dependent_operation_ids: Vec::new(),
                terminal_publication: Some("effect.blocked".to_string()),
                budget_ticks: Some(1),
                requires_proof: false,
            },
            &machine.config.observability_retention,
        );

        let receipt = delegation_receipt(
            3,
            Endpoint {
                sid: 5,
                role: "A".to_string(),
            },
            0,
            1,
        );
        machine.apply_semantic_handoff_obligations(&receipt);

        let pending = machine
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == 11)
            .expect("pending effect");
        assert_eq!(pending.owner_id.as_deref(), Some("coro:1"));
        assert_eq!(pending.status, OutstandingEffectStatus::Pending);

        let blocked = machine
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == 12)
            .expect("blocked effect");
        assert_eq!(blocked.owner_id.as_deref(), Some("coro:1"));
        assert_eq!(blocked.status, OutstandingEffectStatus::Invalidated);

        let err = machine
            .complete_runtime_effect(
                12,
                OutstandingEffectStatus::Succeeded,
                serde_json::json!({ "status": "success" }),
            )
            .expect_err("stale post-handoff result must be rejected");
        assert!(err.to_string().contains("late result"));
    }

    #[test]
    fn runtime_regions_preserve_locality_across_handoff_structure() {
        let mut machine = test_vm();
        machine.clock.tick = 7;
        machine.outstanding_effects.push(
            OutstandingEffect {
                effect_id: 21,
                operation_id: "effect:21".to_string(),
                session: Some(8),
                owner_id: Some("coro:0".to_string()),
                effect_interface: Some("Runtime".to_string()),
                effect_operation: Some("invoke".to_string()),
                effect_kind: "invoke_step".to_string(),
                handler_identity: "host/runtime".to_string(),
                status: OutstandingEffectStatus::Blocked,
                ordering_key: 3,
                budget_ticks: Some(1),
                retry_policy: "forbid_late_results".to_string(),
                invalidation_token: "effect:21:live".to_string(),
                completed_at_tick: None,
                inputs: serde_json::json!({ "session": 8, "fragment": "membership" }),
                outputs: serde_json::json!({ "status": "blocked" }),
            },
            &machine.config.observability_retention,
        );
        machine.operation_instances.push(
            OperationInstance {
                operation_id: "effect:21".to_string(),
                session: Some(8),
                owner_id: Some("coro:0".to_string()),
                kind: "dependent_work".to_string(),
                phase: OperationPhase::Blocked,
                handler_identity: Some("host/runtime".to_string()),
                effect_ids: vec![21],
                dependent_operation_ids: Vec::new(),
                terminal_publication: Some("effect.blocked".to_string()),
                budget_ticks: Some(1),
                requires_proof: false,
            },
            &machine.config.observability_retention,
        );

        let receipt = delegation_receipt(
            8,
            Endpoint {
                sid: 8,
                role: "A".to_string(),
            },
            0,
            1,
        );
        machine.apply_semantic_handoff_obligations(&receipt);
        machine.delegation_audit_log.push(
            DelegationAuditRecord {
                tick: machine.clock.tick,
                receipt,
                status: DelegationStatus::Committed,
                reason: Some("structure locality transfer".to_string()),
            },
            &machine.config.observability_retention,
        );

        let semantic_objects = machine.semantic_objects();
        let region = semantic_objects
            .regions
            .iter()
            .find(|region| region.session == Some(8))
            .expect("handoff should retain one region view");
        assert_eq!(region.region_id, "session:8");
        assert_eq!(region.scope, crate::semantic_objects::OwnershipScope::Session);
        assert_eq!(
            region.owner_id.as_deref(),
            Some("coro:1"),
            "region ownership should move to the activated owner",
        );
        assert!(
            region.operation_ids.iter().any(|id| id == "effect:21"),
            "region should retain blocked dependent-work operation identity",
        );
        assert!(
            region.operation_ids.iter().any(|id| id == "handoff:8"),
            "region should retain the structural handoff operation identity",
        );
        assert_eq!(region.effect_ids, vec![21]);
        assert!(
            semantic_objects
                .transformation_obligations
                .iter()
                .any(|obligation| {
                    obligation.handoff_id == 8
                        && obligation.transformed_fragments == vec!["A".to_string()]
                }),
            "handoff should export one structural transformation obligation bundle",
        );
        assert!(
            semantic_objects
                .publication_events
                .iter()
                .any(|publication| publication.operation_id == "handoff:8"),
            "handoff locality transfer should publish one canonical structural event",
        );
    }

    #[test]
    fn runtime_progress_contract_escalates_and_invalidates_late_results() {
        let mut machine = test_vm();
        machine.clock.tick = 1;
        let effect_id = machine.issue_runtime_effect(
            "invoke_step",
            Some(7),
            "host/runtime",
            serde_json::json!({ "session": 7 }),
        );

        machine.clock.tick = 2;
        machine.evaluate_progress_contracts()
            .expect("blocked escalation should succeed");
        assert!(matches!(
            machine.progress_contracts
                .as_slice()
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::Blocked
        ));

        machine.clock.tick = 3;
        machine.evaluate_progress_contracts()
            .expect("no-progress escalation should succeed");
        assert!(matches!(
            machine.progress_contracts
                .as_slice()
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::NoProgress
        ));

        machine.clock.tick = 4;
        machine.evaluate_progress_contracts()
            .expect("degraded escalation should succeed");
        assert!(matches!(
            machine.progress_contracts
                .as_slice()
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::Degraded
        ));

        machine.clock.tick = 5;
        machine.evaluate_progress_contracts()
            .expect("timeout escalation should succeed");
        let contract = machine
            .progress_contracts
            .as_slice()
            .iter()
            .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
            .expect("progress contract");
        assert_eq!(contract.state, ProgressState::TimedOut);
        assert_eq!(
            contract.reason.as_deref(),
            Some("bounded wait exhausted; late results are invalid")
        );
        let effect = machine
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == effect_id)
            .expect("effect");
        assert_eq!(effect.status, OutstandingEffectStatus::Invalidated);

        let err = machine
            .complete_runtime_effect(
                effect_id,
                OutstandingEffectStatus::Succeeded,
                serde_json::json!({ "status": "success" }),
            )
            .expect_err("late timeout result must be rejected");
        assert!(err.to_string().contains("late result"));
    }

    #[test]
    fn runtime_progress_contract_requires_bounded_waits() {
        let mut machine = test_vm();
        machine.clock.tick = 1;
        let effect_id = machine.issue_runtime_effect(
            "invoke_step",
            Some(9),
            "host/runtime",
            serde_json::json!({ "session": 9 }),
        );
        let operation_id = format!("effect:{effect_id}");
        machine.outstanding_effects
            .as_mut_slice()
            .iter_mut()
            .find(|effect| effect.effect_id == effect_id)
            .expect("effect")
            .budget_ticks = None;
        let contract = machine
            .progress_contracts
            .as_mut_slice()
            .iter_mut()
            .find(|contract| contract.operation_id == operation_id)
            .expect("progress contract");
        contract.budget_ticks = None;
        contract.bounded = false;

        machine.clock.tick = 2;
        let err = machine
            .evaluate_progress_contracts()
            .expect_err("unbounded semantic-path effect must be rejected");
        assert!(err.to_string().contains("bounded wait budget"));
    }

    #[test]
    fn runtime_semantic_lifecycle_harness_covers_seeded_state_machine_paths() {
        let scenarios = lifecycle_scenarios();
        let mut covered_actions = BTreeSet::new();

        for scenario in &scenarios {
            let mut harness = LifecycleHarness::new(scenario.seed);
            harness.run_scenario(scenario);
            covered_actions.extend(harness.action_counts.keys().copied());
            assert!(
                !harness.late_result_rejections.is_empty()
                    || scenario
                        .actions
                        .iter()
                        .all(|action| !matches!(action, LifecycleAction::DuplicateCompletion)),
                "{}",
                harness.context("duplicate-completion scenarios must record a late-result rejection"),
            );
        }

        for scenario in adversarial_scenarios() {
            let mut harness = LifecycleHarness::new(scenario.seed);
            harness.run_scenario(&scenario);
            covered_actions.extend(harness.action_counts.keys().copied());
        }

        let expected_actions = [
            LifecycleAction::OpenOwnedSession,
            LifecycleAction::IssueEffect,
            LifecycleAction::CompleteEffect,
            LifecycleAction::DuplicateCompletion,
            LifecycleAction::LateCancel,
            LifecycleAction::InvalidateSession,
            LifecycleAction::TimeoutEffect,
            LifecycleAction::CancelEffect,
            LifecycleAction::Handoff,
            LifecycleAction::OwnerCrash,
            LifecycleAction::PublicationWithoutProof,
            LifecycleAction::DuplicatePublication,
            LifecycleAction::MaterializeSuccess,
            LifecycleAction::BindCanonicalHandle,
            LifecycleAction::RejectObservedRead,
            LifecycleAction::RequireMissingCanonicalHandle,
            LifecycleAction::ImmediateEffectMisuse,
            LifecycleAction::ReplaySemanticObjects,
        ];
        for action in expected_actions {
            assert!(
                covered_actions.contains(action.name()),
                "seeded lifecycle corpus must cover action `{}`",
                action.name(),
            );
        }
    }

    #[test]
    fn runtime_semantic_lifecycle_adversarial_corpus_is_deterministic() {
        for scenario in adversarial_scenarios() {
            let mut harness = LifecycleHarness::new(scenario.seed);
            harness.run_scenario(&scenario);
            assert_eq!(
                harness.action_log.len(),
                scenario.actions.len(),
                "{}",
                harness.context("adversarial corpus should produce a stable replay artifact"),
            );
        }
    }
}
