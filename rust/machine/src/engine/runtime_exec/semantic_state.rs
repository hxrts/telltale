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

    fn test_vm() -> ProtocolMachine {
        ProtocolMachine::new(ProtocolMachineConfig::default())
    }

    #[test]
    fn runtime_reentrancy_rejects_same_operation_requests() {
        let mut vm = test_vm();
        vm.outstanding_effects.push(
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
            &vm.config.observability_retention,
        );

        let mut request =
            EffectRequest::invoke_step(5, Some(7), Some("effect:1".to_string()), "A", &[]);
        request.metadata.reentrancy_policy =
            crate::effect::EffectReentrancyPolicy::RejectSameOperation;

        let err = vm
            .ensure_effect_request_allowed(&request)
            .expect_err("same operation reentrancy must fail");
        assert!(err.message.contains("reentrancy rejected"));
    }

    #[test]
    fn runtime_reentrancy_rejects_same_fragment_requests() {
        let mut vm = test_vm();
        vm.outstanding_effects.push(
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
            &vm.config.observability_retention,
        );

        let mut request =
            EffectRequest::acquire(6, 9, Some("effect:3".to_string()), "A", "Guard", &[]);
        request.metadata.reentrancy_policy =
            crate::effect::EffectReentrancyPolicy::RejectSameFragment;

        let err = vm
            .ensure_effect_request_allowed(&request)
            .expect_err("same fragment reentrancy must fail");
        assert!(err.message.contains("footprint session:9"));
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn runtime_semantic_handoff_transfers_pending_effects_and_invalidates_blocked_effects() {
        let mut vm = test_vm();
        vm.clock.tick = 7;
        vm.outstanding_effects.push(
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
            &vm.config.observability_retention,
        );
        vm.outstanding_effects.push(
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
            &vm.config.observability_retention,
        );
        vm.operation_instances.push(
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
            &vm.config.observability_retention,
        );
        vm.operation_instances.push(
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
            &vm.config.observability_retention,
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
        vm.apply_semantic_handoff_obligations(&receipt);

        let pending = vm
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == 11)
            .expect("pending effect");
        assert_eq!(pending.owner_id.as_deref(), Some("coro:1"));
        assert_eq!(pending.status, OutstandingEffectStatus::Pending);

        let blocked = vm
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == 12)
            .expect("blocked effect");
        assert_eq!(blocked.owner_id.as_deref(), Some("coro:1"));
        assert_eq!(blocked.status, OutstandingEffectStatus::Invalidated);

        let err = vm
            .complete_runtime_effect(
                12,
                OutstandingEffectStatus::Succeeded,
                serde_json::json!({ "status": "success" }),
            )
            .expect_err("stale post-handoff result must be rejected");
        assert!(err.to_string().contains("late result"));
    }

    #[test]
    fn runtime_progress_contract_escalates_and_invalidates_late_results() {
        let mut vm = test_vm();
        vm.clock.tick = 1;
        let effect_id = vm.issue_runtime_effect(
            "invoke_step",
            Some(7),
            "host/runtime",
            serde_json::json!({ "session": 7 }),
        );

        vm.clock.tick = 2;
        vm.evaluate_progress_contracts()
            .expect("blocked escalation should succeed");
        assert!(matches!(
            vm.progress_contracts
                .as_slice()
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::Blocked
        ));

        vm.clock.tick = 3;
        vm.evaluate_progress_contracts()
            .expect("no-progress escalation should succeed");
        assert!(matches!(
            vm.progress_contracts
                .as_slice()
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::NoProgress
        ));

        vm.clock.tick = 4;
        vm.evaluate_progress_contracts()
            .expect("degraded escalation should succeed");
        assert!(matches!(
            vm.progress_contracts
                .as_slice()
                .iter()
                .find(|contract| contract.operation_id == format!("effect:{effect_id}"))
                .expect("progress contract")
                .state,
            ProgressState::Degraded
        ));

        vm.clock.tick = 5;
        vm.evaluate_progress_contracts()
            .expect("timeout escalation should succeed");
        let contract = vm
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
        let effect = vm
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == effect_id)
            .expect("effect");
        assert_eq!(effect.status, OutstandingEffectStatus::Invalidated);

        let err = vm
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
        let mut vm = test_vm();
        vm.clock.tick = 1;
        let effect_id = vm.issue_runtime_effect(
            "invoke_step",
            Some(9),
            "host/runtime",
            serde_json::json!({ "session": 9 }),
        );
        let operation_id = format!("effect:{effect_id}");
        vm.outstanding_effects
            .as_mut_slice()
            .iter_mut()
            .find(|effect| effect.effect_id == effect_id)
            .expect("effect")
            .budget_ticks = None;
        let contract = vm
            .progress_contracts
            .as_mut_slice()
            .iter_mut()
            .find(|contract| contract.operation_id == operation_id)
            .expect("progress contract");
        contract.budget_ticks = None;
        contract.bounded = false;

        vm.clock.tick = 2;
        let err = vm
            .evaluate_progress_contracts()
            .expect_err("unbounded semantic-path effect must be rejected");
        assert!(err.to_string().contains("bounded wait budget"));
    }
}
