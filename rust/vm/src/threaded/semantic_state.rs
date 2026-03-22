impl ThreadedVM {
    fn ensure_effect_request_allowed(&self, request: &EffectRequest) -> Result<(), EffectFailure> {
        request.metadata.validate()?;
        match request.metadata.reentrancy_policy {
            crate::effect::EffectReentrancyPolicy::Allow => {}
            crate::effect::EffectReentrancyPolicy::RejectSameOperation => {
                if let Some(operation_id) = &request.operation_id {
                    if self.outstanding_effects.iter().any(|effect| {
                        effect.operation_id == *operation_id
                            && matches!(
                                effect.status,
                                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
                            )
                    }) {
                        return Err(EffectFailure::contract_violation(format!(
                            "reentrancy rejected for operation `{operation_id}`"
                        )));
                    }
                }
            }
            crate::effect::EffectReentrancyPolicy::RejectSameFragment => {
                if let Some(session) = request.session {
                    if self.outstanding_effects.iter().any(|effect| {
                        effect.session == Some(session)
                            && matches!(
                                effect.status,
                                OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
                            )
                    }) {
                        return Err(EffectFailure::contract_violation(format!(
                            "reentrancy rejected for session fragment `{session}`"
                        )));
                    }
                }
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
        self.effect_exchanges.push(EffectExchangeRecord {
            effect_id,
            handler_identity: handler_identity.to_string(),
            ordering_key: self.clock.tick,
            request,
            outcome: outcome.clone(),
        });
    }

    fn current_operation_owner(&self, session: Option<SessionId>) -> Option<String> {
        session.and_then(|sid| {
            self.sessions
                .get(sid)
                .and_then(|session| {
                    let session = session.lock().ok()?;
                    session
                        .ownership()
                        .current
                        .as_ref()
                        .map(|capability| capability.owner_id.clone())
                })
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

    #[allow(dead_code)]
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

        self.outstanding_effects.push(OutstandingEffect {
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
        });
        self.operation_instances.push(OperationInstance {
            operation_id,
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
        });
        effect_id
    }

    fn sync_runtime_effect_from_trace_entry(&mut self, entry: &EffectTraceEntry) {
        if self
            .outstanding_effects
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
        let status = match entry.outputs.get("status").and_then(serde_json::Value::as_str) {
            Some("blocked") => OutstandingEffectStatus::Blocked,
            Some("failure") => OutstandingEffectStatus::Failed,
            Some("cancelled") => OutstandingEffectStatus::Cancelled,
            Some("invalidated") => OutstandingEffectStatus::Invalidated,
            _ => OutstandingEffectStatus::Succeeded,
        };
        let budget_ticks = Some(1);

        self.outstanding_effects.push(OutstandingEffect {
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
        });
        self.operation_instances.push(OperationInstance {
            operation_id,
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
        });
    }

    #[allow(dead_code)]
    fn complete_runtime_effect(
        &mut self,
        effect_id: u64,
        status: OutstandingEffectStatus,
        outputs: serde_json::Value,
    ) -> Result<(), VMError> {
        let Some(effect) = self
            .outstanding_effects
            .iter_mut()
            .find(|effect| effect.effect_id == effect_id)
        else {
            return Err(VMError::HandlerError(EffectFailure::contract_violation(
                format!(
                    "[host-contract] completion for effect {effect_id} requires a live outstanding-effect record"
                ),
            )));
        };
        if !matches!(
            effect.status,
            OutstandingEffectStatus::Pending | OutstandingEffectStatus::Blocked
        ) {
            return Err(VMError::HandlerError(EffectFailure::contract_violation(
                format!(
                    "[host-contract] late result for effect {effect_id} rejected after {:?}",
                    effect.status
                ),
            )));
        }
        effect.status = status;
        effect.outputs = outputs;
        effect.completed_at_tick = Some(self.clock.tick);
        effect.ordering_key = self.clock.tick;

        if let Some(operation) = self
            .operation_instances
            .iter_mut()
            .find(|operation| operation.operation_id == effect.operation_id)
        {
            operation.phase = Self::effect_status_phase(status);
            operation.terminal_publication = Self::effect_terminal_publication(status);
        }
        Ok(())
    }

    fn invalidate_outstanding_effects_for_session(&mut self, session: SessionId, reason: &str) {
        let mut invalidated = Vec::new();
        for effect in &mut self.outstanding_effects {
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

        for operation in &mut self.operation_instances {
            if invalidated.iter().any(|operation_id| operation.operation_id == *operation_id) {
                operation.phase = OperationPhase::Failed;
                operation.terminal_publication = Some("effect.invalidated".to_string());
            }
        }
    }
}
