// Commit finalization and endpoint delegation for threaded mode.
impl ThreadedProtocolMachine {
    fn record_effect_observations(
        &mut self,
        observations: Vec<EffectObservation>,
        handler_identity: &str,
    ) -> Result<(), EffectFailure> {
        for observation in observations {
            let predicted_effect_id = match &observation.request.body {
                crate::effect::EffectRequestBody::NominalCommand { request } => request.invocation,
                _ => self.next_effect_id,
            };
            self.record_effect_exchange(
                &observation.request,
                &observation.outcome,
                handler_identity,
                predicted_effect_id,
            )?;
            if let crate::effect::EffectRequestBody::NominalCommand { request } =
                &observation.request.body
            {
                use crate::effect::EffectOutcomeStatus;
                let validation = self
                    .coroutine_indexes
                    .get(&request.coroutine)
                    .and_then(|index| self.coroutines.get(*index))
                    .and_then(|coro| {
                        coro.lock()
                            .expect("threaded ProtocolMachine lock poisoned")
                            .nominal_continuation
                            .as_ref()
                            .and_then(|pending| pending.validation_failure.clone())
                    });
                let accepted = observation
                    .outcome
                    .accepted_status(&observation.request.body);
                let status = if validation.is_some() {
                    Some(OutstandingEffectStatus::Failed)
                } else {
                    match &accepted {
                        EffectOutcomeStatus::Failure { .. } => {
                            Some(OutstandingEffectStatus::Failed)
                        }
                        EffectOutcomeStatus::Blocked if !request.declaration.may_block => {
                            Some(OutstandingEffectStatus::Failed)
                        }
                        EffectOutcomeStatus::Blocked
                            if self.outstanding_effects.iter().any(|effect| {
                                effect.effect_id == predicted_effect_id
                                    && effect.status == OutstandingEffectStatus::Pending
                            }) =>
                        {
                            Some(OutstandingEffectStatus::Blocked)
                        }
                        _ => None,
                    }
                };
                if let Some(status) = status {
                    let outputs = if let Some(validation) = validation {
                        match accepted {
                            EffectOutcomeStatus::Failure { failure } => {
                                json!({"status":"failure", "failure":failure, "independent_validation":validation, "raw_outcome":observation.outcome})
                            }
                            _ => {
                                json!({"status":"failure", "failure":validation, "raw_outcome":observation.outcome})
                            }
                        }
                    } else if matches!(&accepted, EffectOutcomeStatus::Blocked)
                        && !request.declaration.may_block
                    {
                        json!({"status":"failure", "failure":EffectFailure::contract_violation("immediate nominal command returned Blocked"), "raw_outcome":observation.outcome})
                    } else {
                        serde_json::to_value(&observation.outcome)
                            .expect("typed nominal outcome serializes")
                    };
                    self.complete_runtime_effect(predicted_effect_id, status, outputs)
                        .expect("main owner retains the pre-issued live nominal occurrence during its worker wave");
                }
            }
        }
        Ok(())
    }

    fn issue_delegation_receipt(
        &mut self,
        endpoint: Endpoint,
        from_coro: usize,
        to_coro: usize,
    ) -> DelegationReceipt {
        let receipt = delegation_receipt(
            self.next_delegation_receipt_id,
            endpoint,
            from_coro,
            to_coro,
        );
        self.next_delegation_receipt_id = self.next_delegation_receipt_id.saturating_add(1);
        receipt
    }

    fn record_delegation_audit(
        &mut self,
        receipt: DelegationReceipt,
        status: DelegationStatus,
        reason: Option<String>,
    ) {
        self.delegation_audit_log.push(DelegationAuditRecord {
            tick: self.clock.tick,
            receipt,
            status,
            reason,
        });
    }

    fn intern_edge(&mut self, edge: &Edge) -> EdgeId {
        let sender = self.role_symbols.intern(&edge.sender);
        let receiver = self.role_symbols.intern(&edge.receiver);
        self.edge_symbols.intern(edge.sid, sender, receiver)
    }

    fn intern_session_runtime_symbols(&mut self, sid: SessionId) {
        let Some(session) = self.sessions.get(sid) else {
            return;
        };
        let session_guard = session
            .lock()
            .expect("threaded ProtocolMachine lock poisoned");
        let roles = session_guard.roles.clone();
        let default_handler = session_guard.default_handler.clone();
        let handler_bindings: Vec<(Edge, String)> = session_guard
            .edge_handlers
            .iter()
            .map(|(edge, handler_id)| (edge.clone(), handler_id.clone()))
            .collect();
        drop(session_guard);
        for role in roles {
            let _: StringId = self.role_symbols.intern(&role);
        }
        let _: StringId = self.handler_symbols.intern(&default_handler);
        for (edge, handler_id) in handler_bindings {
            let _: EdgeId = self.intern_edge(&edge);
            let _: StringId = self.handler_symbols.intern(&handler_id);
        }
    }

    #[allow(clippy::too_many_lines)]
    fn commit_pack(
        &mut self,
        coro: &Arc<Mutex<Coroutine>>,
        session: &Arc<Mutex<SessionState>>,
        pack: StepPack,
        effect_observations: Vec<EffectObservation>,
        output_observation: Option<OutputHintObservation>,
        handler: &dyn EffectHandler,
        handler_identity: &str,
    ) -> Result<ExecOutcome, Fault> {
        let coro_id = coro
            .lock()
            .expect("threaded ProtocolMachine lock poisoned")
            .id;
        let sid = session
            .lock()
            .expect("threaded ProtocolMachine lock poisoned")
            .sid;

        self.record_effect_observations(effect_observations, handler_identity)
            .map_err(|failure| Fault::Invoke { failure })?;

        let output_hint = if let Some(observation) = output_observation {
            self.ensure_effect_request_allowed(&observation.request)
                .map_err(|failure| Fault::Invoke { failure })?;
            let predicted_effect_id = self.next_effect_id;
            self.record_effect_exchange(
                &observation.request,
                &observation.outcome,
                handler_identity,
                predicted_effect_id,
            )
            .map_err(|failure| Fault::Invoke { failure })?;
            observation.hint
        } else {
            None
        };

        let derived = crate::commit_common::derived_effect_count(&pack.events)
            .map_err(|failure| Fault::Invoke { failure })?;
        let needs_wal = !pack.events.is_empty()
            && !matches!(
                self.config.output_condition_policy,
                crate::output_condition::OutputConditionPolicy::Disabled
            )
            && handler.supports_wal_sync();
        let remaining = derived
            .checked_add(u64::from(needs_wal))
            .ok_or_else(|| Fault::Invoke {
                failure: EffectFailure::contract_violation(
                    "canonical effect occurrence identifiers exhausted",
                ),
            })?;
        crate::commit_common::require_effect_capacity(self.next_effect_id, remaining)
            .map_err(|failure| Fault::Invoke { failure })?;
        if needs_wal {
            let sync = self.current_wal_sync_request(Some(sid), coro_id);
            let request = EffectRequest::wal_sync(self.clock.tick, sync.operation_id.clone(), sync);
            self.ensure_effect_request_allowed(&request)
                .map_err(|failure| Fault::Invoke { failure })?;
            let predicted_effect_id = self.next_effect_id;
            let outcome = handler.handle_effect(request.clone());
            self.record_effect_exchange(&request, &outcome, handler_identity, predicted_effect_id)
                .map_err(|failure| Fault::Invoke { failure })?;
            match outcome.into_unit("wal_sync") {
                Ok(EffectResult::Success(())) => {}
                Ok(EffectResult::Blocked) => {
                    return Ok(ExecOutcome::Blocked(BlockReason::Invoke {
                        handler: handler_identity.to_string(),
                    }));
                }
                Ok(EffectResult::Failure(failure)) | Err(failure) => {
                    return Err(Fault::Invoke { failure });
                }
            }
        }

        if !pack.events.is_empty() {
            apply_output_condition_gate(
                &self.config.output_condition_policy,
                |check| self.output_condition_checks.push(check),
                |event| self.trace.push(event),
                self.clock.tick,
                output_hint,
            )?;
        }

        if matches!(&pack.coro_update, CoroUpdate::CompleteNominal) {
            // Last foreign identity observation occurs outside capsule locks,
            // before either the accepted result or a derived success is published.
            let final_handler_identity = handler.handler_identity();
            self.validate_nominal_commit(coro, session, &final_handler_identity)?;
            self.commit_nominal_result(coro, session, &final_handler_identity)?;
        }

        if let CoroUpdate::OperationLifecycle(action) = &pack.coro_update {
            let mut original = coro.lock().expect("threaded ProtocolMachine lock poisoned");
            let resident_session = session
                .lock()
                .expect("threaded ProtocolMachine lock poisoned");
            let execution = crate::operation_lifecycle::execute_operation_action(
                &mut original,
                &resident_session,
                &mut self.operation_instances,
                &mut self.progress_contracts,
                &mut self.outstanding_effects,
                self.clock.tick,
                action.clone(),
            )
            .map_err(crate::operation_lifecycle::transition_fault)?;
            match execution {
                crate::operation_lifecycle::OperationExecution::AwaitPending => {
                    original.status = CoroStatus::Blocked(BlockReason::OperationAwait {
                        operation_id: original
                            .operation_continuation
                            .as_ref()
                            .expect("validated original operation")
                            .operation_id
                            .clone(),
                    });
                }
                execution => {
                    if let crate::operation_lifecycle::OperationExecution::Begun(record, progress) =
                        execution
                    {
                        self.operation_instances.push(record);
                        self.progress_contracts.push(progress);
                    }
                    original.pc += 1;
                    original.status = CoroStatus::Ready;
                }
            }
        }

        for ev in &pack.events {
            self.intern_obs_event(ev);
            if let ObsEvent::Opened { session, .. } = ev {
                self.intern_session_runtime_symbols(*session);
            }
            let maybe_entry = effect_trace_entry_for_event(
                ev,
                self.next_effect_id,
                handler_identity,
                self.clock.tick,
            );
            if let Some(entry) = maybe_entry {
                self.sync_runtime_effect_from_trace_entry(&entry);
                if self.should_capture_effect_kind(&entry.effect_kind) {
                    self.effect_trace.push(entry);
                }
                self.next_effect_id =
                    self.next_effect_id
                        .checked_add(1)
                        .ok_or_else(|| Fault::Invoke {
                            failure: EffectFailure::contract_violation(
                                "canonical effect occurrence identifiers exhausted",
                            ),
                        })?;
            }
        }

        let mut coro_guard = coro.lock().expect("threaded ProtocolMachine lock poisoned");
        let was_terminal = coro_guard.is_terminal();

        match pack.coro_update {
            CoroUpdate::CompleteNominal | CoroUpdate::OperationLifecycle(_) => {}
            CoroUpdate::AdvancePc => {
                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
            CoroUpdate::SetPc(pc) => {
                coro_guard.pc = pc;
                coro_guard.status = CoroStatus::Ready;
            }
            CoroUpdate::Block(ref reason) => {
                coro_guard.status = CoroStatus::Blocked(reason.clone());
            }
            CoroUpdate::Halt => {
                coro_guard.status = CoroStatus::Done;
            }
            CoroUpdate::AdvancePcWriteReg { reg, ref val } => {
                write_coro_reg(&mut coro_guard, reg, val.clone())?;
                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
            CoroUpdate::AdvancePcSpawnChild { target, ref args } => {
                if self.coroutines.len() >= self.config.max_coroutines {
                    return Err(Fault::Speculation {
                        message: "max coroutines exceeded".to_string(),
                    });
                }
                let new_id = self.next_coro_id;
                self.next_coro_id = self.next_coro_id.saturating_add(1);

                let mut child = Coroutine::new(
                    new_id,
                    coro_guard.program_id,
                    coro_guard.session_id,
                    coro_guard.role.clone(),
                    self.config.num_registers,
                    self.config.initial_cost_budget,
                );
                child.pc = target;
                child.effect_ctx = coro_guard.effect_ctx.clone();
                for (dst_idx, src_reg) in args.iter().enumerate() {
                    if dst_idx >= child.regs.len() {
                        break;
                    }
                    if let Some(value) = coro_guard.regs.get(usize::from(*src_reg)).cloned() {
                        child.regs[dst_idx] = value;
                    }
                }
                self.scheduler.add_ready(new_id);
                self.coroutine_indexes.insert(new_id, self.coroutines.len());
                self.coroutines.push(Arc::new(Mutex::new(child)));
                self.non_terminal_coroutines = self.non_terminal_coroutines.saturating_add(1);

                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
        }
        let is_terminal = coro_guard.is_terminal();
        self.note_status_transition(was_terminal, is_terminal);

        if let Some((ep, update)) = pack.type_update {
            let mut session_guard = session
                .lock()
                .expect("threaded ProtocolMachine lock poisoned");
            match update {
                TypeUpdate::Advance(lt) => {
                    if let Some(entry) = session_guard.local_types.get_mut(&ep) {
                        entry.current = lt;
                    }
                }
                TypeUpdate::AdvanceWithOriginal(lt, orig) => {
                    if let Some(entry) = session_guard.local_types.get_mut(&ep) {
                        entry.current = lt;
                        entry.original = orig;
                    }
                }
                TypeUpdate::Remove => {
                    session_guard.local_types.remove(&ep);
                }
            }
        }

        let transfer = pack.events.iter().find_map(|event| match event {
            ObsEvent::Transferred {
                session,
                role,
                from,
                to,
                ..
            } => Some((
                Endpoint {
                    sid: *session,
                    role: role.clone(),
                },
                *from,
                *to,
            )),
            _ => None,
        });

        if let Some((endpoint, from_id, _to_id)) = &transfer {
            if *from_id != coro_guard.id {
                return Err(Fault::Transfer {
                    message: "transfer source mismatch".into(),
                });
            }
            if !coro_guard.owned_endpoints.contains(endpoint) {
                return Err(Fault::Transfer {
                    message: "endpoint not owned".into(),
                });
            }
        }

        drop(coro_guard);
        if let Some((endpoint, from_id, to_id)) = transfer {
            self.enqueue_handoff(endpoint, from_id, to_id, self.clock.tick)?;
            self.apply_handoffs_deterministically()?;
        }

        self.assert_delegation_events_audited(&pack.events)
            .map_err(|err: ProtocolMachineError| Fault::Invoke {
                failure: EffectFailure::contract_violation(err.to_string()),
            })?;

        self.trace.extend(pack.events);
        let coro_guard = coro.lock().expect("threaded ProtocolMachine lock poisoned");

        match &coro_guard.status {
            CoroStatus::Ready => Ok(ExecOutcome::Continue),
            CoroStatus::Blocked(reason) => Ok(ExecOutcome::Blocked(reason.clone())),
            CoroStatus::Done => Ok(ExecOutcome::Halted),
            CoroStatus::Faulted(f) => Err(f.clone()),
            CoroStatus::Speculating => Ok(ExecOutcome::Continue),
        }
    }

    fn intern_obs_event(&mut self, ev: &ObsEvent) {
        match ev {
            ObsEvent::Sent {
                from, to, label, ..
            }
            | ObsEvent::Received {
                from, to, label, ..
            } => {
                let _: StringId = self.role_symbols.intern(from);
                let _: StringId = self.role_symbols.intern(to);
                let _: StringId = self.label_symbols.intern(label);
            }
            ObsEvent::Offered { edge, label, .. } | ObsEvent::Chose { edge, label, .. } => {
                let _: EdgeId = self.intern_edge(edge);
                let _: StringId = self.label_symbols.intern(label);
            }
            ObsEvent::Opened { roles, .. } => {
                for role in roles {
                    let _: StringId = self.role_symbols.intern(role);
                }
            }
            ObsEvent::Invoked { role, .. }
            | ObsEvent::Tagged { role, .. }
            | ObsEvent::Checked { role, .. }
            | ObsEvent::Transferred { role, .. } => {
                let _: StringId = self.role_symbols.intern(role);
            }
            _ => {}
        }
    }

    fn enqueue_handoff(
        &mut self,
        endpoint: Endpoint,
        from_coro: usize,
        to_coro: usize,
        tick: u64,
    ) -> Result<(), Fault> {
        self.assert_delegation_handoff_owner(&endpoint, from_coro)?;
        let source_arc = self
            .coroutine_by_id(from_coro)
            .cloned()
            .ok_or(Fault::Transfer {
                message: "transfer source coroutine not found".into(),
            })?;
        let target_arc = self
            .coroutine_by_id(to_coro)
            .cloned()
            .ok_or(Fault::Transfer {
                message: "target coroutine not found".into(),
            })?;
        {
            let source = source_arc
                .lock()
                .expect("threaded ProtocolMachine lock poisoned");
            let target = target_arc
                .lock()
                .expect("threaded ProtocolMachine lock poisoned");
            validate_delegation_coherence(&source, &target, &endpoint, &source.role)?;
        }
        let from_lane = self.lane_of_coro(from_coro).ok_or(Fault::Transfer {
            message: "transfer source coroutine not found".into(),
        })?;
        let to_lane = self.lane_of_coro(to_coro).ok_or(Fault::Transfer {
            message: "target coroutine not found".into(),
        })?;
        if from_lane != to_lane {
            self.contention_metrics.cross_lane_transfer_count = self
                .contention_metrics
                .cross_lane_transfer_count
                .saturating_add(1);
        }
        let handoff = LaneHandoff {
            handoff_id: self.next_handoff_id,
            tick,
            session: endpoint.sid,
            endpoint_role: endpoint.role.clone(),
            from_coro,
            to_coro,
            from_lane,
            to_lane,
            receipt: self.issue_delegation_receipt(endpoint, from_coro, to_coro),
        };
        self.next_handoff_id = self.next_handoff_id.saturating_add(1);
        self.pending_handoffs.push_back(handoff.clone());
        self.handoff_trace_log.push(handoff);
        Ok(())
    }

    fn apply_handoffs_deterministically(&mut self) -> Result<(), Fault> {
        while let Some(handoff) = self.pending_handoffs.pop_front() {
            self.apply_handoff(&handoff)?;
            let endpoint = Endpoint {
                sid: handoff.session,
                role: handoff.endpoint_role.clone(),
            };
            let expected_owner = if handoff.from_coro == handoff.to_coro {
                handoff.from_coro
            } else {
                handoff.to_coro
            };
            self.assert_delegation_handoff_owner(&endpoint, expected_owner)?;
            self.contention_metrics.handoff_applied_count = self
                .contention_metrics
                .handoff_applied_count
                .saturating_add(1);
        }
        Ok(())
    }

    fn apply_handoff(&mut self, handoff: &LaneHandoff) -> Result<(), Fault> {
        let endpoint = handoff.receipt.endpoint.clone();
        if handoff.from_coro == handoff.to_coro {
            let source_arc =
                self.coroutine_by_id(handoff.from_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "transfer source coroutine not found".into(),
                    })?;
            let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
            let source_before = source.clone();
            let result = move_endpoint_bundle(&endpoint, &mut source, None).and_then(|_| {
                drop(source);
                self.assert_delegation_handoff_owner(&endpoint, handoff.to_coro)
            });
            if let Err(err) = result {
                let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
                *source = source_before;
                self.record_delegation_audit(
                    handoff.receipt.clone(),
                    DelegationStatus::RolledBack,
                    Some(err.to_string()),
                );
                return Err(err);
            }
        } else {
            let source_arc =
                self.coroutine_by_id(handoff.from_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "transfer source coroutine not found".into(),
                    })?;
            let target_arc =
                self.coroutine_by_id(handoff.to_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "target coroutine not found".into(),
                    })?;

            // Global lock order: lower coroutine id first.
            if handoff.from_coro < handoff.to_coro {
                let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
                let mut target = lock_with_contention(&target_arc, &mut self.contention_metrics);
                validate_delegation_coherence(&source, &target, &endpoint, &source.role)?;
                let source_before = source.clone();
                let target_before = target.clone();
                let result = move_endpoint_bundle(&endpoint, &mut source, Some(&mut target))
                    .and_then(|_| {
                        drop(target);
                        drop(source);
                        self.assert_delegation_handoff_owner(&endpoint, handoff.to_coro)
                    });
                if let Err(err) = result {
                    let mut source =
                        lock_with_contention(&source_arc, &mut self.contention_metrics);
                    let mut target =
                        lock_with_contention(&target_arc, &mut self.contention_metrics);
                    *source = source_before;
                    *target = target_before;
                    self.record_delegation_audit(
                        handoff.receipt.clone(),
                        DelegationStatus::RolledBack,
                        Some(err.to_string()),
                    );
                    return Err(err);
                }
            } else {
                let mut target = lock_with_contention(&target_arc, &mut self.contention_metrics);
                let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
                validate_delegation_coherence(&source, &target, &endpoint, &source.role)?;
                let source_before = source.clone();
                let target_before = target.clone();
                let result = move_endpoint_bundle(&endpoint, &mut source, Some(&mut target))
                    .and_then(|_| {
                        drop(source);
                        drop(target);
                        self.assert_delegation_handoff_owner(&endpoint, handoff.to_coro)
                    });
                if let Err(err) = result {
                    let mut target =
                        lock_with_contention(&target_arc, &mut self.contention_metrics);
                    let mut source =
                        lock_with_contention(&source_arc, &mut self.contention_metrics);
                    *source = source_before;
                    *target = target_before;
                    self.record_delegation_audit(
                        handoff.receipt.clone(),
                        DelegationStatus::RolledBack,
                        Some(err.to_string()),
                    );
                    return Err(err);
                }
            }
        }
        self.record_delegation_audit(handoff.receipt.clone(), DelegationStatus::Committed, None);
        self.apply_semantic_handoff_obligations(&handoff.receipt);
        Ok(())
    }

    fn assert_delegation_handoff_owner(
        &self,
        endpoint: &Endpoint,
        expected_owner: usize,
    ) -> Result<(), Fault> {
        let mut owners = Vec::new();
        for coro in &self.coroutines {
            let guard = coro.lock().expect("threaded ProtocolMachine lock poisoned");
            if guard.owned_endpoints.contains(endpoint) {
                owners.push(guard.id);
            }
        }
        if owners == vec![expected_owner] {
            return Ok(());
        }
        // Intentional discard: values available for debugging but not in error message.
        let _ = (endpoint, owners, expected_owner);
        Err(transfer_fault_delegation_guard_violation("for handoff"))
    }
}
