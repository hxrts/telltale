struct RecvTypePlan {
    ep: Endpoint,
    sid: SessionId,
    partner: String,
    label: String,
    expected_type: Option<ValType>,
    continuation: LocalTypeR,
}

impl VM {
    fn recv_type_plan(
        &self,
        coro_idx: usize,
        role: &str,
        chan: u16,
    ) -> Result<RecvTypePlan, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed { endpoint: ep });
        }
        let sid = ep.sid;
        let local_type = self
            .sessions
            .lookup_type(&ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?
            .clone();
        let (partner, label, expected_type, continuation) = match &local_type {
            LocalTypeR::Recv {
                partner, branches, ..
            } => {
                let (label, expected_type, continuation) =
                    branches.first().ok_or_else(|| Fault::TypeViolation {
                        expected: telltale_types::ValType::Unit,
                        actual: telltale_types::ValType::Unit,
                        message: format!("{role}: recv has no branches"),
                    })?;
                (
                    partner.clone(),
                    label.name.clone(),
                    expected_type.clone(),
                    continuation.clone(),
                )
            }
            other => {
                return Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: expected Recv, got {other:?}"),
                });
            }
        };
        Ok(RecvTypePlan {
            ep,
            sid,
            partner,
            label,
            expected_type,
            continuation,
        })
    }

    fn recv_verified_signed_payload(
        &mut self,
        sid: SessionId,
        ep: &Endpoint,
        edge: &Edge,
        partner: &str,
        role: &str,
    ) -> Result<(Value, u64), Fault> {
        let session = self
            .sessions
            .get_mut(sid)
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
        let signed = session
            .recv_verified_signed(partner, role)
            .map_err(|message| Fault::VerificationFailed {
                edge: edge.clone(),
                message,
            })?
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
        Ok((signed.payload, signed.sequence_no))
    }

    fn consume_receive_replay_identity(
        &mut self,
        edge: &Edge,
        label: &str,
        expected_type: Option<&ValType>,
        val: &Value,
        sequence_no: u64,
    ) -> Result<(), Fault> {
        let replay_label =
            crate::communication_replay::canonical_receive_label_context(label, expected_type);
        let identity = crate::communication_replay::CommunicationIdentitySeed::new(
            edge,
            CommunicationStepKind::Receive,
            replay_label,
        )
        .build(val, sequence_no);
        self.consume_receive_identity(identity).map_err(|err| {
            let tag = err.tag();
            let message = match err {
                CommunicationReplayError::SequenceMismatch { expected, actual } => {
                    format!("{tag}: expected={expected}, actual={actual}")
                }
                CommunicationReplayError::DuplicateIdentity { .. } => tag.to_string(),
            };
            Fault::VerificationFailed {
                edge: edge.clone(),
                message,
            }
        })?;
        Ok(())
    }

    /// Recv: lookup type → match Recv → try dequeue → block or process → StepPack.
    pub(crate) fn step_recv(
        &mut self,
        coro_idx: usize,
        role: &str,
        chan: u16,
        dst_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let recv_plan = self.recv_type_plan(coro_idx, role, chan)?;
        let ep = recv_plan.ep;
        let sid = recv_plan.sid;
        let partner = recv_plan.partner;
        let label = recv_plan.label;
        let expected_type = recv_plan.expected_type;
        let continuation = recv_plan.continuation;
        let session = self.sessions.get(sid).ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
        if !session.has_message(&partner, role) {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::Recv {
                    edge: Edge::new(sid, partner, role.to_string()),
                    token: ProgressToken::for_endpoint(ep.clone()),
                }),
                type_update: None,
                events: vec![],
            });
        }

        let edge = Edge::new(sid, partner.clone(), role.to_string());
        let (val, sequence_no) =
            self.recv_verified_signed_payload(sid, &ep, &edge, &partner, role)?;
        self.consume_receive_replay_identity(&edge, &label, expected_type.as_ref(), &val, sequence_no)?;

        self.validate_payload(
            role,
            "receive",
            &label,
            expected_type.as_ref(),
            &val,
            true,
        )?;

        // Process via handler.
        let handler_identity = handler.handler_identity();
        let request = EffectRequest::receive(
            self.clock.tick,
            Some(sid),
            None,
            role,
            &partner,
            &label,
            &self.coroutines[coro_idx].regs,
            val.clone(),
        );
        self.ensure_effect_request_allowed(&request)
            .map_err(|failure| Fault::Invoke { failure })?;
        let predicted_effect_id = self.next_effect_id;
        let recv_outcome = handler.handle_effect(request.clone());
        self.record_effect_exchange(&request, &recv_outcome, &handler_identity, predicted_effect_id);
        if let Some(EffectResponse::Receive { state }) = recv_outcome.response.clone() {
            self.coroutines[coro_idx].regs = state;
        }
        match recv_outcome
            .into_unit("handle_recv")
            .unwrap_or_else(EffectResult::failure)
        {
            EffectResult::Success(()) => {}
            EffectResult::Blocked => {
                let effect_id = self.issue_runtime_effect(
                    "handle_recv",
                    Some(sid),
                    &handler_identity,
                    json!({
                        "session": sid,
                        "from": partner,
                        "to": role,
                        "label": label,
                    }),
                );
                let failure = EffectFailure::contract_violation("handle_recv returned blocked");
                self.complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Failed,
                    json!({
                        "status": "failure",
                        "failure": failure,
                    }),
                )
                .map_err(|err| Fault::Invoke {
                    failure: EffectFailure::contract_violation(err.to_string()),
                })?;
                return Err(Fault::Invoke { failure });
            }
            EffectResult::Failure(failure) => {
                let effect_id = self.issue_runtime_effect(
                    "handle_recv",
                    Some(sid),
                    &handler_identity,
                    json!({
                        "session": sid,
                        "from": partner,
                        "to": role,
                        "label": label,
                    }),
                );
                self.complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Failed,
                    json!({
                        "status": "failure",
                        "failure": failure,
                    }),
                )
                .map_err(|err| Fault::Invoke {
                    failure: EffectFailure::contract_violation(err.to_string()),
                })?;
                return Err(Fault::Invoke { failure });
            }
        }

        let original = self.sessions.original_type(&ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst_reg, val },
            type_update,
            events: vec![ObsEvent::Received {
                tick: self.clock.tick,
                edge: Edge::new(sid, partner.clone(), role.to_string()),
                session: sid,
                from: partner,
                to: role.to_string(),
                label,
            }],
        })
    }

    /// Halt: verify type is End → remove type entry.
    pub(crate) fn step_halt(&self, ep: &Endpoint) -> Result<StepPack, Fault> {
        // Optionally verify type is End (permissive in V1).
        if let Some(lt) = self.sessions.lookup_type(ep) {
            if !matches!(lt, LocalTypeR::End) {
                // V1: warn but allow. V2: fault.
            }
        }
        Ok(StepPack {
            coro_update: CoroUpdate::Halt,
            type_update: Some((ep.clone(), TypeUpdate::Remove)),
            events: vec![],
        })
    }

    /// Spawn: allocate a new ready coroutine with copied argument registers.
    pub(crate) fn step_spawn(
        &mut self,
        coro_idx: usize,
        target: PC,
        args: &[u16],
    ) -> Result<StepPack, Fault> {
        if self.coroutines.len() >= self.config.max_coroutines {
            return Err(Fault::Speculation {
                message: "max coroutines exceeded".to_string(),
            });
        }

        let parent = self.coroutines[coro_idx].clone();
        let new_id = self.next_coro_id;
        self.next_coro_id = self.next_coro_id.saturating_add(1);

        let mut child = Coroutine::new(
            new_id,
            parent.program_id,
            parent.session_id,
            parent.role.clone(),
            self.config.num_registers,
            self.config.initial_cost_budget,
        );
        child.pc = target;
        child.effect_ctx = parent.effect_ctx.clone();
        for (dst_idx, src_reg) in args.iter().enumerate() {
            if dst_idx >= child.regs.len() {
                break;
            }
            if let Some(value) = parent.regs.get(usize::from(*src_reg)).cloned() {
                child.regs[dst_idx] = value;
            }
        }

        self.role_coroutines
            .entry(child.role.clone())
            .or_default()
            .push(new_id);
        if self.paused_roles.contains(&child.role) {
            self.paused_coro_ids.insert(new_id);
        }
        if self.timed_out_sites.contains_key(&child.role) {
            self.timed_out_coro_ids.insert(new_id);
        }
        self.sched.add_ready(new_id);
        self.coroutines.push(child);
        self.coro_slots.insert(new_id, self.coroutines.len() - 1);
        self.sync_ready_eligibility_for(new_id);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![],
        })
    }

    /// Invoke: call handler.step() for integration.
    pub(crate) fn step_invoke(
        &mut self,
        coro_idx: usize,
        role: &str,
        action: InvokeAction,
        legacy_dst: Option<u16>,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let action_repr = match action {
            InvokeAction::Named(name) => name,
            InvokeAction::Reg(reg) => {
                let action_value = self.read_reg_checked(coro_idx, reg)?;
                format!("{action_value:?}")
            }
        };
        if let Some(dst) = legacy_dst {
            if usize::from(dst) >= self.coroutines[coro_idx].regs.len() {
                return Err(Fault::OutOfRegisters);
            }
        }
        let sid = self.coroutines[coro_idx].session_id;
        if self
            .sessions
            .default_handler_for_session(sid)
            .map_or(true, String::is_empty)
        {
            return Err(Fault::Invoke {
                failure: EffectFailure::contract_violation("no handler bound"),
            });
        }
        let coro_id = self.coroutines[coro_idx].id;
        let handler_identity = handler.handler_identity();
        let request = EffectRequest::invoke_step(
            self.clock.tick,
            Some(sid),
            None,
            role,
            &self.coroutines[coro_idx].regs,
        );
        self.ensure_effect_request_allowed(&request)
            .map_err(|failure| Fault::Invoke { failure })?;
        let predicted_effect_id = self.next_effect_id;
        let step_outcome = handler.handle_effect(request.clone());
        self.record_effect_exchange(&request, &step_outcome, &handler_identity, predicted_effect_id);
        if let Some(EffectResponse::InvokeStep { state }) = step_outcome.response.clone() {
            self.coroutines[coro_idx].regs = state;
        }
        match step_outcome
            .into_unit("invoke_step")
            .unwrap_or_else(EffectResult::failure)
        {
            EffectResult::Success(()) => {}
            EffectResult::Blocked => {
                let effect_id = self.issue_runtime_effect(
                    "invoke_step",
                    Some(sid),
                    &handler_identity,
                    json!({
                        "session": sid,
                        "role": role,
                        "action": action_repr,
                    }),
                );
                let failure = EffectFailure::contract_violation("step returned blocked");
                self.complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Failed,
                    json!({
                        "status": "failure",
                        "failure": failure,
                    }),
                )
                .map_err(|err| Fault::Invoke {
                    failure: EffectFailure::contract_violation(err.to_string()),
                })?;
                return Err(Fault::Invoke { failure });
            }
            EffectResult::Failure(failure) => {
                let effect_id = self.issue_runtime_effect(
                    "invoke_step",
                    Some(sid),
                    &handler_identity,
                    json!({
                        "session": sid,
                        "role": role,
                        "action": action_repr,
                    }),
                );
                self.complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Failed,
                    json!({
                        "status": "failure",
                        "failure": failure,
                    }),
                )
                .map_err(|err| Fault::Invoke {
                    failure: EffectFailure::contract_violation(err.to_string()),
                })?;
                return Err(Fault::Invoke { failure });
            }
        }
        self.apply_invoke_delta(sid, &action_repr)
            .map_err(|e| Fault::Invoke {
                failure: EffectFailure::contract_violation(format!(
                    "invoke persistence delta failed: {e}"
                )),
            })?;

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Invoked {
                tick: self.clock.tick,
                coro_id,
                role: role.to_string(),
            }],
        })
    }

    fn guard_active(&self, layer: &str) -> Result<(), Fault> {
        if self.config.guard_layers.is_empty() {
            return Ok(());
        }
        match self.config.guard_layers.iter().find(|cfg| cfg.id == layer) {
            None => Err(Fault::Acquire {
                layer: layer.to_string(),
                failure: EffectFailure::invalid_input("unknown layer"),
            }),
            Some(cfg) if !cfg.active => Err(Fault::Acquire {
                layer: layer.to_string(),
                failure: EffectFailure::unavailable("inactive layer"),
            }),
            Some(_) => Ok(()),
        }
    }

    pub(crate) fn step_acquire(
        &mut self,
        input: GuardAcquireInput<'_>,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        self.guard_active(input.layer)?;
        let layer_id = LayerId(input.layer.to_string());
        if self.guard_layer.resources.is_empty() {
            self.guard_layer
                .resources
                .insert(layer_id.clone(), Value::Unit);
        }
        self.guard_layer
            .open_(&layer_id)
            .map_err(|e| Fault::Acquire {
                layer: input.layer.to_string(),
                failure: EffectFailure::invalid_evidence(e),
            })?;
        let request = EffectRequest::acquire(
            self.clock.tick,
            input.sid,
            None,
            input.role,
            input.layer,
            &self.coroutines[input.coro_idx].regs,
        );
        self.ensure_effect_request_allowed(&request)
            .map_err(|failure| Fault::Acquire {
                layer: input.layer.to_string(),
                failure,
            })?;
        let predicted_effect_id = self.next_effect_id;
        let handler_identity = handler.handler_identity();
        let acquire_outcome = handler.handle_effect(request.clone());
        self.record_effect_exchange(&request, &acquire_outcome, &handler_identity, predicted_effect_id);
        let decision = acquire_outcome
            .into_value("acquire")
            .unwrap_or_else(EffectResult::failure);
        match decision {
            EffectResult::Success(evidence) => {
                self.guard_layer
                    .resources
                    .insert(layer_id, evidence.clone());
                let state = self
                    .resource_states
                    .entry(input.sid)
                    .or_default();
                let _commitment = state.commit(&evidence);
                Ok(StepPack {
                    coro_update: CoroUpdate::AdvancePcWriteReg {
                        reg: input.dst,
                        val: evidence,
                    },
                    type_update: None,
                    events: vec![ObsEvent::Acquired {
                        tick: self.clock.tick,
                        session: input.endpoint.sid,
                        role: input.role.to_string(),
                        layer: input.layer.to_string(),
                    }],
                })
            }
            EffectResult::Blocked => Ok(StepPack {
                coro_update: {
                    let effect_id = self.issue_runtime_effect(
                        "handle_acquire",
                        Some(input.sid),
                        &handler_identity,
                        json!({
                            "session": input.sid,
                            "role": input.role,
                            "layer": input.layer,
                        }),
                    );
                    self.complete_runtime_effect(
                        effect_id,
                        OutstandingEffectStatus::Blocked,
                        json!({
                            "status": "blocked",
                        }),
                    )
                    .map_err(|err| Fault::Acquire {
                        layer: input.layer.to_string(),
                        failure: EffectFailure::contract_violation(err.to_string()),
                    })?;
                    CoroUpdate::Block(BlockReason::AcquireDenied {
                        layer: input.layer.to_string(),
                    })
                },
                type_update: None,
                events: vec![],
            }),
            EffectResult::Failure(failure) => Err(Fault::Acquire {
                layer: input.layer.to_string(),
                failure: {
                    let effect_id = self.issue_runtime_effect(
                        "handle_acquire",
                        Some(input.sid),
                        &handler_identity,
                        json!({
                            "session": input.sid,
                            "role": input.role,
                            "layer": input.layer,
                        }),
                    );
                    self.complete_runtime_effect(
                        effect_id,
                        OutstandingEffectStatus::Failed,
                        json!({
                            "status": "failure",
                            "failure": failure,
                        }),
                    )
                    .map_err(|err| Fault::Acquire {
                        layer: input.layer.to_string(),
                        failure: EffectFailure::contract_violation(err.to_string()),
                    })?;
                    failure
                },
            }),
        }
    }

    pub(crate) fn step_release(
        &mut self,
        input: GuardReleaseInput<'_>,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        self.guard_active(input.layer)?;
        let layer_id = LayerId(input.layer.to_string());
        if self.guard_layer.resources.is_empty() {
            self.guard_layer
                .resources
                .insert(layer_id.clone(), Value::Unit);
        }
        let ev = self.coroutines[input.coro_idx]
            .regs
            .get(usize::from(input.evidence))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        let decoded = InMemoryGuardLayer::decodeEvidence(&ev).map_err(|e| Fault::Acquire {
            layer: input.layer.to_string(),
            failure: EffectFailure::invalid_evidence(e),
        })?;
        let handler_identity = handler.handler_identity();
        let request = EffectRequest::release(
            self.clock.tick,
            input.sid,
            None,
            input.role,
            input.layer,
            &ev,
            &self.coroutines[input.coro_idx].regs,
        );
        self.ensure_effect_request_allowed(&request)
            .map_err(|failure| Fault::Acquire {
                layer: input.layer.to_string(),
                failure,
            })?;
        let predicted_effect_id = self.next_effect_id;
        let release_outcome = handler.handle_effect(request.clone());
        self.record_effect_exchange(&request, &release_outcome, &handler_identity, predicted_effect_id);
        match release_outcome
            .into_unit("handle_release")
            .unwrap_or_else(EffectResult::failure)
        {
            EffectResult::Success(()) => {}
            EffectResult::Blocked => {
                let effect_id = self.issue_runtime_effect(
                    "handle_release",
                    Some(input.sid),
                    &handler_identity,
                    json!({
                        "session": input.sid,
                        "role": input.role,
                        "layer": input.layer,
                    }),
                );
                let failure =
                    EffectFailure::contract_violation("handle_release returned blocked");
                self.complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Failed,
                    json!({
                        "status": "failure",
                        "failure": failure,
                    }),
                )
                .map_err(|err| Fault::Acquire {
                    layer: input.layer.to_string(),
                    failure: EffectFailure::contract_violation(err.to_string()),
                })?;
                return Err(Fault::Acquire {
                    layer: input.layer.to_string(),
                    failure,
                });
            }
            EffectResult::Failure(failure) => {
                let effect_id = self.issue_runtime_effect(
                    "handle_release",
                    Some(input.sid),
                    &handler_identity,
                    json!({
                        "session": input.sid,
                        "role": input.role,
                        "layer": input.layer,
                    }),
                );
                self.complete_runtime_effect(
                    effect_id,
                    OutstandingEffectStatus::Failed,
                    json!({
                        "status": "failure",
                        "failure": failure,
                    }),
                )
                .map_err(|err| Fault::Acquire {
                    layer: input.layer.to_string(),
                    failure: EffectFailure::contract_violation(err.to_string()),
                })?;
                return Err(Fault::Acquire {
                    layer: input.layer.to_string(),
                    failure,
                });
            }
        }
        self.guard_layer
            .close(&layer_id, decoded)
            .map_err(|e| Fault::Acquire {
                layer: input.layer.to_string(),
                failure: EffectFailure::invalid_evidence(e),
            })?;
        if let Some(state) = self.resource_states.get_mut(&input.sid) {
            state.consume(&ev).map_err(|e| Fault::Acquire {
                layer: input.layer.to_string(),
                failure: EffectFailure::invalid_evidence(e),
            })?;
        }
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Released {
                tick: self.clock.tick,
                session: input.endpoint.sid,
                role: input.role.to_string(),
                layer: input.layer.to_string(),
            }],
        })
    }

    pub(crate) fn step_fork(
        &mut self,
        coro_idx: usize,
        role: &str,
        sid: SessionId,
        ghost: u16,
    ) -> Result<StepPack, Fault> {
        if !self.config.speculation_enabled {
            return Err(speculation_fault_disabled());
        }
        let ghost_val = self.coroutines[coro_idx]
            .regs
            .get(usize::from(ghost))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        let ghost_sid = match ghost_val {
            Value::Nat(v) => usize::try_from(v).map_err(|_| Fault::TypeViolation {
                expected: telltale_types::ValType::Nat,
                actual: telltale_types::ValType::Nat,
                message: format!("{role}: fork ghost id out of range"),
            })?,
            _ => {
                return Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Nat,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: fork expects nat ghost id"),
                })
            }
        };
        self.coroutines[coro_idx].spec_state = Some(crate::coroutine::SpeculationState {
            ghost_sid,
            depth: 0,
        });
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Forked {
                tick: self.clock.tick,
                session: sid,
                ghost: ghost_sid,
            }],
        })
    }

    pub(crate) fn step_join(
        &mut self,
        coro_idx: usize,
        _role: &str,
        sid: SessionId,
    ) -> Result<StepPack, Fault> {
        if self.coroutines[coro_idx].spec_state.is_none() {
            return Err(speculation_fault_join_requires_active());
        }
        self.coroutines[coro_idx].spec_state = None;
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Joined {
                tick: self.clock.tick,
                session: sid,
            }],
        })
    }

    pub(crate) fn step_abort(
        &mut self,
        coro_idx: usize,
        _role: &str,
        sid: SessionId,
    ) -> Result<StepPack, Fault> {
        if self.coroutines[coro_idx].spec_state.is_none() {
            return Err(speculation_fault_abort_requires_active());
        }
        // Deterministic V2 policy: abort clears speculation state and records
        // one abort event. It does not mutate effect nonce, topology-failure
        // fields, or effect trace outside normal event emission.
        self.coroutines[coro_idx].spec_state = None;
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![
                ObsEvent::Aborted {
                    tick: self.clock.tick,
                    session: sid,
                },
                ObsEvent::SessionTerminal {
                    tick: self.clock.tick,
                    session: sid,
                    reason: SessionTerminalReason::Aborted {
                        reason: "abort instruction".to_string(),
                    },
                },
            ],
        })
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
        self.delegation_audit_log.push(
            DelegationAuditRecord {
                tick: self.clock.tick,
                receipt,
                status,
                reason,
            },
            &self.config.observability_retention,
        );
    }

    fn validate_delegation_transfer(
        &self,
        coro_idx: usize,
        target_idx: usize,
        role: &str,
        endpoint: &Endpoint,
    ) -> Result<(), Fault> {
        validate_delegation_coherence(
            &self.coroutines[coro_idx],
            &self.coroutines[target_idx],
            endpoint,
            role,
        )?;
        if endpoint_owner_ids(&self.coroutines, endpoint) != vec![self.coroutines[coro_idx].id] {
            return Err(transfer_fault_delegation_guard_violation("before"));
        }
        Ok(())
    }

    fn apply_delegation_transfer_with_receipt(
        &mut self,
        coro_idx: usize,
        target_idx: usize,
        receipt: &DelegationReceipt,
    ) -> Result<(), Fault> {
        let ep = receipt.endpoint.clone();
        if coro_idx == target_idx {
            let source_before = self.coroutines[coro_idx].clone();
            let result = move_endpoint_bundle(&ep, &mut self.coroutines[coro_idx], None).and_then(
                |_| {
                    if endpoint_owner_ids(&self.coroutines, &ep) == vec![self.coroutines[target_idx].id]
                    {
                        Ok(())
                    } else {
                        Err(transfer_fault_delegation_guard_violation("after"))
                    }
                },
            );
            if let Err(err) = result {
                self.coroutines[coro_idx] = source_before;
                self.record_delegation_audit(
                    receipt.clone(),
                    DelegationStatus::RolledBack,
                    Some(err.to_string()),
                );
                return Err(err);
            }
        } else if coro_idx < target_idx {
            let source_before = self.coroutines[coro_idx].clone();
            let target_before = self.coroutines[target_idx].clone();
            let result = {
                let (left, right) = self.coroutines.split_at_mut(target_idx);
                move_endpoint_bundle(&ep, &mut left[coro_idx], Some(&mut right[0]))
            }
            .and_then(|_| {
                if endpoint_owner_ids(&self.coroutines, &ep) == vec![self.coroutines[target_idx].id] {
                    Ok(())
                } else {
                    Err(transfer_fault_delegation_guard_violation("after"))
                }
            });
            if let Err(err) = result {
                self.coroutines[coro_idx] = source_before;
                self.coroutines[target_idx] = target_before;
                self.record_delegation_audit(
                    receipt.clone(),
                    DelegationStatus::RolledBack,
                    Some(err.to_string()),
                );
                return Err(err);
            }
        } else {
            let source_before = self.coroutines[coro_idx].clone();
            let target_before = self.coroutines[target_idx].clone();
            let result = {
                let (left, right) = self.coroutines.split_at_mut(coro_idx);
                move_endpoint_bundle(&ep, &mut right[0], Some(&mut left[target_idx]))
            }
            .and_then(|_| {
                if endpoint_owner_ids(&self.coroutines, &ep) == vec![self.coroutines[target_idx].id] {
                    Ok(())
                } else {
                    Err(transfer_fault_delegation_guard_violation("after"))
                }
            });
            if let Err(err) = result {
                self.coroutines[coro_idx] = source_before;
                self.coroutines[target_idx] = target_before;
                self.record_delegation_audit(
                    receipt.clone(),
                    DelegationStatus::RolledBack,
                    Some(err.to_string()),
                );
                return Err(err);
            }
        }

        self.record_delegation_audit(receipt.clone(), DelegationStatus::Committed, None);
        Ok(())
    }

    pub(crate) fn step_transfer(
        &mut self,
        coro_idx: usize,
        role: &str,
        _sid: SessionId,
        endpoint: u16,
        target: u16,
        _bundle: u16,
    ) -> Result<StepPack, Fault> {
        let request = decode_transfer_request(&self.coroutines[coro_idx], role, endpoint, target)?;
        let target_id = request.target_id;
        let ep = request.endpoint;
        let target_idx = self
            .coroutines
            .iter()
            .position(|c| c.id == target_id)
            .ok_or(Fault::Transfer {
                message: "target coroutine not found".into(),
            })?;
        self.validate_delegation_transfer(coro_idx, target_idx, role, &ep)?;
        let receipt = self.issue_delegation_receipt(
            ep.clone(),
            self.coroutines[coro_idx].id,
            self.coroutines[target_idx].id,
        );
        self.apply_delegation_transfer_with_receipt(coro_idx, target_idx, &receipt)?;

        self.sched.record_cross_lane_handoff(
            self.coroutines[coro_idx].id,
            self.coroutines[target_idx].id,
            format!("transfer {}:{}", ep.sid, ep.role),
        );

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Transferred {
                tick: self.clock.tick,
                session: ep.sid,
                role: role.to_string(),
                from: self.coroutines[coro_idx].id,
                to: self.coroutines[target_idx].id,
            }],
        })
    }

}
