impl VM {
    /// Recv: lookup type → match Recv → try dequeue → block or process → StepPack.
    pub(crate) fn step_recv(
        &mut self,
        coro_idx: usize,
        role: &str,
        chan: u16,
        dst_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed { endpoint: ep });
        }
        let sid = ep.sid;

        // Type lookup.
        let local_type = self
            .sessions
            .lookup_type(&ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?
            .clone();

        // Pattern match: must be Recv.
        let (partner, branches) = match &local_type {
            LocalTypeR::Recv {
                partner, branches, ..
            } => (partner.clone(), branches.clone()),
            other => {
                return Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: expected Recv, got {other:?}"),
                })
            }
        };

        let (label, expected_type, continuation) = branches
            .first()
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: recv has no branches"),
            })?
            .clone();

        // Try dequeue.
        let session = self.sessions.get(sid).ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
        if !session.has_message(&partner, role) {
            // Block — NO type advancement, NO state change.
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
        // Dequeue from signed session buffer and verify in place.
        let val = {
            let session = self
                .sessions
                .get_mut(sid)
                .ok_or_else(|| Fault::ChannelClosed {
                    endpoint: ep.clone(),
                })?;
            session
                .recv_verified(&partner, role)
                .map_err(|message| Fault::VerificationFailed {
                    edge: edge.clone(),
                    message,
                })?
                .ok_or_else(|| Fault::ChannelClosed {
                    endpoint: ep.clone(),
                })?
        };

        self.validate_payload(
            role,
            "receive",
            &label.name,
            expected_type.as_ref(),
            &val,
            true,
        )?;

        // Process via handler.
        handler
            .handle_recv(
                role,
                &partner,
                &label.name,
                &mut self.coroutines[coro_idx].regs,
                &val,
            )
            .map_err(|e| Fault::Invoke { message: e })?;

        // Resolve continuation and advance type.
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
                label: label.name,
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

        self.sched.add_ready(new_id);
        self.coroutines.push(child);

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
            .is_none_or(String::is_empty)
        {
            return Err(Fault::Invoke {
                message: "no handler bound".to_string(),
            });
        }
        let coro_id = self.coroutines[coro_idx].id;
        handler
            .step(role, &mut self.coroutines[coro_idx].regs)
            .map_err(|e| Fault::Invoke { message: e })?;
        self.apply_invoke_delta(sid, &action_repr)
            .map_err(|e| Fault::Invoke {
                message: format!("invoke persistence delta failed: {e}"),
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
                message: "unknown layer".into(),
            }),
            Some(cfg) if !cfg.active => Err(Fault::Acquire {
                layer: layer.to_string(),
                message: "inactive layer".into(),
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
                message: e,
            })?;
        let decision = handler
            .handle_acquire(
                input.sid,
                input.role,
                input.layer,
                &self.coroutines[input.coro_idx].regs,
            )
            .map_err(|e| Fault::Acquire {
                layer: input.layer.to_string(),
                message: e,
            })?;
        match decision {
            crate::effect::AcquireDecision::Grant(evidence) => {
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
            crate::effect::AcquireDecision::Block => Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::AcquireDenied {
                    layer: input.layer.to_string(),
                }),
                type_update: None,
                events: vec![],
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
            message: e,
        })?;
        handler
            .handle_release(
                input.sid,
                input.role,
                input.layer,
                &ev,
                &self.coroutines[input.coro_idx].regs,
            )
            .map_err(|e| Fault::Acquire {
                layer: input.layer.to_string(),
                message: e,
            })?;
        self.guard_layer
            .close(&layer_id, decoded)
            .map_err(|e| Fault::Acquire {
                layer: input.layer.to_string(),
                message: e,
            })?;
        if let Some(state) = self.resource_states.get_mut(&input.sid) {
            state.consume(&ev).map_err(|e| Fault::Acquire {
                layer: input.layer.to_string(),
                message: e,
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
            events: vec![ObsEvent::Aborted {
                tick: self.clock.tick,
                session: sid,
            }],
        })
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
        if endpoint_owner_ids(&self.coroutines, &ep) != vec![self.coroutines[coro_idx].id] {
            return Err(transfer_fault_delegation_guard_violation("before"));
        }

        if coro_idx == target_idx {
            move_endpoint_bundle(&ep, &mut self.coroutines[coro_idx], None)?;
        } else if coro_idx < target_idx {
            let (left, right) = self.coroutines.split_at_mut(target_idx);
            move_endpoint_bundle(&ep, &mut left[coro_idx], Some(&mut right[0]))?;
        } else {
            let (left, right) = self.coroutines.split_at_mut(coro_idx);
            move_endpoint_bundle(&ep, &mut right[0], Some(&mut left[target_idx]))?;
        }
        if endpoint_owner_ids(&self.coroutines, &ep) != vec![self.coroutines[target_idx].id] {
            return Err(transfer_fault_delegation_guard_violation("after"));
        }

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

    pub(crate) fn step_tag(
        &mut self,
        coro_idx: usize,
        role: &str,
        _sid: SessionId,
        fact_reg: u16,
        dst: u16,
    ) -> Result<StepPack, Fault> {
        let fact_val = self.coroutines[coro_idx]
            .regs
            .get(usize::from(fact_reg))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        let (endpoint, fact) = Self::decode_fact(fact_val).ok_or_else(|| Fault::Transfer {
            message: format!("{role}: tag expects (endpoint, string) fact"),
        })?;
        self.coroutines[coro_idx]
            .knowledge_set
            .push(crate::coroutine::KnowledgeFact {
                endpoint: endpoint.clone(),
                fact: fact.clone(),
            });
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePcWriteReg {
                reg: dst,
                val: Value::Bool(true),
            },
            type_update: None,
            events: vec![ObsEvent::Tagged {
                tick: self.clock.tick,
                session: endpoint.sid,
                role: role.to_string(),
                fact,
            }],
        })
    }

}
