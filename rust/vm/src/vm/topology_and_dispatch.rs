impl VM {
    fn duration_to_ticks(&self, duration: Duration) -> u64 {
        let tick_nanos = self.config.tick_duration.as_nanos();
        if tick_nanos == 0 {
            return 1;
        }
        let duration_nanos = duration.as_nanos();
        let ticks = duration_nanos.div_ceil(tick_nanos);
        u64::try_from(ticks).unwrap_or(u64::MAX).max(1)
    }

    fn prune_expired_timeouts(&mut self) {
        let tick = self.clock.tick;
        let expired_roles: Vec<String> = self
            .timed_out_sites
            .iter()
            .filter_map(|(role, until_tick)| (*until_tick <= tick).then_some(role.clone()))
            .collect();
        if !expired_roles.is_empty() {
            for role in &expired_roles {
                self.timed_out_sites.remove(role);
                let coro_ids = self.role_coroutines.get(role).cloned().unwrap_or_default();
                for coro_id in coro_ids {
                    self.timed_out_coro_ids.remove(&coro_id);
                    self.sync_ready_eligibility_for(coro_id);
                }
            }
        }
    }

    fn is_site_timed_out(&self, site: &str) -> bool {
        self.timed_out_sites.contains_key(site)
    }

    fn is_site_crashed(&self, site: &str) -> bool {
        self.crashed_sites.contains(site)
    }

    fn is_edge_partitioned(&self, from: &str, to: &str) -> bool {
        self.partitioned_edges
            .contains(&(from.to_string(), to.to_string()))
    }

    fn edge_corruption(&self, edge: &Edge) -> Option<CorruptionType> {
        self.corrupted_edges
            .get(&(edge.sender.clone(), edge.receiver.clone()))
            .cloned()
    }

    fn apply_corruption(value: Value, corruption: CorruptionType) -> Value {
        match corruption {
            CorruptionType::BitFlip => match value {
                Value::Nat(v) => Value::Nat(v ^ 1),
                Value::Bool(v) => Value::Bool(!v),
                Value::Str(s) => {
                    let mut bytes = s.into_bytes();
                    if let Some(first) = bytes.first_mut() {
                        *first ^= 0x01;
                    }
                    Value::Str(String::from_utf8_lossy(&bytes).to_string())
                }
                Value::Prod(left, right) => {
                    Value::Prod(Box::new(Self::apply_corruption(*left, corruption)), right)
                }
                other => other,
            },
            CorruptionType::Truncation => match value {
                Value::Str(s) => Value::Str(s.chars().take(s.chars().count() / 2).collect()),
                _ => Value::Unit,
            },
            CorruptionType::PayloadErase => Value::Unit,
        }
    }

    fn normalize_topology_state(&mut self) {}

    fn apply_site_failure(&mut self, site: &str) {
        let reason = format!("site {site} crashed");

        let session_ids = self.sessions.session_ids();
        for sid in session_ids {
            let should_fault = self
                .sessions
                .get(sid)
                .is_some_and(|session| session.roles.iter().any(|role| role == site));
            if !should_fault {
                continue;
            }
            if let Some(session) = self.sessions.get_mut(sid) {
                if matches!(
                    session.status,
                    SessionStatus::Closed
                        | SessionStatus::Cancelled
                        | SessionStatus::Faulted { .. }
                ) {
                    continue;
                }
                session.status = SessionStatus::Faulted {
                    reason: reason.clone(),
                };
                self.monitor.remove_kind(sid);
            }
        }

        let mut faulted = Vec::new();
        for coro in &mut self.coroutines {
            if coro.role == site && !coro.is_terminal() {
                let fault = Fault::Invoke {
                    message: reason.clone(),
                };
                coro.status = CoroStatus::Faulted(fault.clone());
                faulted.push((coro.id, fault));
            }
        }
        for (coro_id, fault) in faulted {
            self.sched.mark_done(coro_id);
            self.eligible_ready.remove(&coro_id);
            self.obs_trace.push(
                ObsEvent::Faulted {
                    tick: self.clock.tick,
                    coro_id,
                    fault,
                },
                &self.config.observability_retention,
            );
        }
    }

    fn charge_instruction_cost(&mut self, coro_idx: usize) -> Result<(), Fault> {
        let cost = self.config.instruction_cost;
        let budget = self.coroutines[coro_idx].cost_budget;
        if budget < cost {
            return Err(Fault::OutOfCredits);
        }
        self.coroutines[coro_idx].cost_budget = budget - cost;
        Ok(())
    }

    fn should_capture_effect_kind(&self, effect_kind: &str) -> bool {
        match self.config.effect_trace_capture_mode {
            EffectTraceCaptureMode::Full => true,
            EffectTraceCaptureMode::TopologyOnly => effect_kind == "topology_event",
            EffectTraceCaptureMode::Disabled => false,
        }
    }

    fn enforce_handler_identity_contract(&mut self, handler_identity: &str) -> Result<(), VMError> {
        if !self.config.host_contract_assertions {
            return Ok(());
        }
        match &self.handler_identity_anchor {
            None => {
                self.handler_identity_anchor = Some(handler_identity.to_string());
                Ok(())
            }
            Some(anchor) if anchor == handler_identity => Ok(()),
            Some(anchor) => Err(VMError::HandlerError(format!(
                "[host-contract] handler_identity changed from '{anchor}' to '{handler_identity}'"
            ))),
        }
    }

    fn assert_topology_events_sorted(
        &self,
        tick: u64,
        events: &[TopologyPerturbation],
    ) -> Result<(), VMError> {
        if !self.config.host_contract_assertions {
            return Ok(());
        }
        for idx in 1..events.len() {
            let prev_key = events[idx - 1].ordering_key();
            let next_key = events[idx].ordering_key();
            if prev_key > next_key {
                return Err(VMError::HandlerError(format!(
                    "[host-contract] topology_events at tick {tick} must be pre-sorted by ordering_key; out-of-order index {idx}"
                )));
            }
        }
        Ok(())
    }

    fn apply_topology_event(&mut self, event: &TopologyPerturbation) {
        match event {
            TopologyPerturbation::Crash { site } => {
                self.crashed_sites.insert(site.clone());
                self.apply_site_failure(site);
                self.mark_eligibility_dirty();
            }
            TopologyPerturbation::Partition { from, to } => {
                self.partitioned_edges.insert((from.clone(), to.clone()));
                self.partitioned_edges.insert((to.clone(), from.clone()));
            }
            TopologyPerturbation::Heal { from, to } => {
                self.partitioned_edges.remove(&(from.clone(), to.clone()));
                self.partitioned_edges.remove(&(to.clone(), from.clone()));
                self.corrupted_edges.remove(&(from.clone(), to.clone()));
                self.corrupted_edges.remove(&(to.clone(), from.clone()));
            }
            TopologyPerturbation::Corrupt {
                from,
                to,
                corruption,
            } => {
                self.corrupted_edges
                    .insert((from.clone(), to.clone()), *corruption);
            }
            TopologyPerturbation::Timeout { site, duration } => {
                let until_tick = self
                    .clock
                    .tick
                    .saturating_add(self.duration_to_ticks(*duration));
                self.timed_out_sites.insert(site.clone(), until_tick);
                let coro_ids = self.role_coroutines.get(site).cloned().unwrap_or_default();
                for coro_id in coro_ids {
                    self.timed_out_coro_ids.insert(coro_id);
                    self.sync_ready_eligibility_for(coro_id);
                }
            }
        }
        self.normalize_topology_state();
    }

    fn ingest_topology_events(&mut self, handler: &dyn EffectHandler) -> Result<(), VMError> {
        let tick = self.clock.tick;
        let handler_identity = handler.handler_identity();
        self.enforce_handler_identity_contract(&handler_identity)?;
        let mut events = handler
            .topology_events(tick)
            .map_err(VMError::HandlerError)?;
        self.assert_topology_events_sorted(tick, &events)?;
        events.sort_by_key(TopologyPerturbation::ordering_key);
        for event in events {
            self.apply_topology_event(&event);
            if self.should_capture_effect_kind("topology_event") {
                self.effect_trace.push(
                    EffectTraceEntry {
                        effect_id: self.next_effect_id,
                        effect_kind: "topology_event".to_string(),
                        inputs: json!({
                            "tick": tick,
                        }),
                        outputs: json!({
                            "applied": true,
                            "topology": event,
                        }),
                        handler_identity: handler_identity.clone(),
                        ordering_key: self.next_effect_id,
                        topology: Some(event),
                    },
                    &self.config.observability_retention,
                );
                self.next_effect_id = self.next_effect_id.saturating_add(1);
            }
        }
        Ok(())
    }

    /// Try to unblock coroutines that are waiting on receives.
    fn try_unblock_receivers(&mut self) {
        let blocked_ids = self.sched.blocked_ids();
        for coro_id in blocked_ids {
            let Some(idx) = self.coro_index(coro_id) else {
                continue;
            };
            let role = &self.coroutines[idx].role;
            if self.paused_roles.contains(role)
                || self.is_site_crashed(role)
                || self.is_site_timed_out(role)
            {
                continue;
            }
            let reason = self.sched.block_reason(coro_id).cloned();
            if let Some(BlockReason::Recv { token, .. }) = reason {
                if let Some(session) = self.sessions.get(token.sid) {
                    let has_msg = session.roles.iter().any(|sender| {
                        sender != &token.endpoint.role
                            && session.has_message(sender, &token.endpoint.role)
                    });
                    if has_msg {
                        self.sched.unblock(coro_id);
                        self.sync_ready_eligibility_for(coro_id);
                    }
                }
            }
        }
    }

    /// Execute one instruction for a coroutine.
    ///
    /// Follows the Lean `execInstr` pipeline:
    /// 1. Fetch instruction at PC
    /// 2. Dispatch to per-instruction step function (which owns type checking)
    /// 3. Commit the `StepPack` atomically
    fn exec_instr(
        &mut self,
        coro_id: usize,
        handler: &dyn EffectHandler,
    ) -> Result<ExecOutcome, Fault> {
        let handler_identity = handler.handler_identity();
        self.enforce_handler_identity_contract(&handler_identity)
            .map_err(|e| Fault::Invoke {
                message: e.to_string(),
            })?;
        let idx = self.coro_index(coro_id).ok_or_else(|| Fault::Speculation {
            message: format!("scheduler selected missing coroutine {coro_id}"),
        })?;
        let pc = self.coroutines[idx].pc;
        let sid = self.coroutines[idx].session_id;
        let role = self.coroutines[idx].role.clone();
        let fallback_ep = self.coroutines[idx]
            .owned_endpoints
            .first()
            .cloned()
            .unwrap_or(Endpoint {
                sid,
                role: role.clone(),
            });
        let program = self
            .programs
            .get(self.coroutines[idx].program_id)
            .ok_or(Fault::PcOutOfBounds)?;

        // 1. Fetch.
        if pc >= program.len() {
            return Err(Fault::PcOutOfBounds);
        }
        let instr = program[pc].clone();
        let monitor_ep = match &instr {
            Instr::Send { chan, .. }
            | Instr::Receive { chan, .. }
            | Instr::Offer { chan, .. }
            | Instr::Choose { chan, .. } => self
                .endpoint_from_reg(idx, *chan)
                .unwrap_or_else(|_| fallback_ep.clone()),
            Instr::Close { session } => self
                .endpoint_from_reg(idx, *session)
                .unwrap_or_else(|_| fallback_ep.clone()),
            _ => fallback_ep,
        };

        // 1.5 Monitor precheck and deterministic cost charge.
        self.monitor_precheck(&monitor_ep, &role, &instr)?;
        self.charge_instruction_cost(idx)?;

        // 2. Dispatch to per-instruction step function.
        let pack = exec::step_instr(self, idx, &monitor_ep, &role, sid, instr, handler)?;

        let output_hint = if pack.events.is_empty() {
            None
        } else {
            handler.output_condition_hint(sid, &role, &self.coroutines[idx].regs)
        };

        // 3. Commit atomically.
        self.commit_pack(idx, pack, output_hint, &handler_identity)
    }

    // ---- Per-instruction step functions (each owns its type logic) ----

    /// Send: lookup type → match Send → compute payload → enqueue → StepPack with L'.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn step_send(
        &mut self,
        coro_idx: usize,
        role: &str,
        chan: u16,
        val_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed { endpoint: ep });
        }
        let sid = ep.sid;

        // Type lookup — instruction owns this.
        let local_type = self
            .sessions
            .lookup_type(&ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?
            .clone();

        // Pattern match: must be Send.
        let (partner, branches) = match &local_type {
            LocalTypeR::Send {
                partner, branches, ..
            } => (partner.clone(), branches.clone()),
            other => {
                return Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: expected Send, got {other:?}"),
                })
            }
        };

        // Extract continuation (L') from first branch.
        let (label, expected_type, continuation) = branches
            .first()
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: send has no branches"),
            })?
            .clone();

        // Compute payload/decision via handler.
        let coro = &self.coroutines[coro_idx];
        let send_payload = self.read_reg_checked(coro_idx, val_reg)?;
        let fast_path =
            SendDecisionFastPathInput::new(sid, role, &partner, &label.name, Some(&send_payload));
        let decision = if let Some(decision) =
            handler.send_decision_fast_path(fast_path, &coro.regs, Some(&send_payload))
        {
            decision.map_err(|e| Fault::Invoke { message: e })?
        } else {
            handler
                .send_decision(SendDecisionInput {
                    sid,
                    role,
                    partner: &partner,
                    label: &label.name,
                    state: &coro.regs,
                    payload: Some(send_payload),
                })
                .map_err(|e| Fault::Invoke { message: e })?
        };

        let edge = Edge::new(sid, role.to_string(), partner.clone());

        if self.is_site_crashed(role)
            || self.is_site_crashed(&partner)
            || self.is_site_timed_out(role)
            || self.is_site_timed_out(&partner)
            || self.is_edge_partitioned(role, &partner)
        {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::Send { edge }),
                type_update: None,
                events: vec![],
            });
        }

        // Enqueue into per-edge signed session buffer (if delivered).
        let maybe_corruption = self.edge_corruption(&edge);
        if let SendDecision::Deliver(payload) = &decision {
            self.validate_payload(
                role,
                "send",
                &label.name,
                expected_type.as_ref(),
                payload,
                true,
            )?;
        }
        let enqueue = match decision {
            SendDecision::Deliver(payload) => {
                let sequence_no = self.allocate_send_sequence(&edge);
                let payload = if let Some(corruption) = maybe_corruption {
                    Self::apply_corruption(payload, corruption)
                } else {
                    payload
                };
                let session = self
                    .sessions
                    .get_mut(sid)
                    .ok_or_else(|| Fault::ChannelClosed {
                        endpoint: ep.clone(),
                    })?;
                session
                    .send_with_sequence(role, &partner, payload, sequence_no)
                    .map_err(|e| Fault::Invoke { message: e })?
            }
            SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
        };

        match enqueue {
            EnqueueResult::Ok => {}
            EnqueueResult::WouldBlock => {
                // Block — NO type advancement.
                return Ok(StepPack {
                    coro_update: CoroUpdate::Block(BlockReason::Send { edge }),
                    type_update: None,
                    events: vec![],
                });
            }
            EnqueueResult::Full => {
                return Err(Fault::BufferFull { endpoint: ep });
            }
            EnqueueResult::Dropped => {}
        }

        // Success: resolve continuation and advance type.
        let original = self.sessions.original_type(&ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update,
            events: vec![ObsEvent::Sent {
                tick: self.clock.tick,
                edge,
                session: sid,
                from: role.to_string(),
                to: partner,
                label: label.name,
            }],
        })
    }

}
