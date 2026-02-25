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
                self.effect_trace.push(EffectTraceEntry {
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
                });
                self.next_effect_id = self.next_effect_id.saturating_add(1);
            }
        }
        Ok(())
    }

    fn try_unblock_receivers(&mut self) {
        let blocked_ids = self.scheduler.blocked_ids();
        for coro_id in blocked_ids {
            let should_skip = self.coroutines.get(coro_id).is_some_and(|coro| {
                let guard = coro.lock().expect("coroutine lock poisoned");
                self.crashed_sites.contains(&guard.role)
                    || self.timed_out_sites.contains_key(&guard.role)
            });
            if should_skip {
                continue;
            }
            let reason = self.scheduler.block_reason(coro_id).cloned();
            if let Some(BlockReason::Recv { token, .. }) = reason {
                if let Some(session) = self.sessions.get(token.sid) {
                    let session = session.lock().expect("session lock poisoned");
                    let has_msg = session.roles.iter().any(|sender| {
                        sender != &token.endpoint.role
                            && session.has_message(sender, &token.endpoint.role)
                    });
                    if has_msg {
                        self.scheduler.unblock(coro_id);
                    }
                }
            }
        }
    }

    fn planner_eligible(
        planner: &mut WavePlannerState,
        coros: &[Arc<Mutex<Coroutine>>],
        crashed_sites: &BTreeSet<SiteId>,
        timed_out_sites: &BTreeMap<SiteId, u64>,
        id: usize,
    ) -> bool {
        let Some(coro) = coros.get(id) else {
            return false;
        };
        let coro_guard = coro.lock().expect("coroutine lock poisoned");
        let sid = coro_guard.session_id;
        let lane = id % planner.lane_count;
        if crashed_sites.contains(&coro_guard.role)
            || timed_out_sites.contains_key(&coro_guard.role)
        {
            return false;
        }

        if planner.used_lanes.contains(&lane) {
            planner.note_conflict();
            return false;
        }
        if planner.used_sessions.contains(&sid) && !planner.allow_same_session_disjoint {
            planner.note_conflict();
            return false;
        }

        let footprint: Vec<(SessionId, u64)> = coro_guard
            .owned_endpoints
            .iter()
            .map(|ep| (ep.sid, role_fingerprint(&ep.role)))
            .collect();
        if footprint
            .iter()
            .any(|entry| planner.used_footprints.contains(entry))
        {
            planner.note_conflict();
            return false;
        }
        for entry in footprint {
            planner.used_footprints.insert(entry);
        }
        true
    }

    fn push_pick(
        &mut self,
        picks: &mut Vec<Picked>,
        planner: &mut WavePlannerState,
        coro_id: usize,
    ) -> Result<(), VMError> {
        let lane = coro_id % planner.lane_count;
        let coro = self
            .coroutines
            .get(coro_id)
            .cloned()
            .expect("coroutine exists");
        let sid = {
            let coro_guard = coro.lock().expect("coroutine lock poisoned");
            coro_guard.session_id
        };
        let session = self
            .sessions
            .get(sid)
            .ok_or(VMError::SessionNotFound(sid))?;
        planner.used_sessions.insert(sid);
        planner.used_lanes.insert(lane);
        picks.push(Picked {
            coro_id,
            sid,
            lane,
            coro,
            session,
        });
        Ok(())
    }

    fn record_planner_conflicts(&mut self, planner_conflict_events: u64) {
        self.contention_metrics.lock_contention_events = self
            .contention_metrics
            .lock_contention_events
            .saturating_add(planner_conflict_events);
        self.contention_metrics.planner_conflict_events = self
            .contention_metrics
            .planner_conflict_events
            .saturating_add(planner_conflict_events);
    }

    fn pick_ready(&mut self, n: usize) -> Result<Vec<Picked>, VMError> {
        let mut picks = Vec::new();
        let coros = &self.coroutines;
        let mut planner = WavePlannerState::new(
            self.lane_count.max(1),
            self.config.footprint_guided_wave_widening,
        );

        while picks.len() < n {
            let Some(coro_id) = VMKernel::select_ready_eligible(
                &mut self.scheduler,
                |id| coro_has_progress(coros, id),
                |id| {
                    Self::planner_eligible(
                        &mut planner,
                        coros,
                        &self.crashed_sites,
                        &self.timed_out_sites,
                        id,
                    )
                },
            ) else {
                break;
            };

            if picks.len() >= n {
                break;
            }

            self.push_pick(&mut picks, &mut planner, coro_id)?;
        }

        self.record_planner_conflicts(planner.conflict_events);

        Ok(picks)
    }

    #[allow(clippy::too_many_lines)]
    fn commit_pack(
        &mut self,
        coro: &Arc<Mutex<Coroutine>>,
        session: &Arc<Mutex<SessionState>>,
        pack: StepPack,
        output_hint: Option<OutputConditionHint>,
        handler_identity: &str,
    ) -> Result<ExecOutcome, Fault> {
        if !pack.events.is_empty() {
            apply_output_condition_gate(
                &self.config.output_condition_policy,
                &mut self.output_condition_checks,
                &mut self.trace,
                self.clock.tick,
                output_hint,
            )?;
        }

        for ev in &pack.events {
            self.intern_obs_event(ev);
            let maybe_entry = effect_trace_entry_for_event(
                ev,
                self.next_effect_id,
                handler_identity,
                self.clock.tick,
            );
            if let Some(entry) = maybe_entry {
                if self.should_capture_effect_kind(&entry.effect_kind) {
                    self.effect_trace.push(entry);
                    self.next_effect_id = self.next_effect_id.saturating_add(1);
                }
            }
        }

        let mut coro_guard = coro.lock().expect("coroutine lock poisoned");

        match pack.coro_update {
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
                coro_guard.regs[usize::from(reg)] = val.clone();
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
                self.coroutines.push(Arc::new(Mutex::new(child)));

                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
        }

        if let Some((ep, update)) = pack.type_update {
            let mut session_guard = session.lock().expect("session lock poisoned");
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

        self.trace.extend(pack.events);
        let coro_guard = coro.lock().expect("coroutine lock poisoned");

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
                let _: StringId = self.role_symbols.intern(&edge.sender);
                let _: StringId = self.role_symbols.intern(&edge.receiver);
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
            endpoint_role: endpoint.role,
            from_coro,
            to_coro,
            from_lane,
            to_lane,
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
        let endpoint = Endpoint {
            sid: handoff.session,
            role: handoff.endpoint_role.clone(),
        };
        if handoff.from_coro == handoff.to_coro {
            let source_arc =
                self.coroutines
                    .get(handoff.from_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "transfer source coroutine not found".into(),
                    })?;
            let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
            move_endpoint_bundle(&endpoint, &mut source, None)
        } else {
            let source_arc =
                self.coroutines
                    .get(handoff.from_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "transfer source coroutine not found".into(),
                    })?;
            let target_arc =
                self.coroutines
                    .get(handoff.to_coro)
                    .cloned()
                    .ok_or(Fault::Transfer {
                        message: "target coroutine not found".into(),
                    })?;

            // Global lock order: lower coroutine id first.
            if handoff.from_coro < handoff.to_coro {
                let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
                let mut target = lock_with_contention(&target_arc, &mut self.contention_metrics);
                move_endpoint_bundle(&endpoint, &mut source, Some(&mut target))
            } else {
                let mut target = lock_with_contention(&target_arc, &mut self.contention_metrics);
                let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
                move_endpoint_bundle(&endpoint, &mut source, Some(&mut target))
            }
        }
    }

    fn assert_delegation_handoff_owner(
        &self,
        endpoint: &Endpoint,
        expected_owner: usize,
    ) -> Result<(), Fault> {
        let mut owners = Vec::new();
        for coro in &self.coroutines {
            let guard = coro.lock().expect("coroutine lock poisoned");
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

fn role_fingerprint(role: &str) -> u64 {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;
    let mut hash = FNV_OFFSET;
    for byte in role.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

fn lock_with_contention<'a, T>(
    arc: &'a Arc<Mutex<T>>,
    metrics: &mut ContentionMetrics,
) -> std::sync::MutexGuard<'a, T> {
    match arc.try_lock() {
        Ok(guard) => guard,
        Err(TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
        Err(TryLockError::WouldBlock) => {
            metrics.lock_contention_events = metrics.lock_contention_events.saturating_add(1);
            metrics.mutex_lock_contention_events =
                metrics.mutex_lock_contention_events.saturating_add(1);
            arc.lock().expect("mutex lock poisoned after contention")
        }
    }
}

struct ThreadedStepCtx<'a> {
    config: &'a VMConfig,
    guard_resources: &'a Arc<Mutex<BTreeMap<String, Value>>>,
    resource_states: &'a Arc<Mutex<BTreeMap<SessionId, ResourceState>>>,
    crashed_sites: &'a BTreeSet<String>,
    partitioned_edges: &'a BTreeSet<(String, String)>,
    corrupted_edges: &'a BTreeMap<(String, String), CorruptionType>,
    timed_out_sites: &'a BTreeMap<String, u64>,
    handler: &'a dyn EffectHandler,
    tick: u64,
}

struct ThreadedExecCtx<'a> {
    store: &'a ThreadedSessionStore,
    programs: &'a [Vec<Instr>],
    step: ThreadedStepCtx<'a>,
}

#[derive(Clone, Copy)]
struct GuardAcquireStep<'a> {
    ep: &'a Endpoint,
    role: &'a str,
    sid: SessionId,
    layer: &'a str,
    dst: u16,
}

#[derive(Clone, Copy)]
struct GuardReleaseStep<'a> {
    ep: &'a Endpoint,
    role: &'a str,
    sid: SessionId,
    layer: &'a str,
    evidence: u16,
}

#[allow(clippy::too_many_lines)]
fn exec_instr(
    coro: &Arc<Mutex<Coroutine>>,
    session: &Arc<Mutex<SessionState>>,
    ctx: &ThreadedExecCtx<'_>,
) -> Result<(StepPack, Option<OutputConditionHint>), Fault> {
