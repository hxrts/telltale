/// Approximate retained state for the live VM runtime.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmMemoryUsage {
    /// Session-store retained state.
    pub session_store: SessionStoreMemoryUsage,
    /// Number of coroutine records still retained by the VM.
    pub coroutine_records: usize,
    /// Number of terminal coroutine records retained by the VM.
    pub terminal_coroutines: usize,
    /// Number of loaded immutable program records.
    pub program_count: usize,
    /// Total instruction count across loaded programs.
    pub program_instruction_count: usize,
    /// Number of retained observable events.
    pub obs_events: usize,
    /// Number of retained effect-trace entries.
    pub effect_trace_entries: usize,
    /// Number of retained replay-consumption artifacts.
    pub communication_artifacts: usize,
    /// Number of retained output-condition checks.
    pub output_condition_checks: usize,
    /// Estimated retained bytes by VM subsystem.
    pub retained_bytes: VmRetainedBytes,
}

/// Estimated retained bytes for VM subsystems.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmRetainedBytes {
    /// Session-store retained bytes.
    pub session_store: usize,
    /// Coroutine state.
    pub coroutines: usize,
    /// Immutable program storage.
    pub programs: usize,
    /// Resource-state storage.
    pub resource_states: usize,
    /// Observable/effect trace storage.
    pub traces: usize,
    /// Replay-state and replay-artifact storage.
    pub replay: usize,
    /// Output-condition diagnostics.
    pub output_condition_checks: usize,
    /// Scheduler and control-state bookkeeping.
    pub scheduler_and_control: usize,
    /// Symbol interning tables.
    pub symbols: usize,
    /// Guard-layer resources.
    pub guard_layer: usize,
    /// Session monitor metadata.
    pub monitor: usize,
    /// Arena slot storage.
    pub arena: usize,
    /// Aggregate retained bytes across VM subsystems.
    pub total: usize,
}

fn vm_serialized_bytes<T: Serialize>(value: &T) -> usize {
    bincode::serialized_size(value)
        .ok()
        .and_then(|bytes| usize::try_from(bytes).ok())
        .unwrap_or(0)
}

impl VM {
    fn communication_replay_enabled(&self) -> bool {
        !matches!(
            self.config.communication_replay_mode,
            CommunicationReplayMode::Off
        )
    }

    fn intern_load_plan_symbols(&mut self, plan: &crate::session::SessionOpenPlan, sid: SessionId) {
        for role in plan.roles() {
            let _: StringId = self.role_symbols.intern(role);
        }
        let _: StringId = self.handler_symbols.intern(crate::session::DEFAULT_HANDLER_ID);
        let edge_handlers: Vec<_> = self
            .sessions
            .get(sid)
            .map(|session| session.edge_handlers.keys().cloned().collect())
            .unwrap_or_default();
        for edge in edge_handlers {
            let _: EdgeId = self.intern_edge(&edge);
        }
    }

    /// Create a VM instance from configuration.
    #[must_use]
    pub fn new(config: VMConfig) -> Self {
        Self::new_with_models(config)
    }

    fn bind_default_handlers_for_session(&mut self, sid: SessionId) {
        self.sessions.set_default_handler_for_session(
            sid,
            crate::session::DEFAULT_HANDLER_ID.to_string(),
        );
        self.handler_symbols.intern(crate::session::DEFAULT_HANDLER_ID);
    }

    fn ensure_session_capacity(&self) -> Result<(), VMError> {
        if self.sessions.active_count() >= self.config.max_sessions {
            return Err(VMError::TooManySessions {
                max: self.config.max_sessions,
            });
        }
        Ok(())
    }

    fn coroutine_runtime_eligible(&self, coro_id: usize) -> bool {
        let Some(idx) = self.coro_index(coro_id) else {
            return false;
        };
        let role = &self.coroutines[idx].role;
        !(self.paused_coro_ids.contains(&coro_id)
            || self.paused_roles.contains(role)
            || self.crashed_sites.contains(role)
            || self.timed_out_coro_ids.contains(&coro_id)
            || self.timed_out_sites.contains_key(role))
    }

    fn mark_eligibility_dirty(&mut self) {
        self.eligibility_dirty = true;
    }

    fn sync_ready_eligibility_for(&mut self, coro_id: usize) {
        let eligible = self.sched.is_ready(coro_id) && self.coroutine_runtime_eligible(coro_id);
        let eligibility = if eligible {
            crate::scheduler::ReadyEligibility::Eligible
        } else {
            crate::scheduler::ReadyEligibility::Ineligible
        };
        self.sched.set_ready_eligibility(coro_id, eligibility);
        #[cfg(debug_assertions)]
        {
            if eligible {
                self.eligible_ready.insert(coro_id);
            } else {
                self.eligible_ready.remove(&coro_id);
            }
        }
    }

    fn refresh_ready_eligibility(&mut self) {
        self.sched.clear_ready_eligibility();
        #[cfg(debug_assertions)]
        self.eligible_ready.clear();
        for coro_id in self.sched.ready_set_snapshot() {
            let eligible = self.coroutine_runtime_eligible(coro_id);
            let eligibility = if eligible {
                crate::scheduler::ReadyEligibility::Eligible
            } else {
                crate::scheduler::ReadyEligibility::Ineligible
            };
            self.sched.set_ready_eligibility(coro_id, eligibility);
            #[cfg(debug_assertions)]
            if eligible {
                self.eligible_ready.insert(coro_id);
            }
        }
        self.eligibility_dirty = false;
    }

    fn ensure_ready_eligibility(&mut self) {
        if self.eligibility_dirty {
            self.refresh_ready_eligibility();
        }
    }

    #[cfg(debug_assertions)]
    fn debug_assert_ready_eligibility_consistent(&self) {
        for coro_id in &self.eligible_ready {
            debug_assert!(self.sched.is_ready(*coro_id));
            debug_assert!(self.coroutine_runtime_eligible(*coro_id));
        }
    }

    fn sync_communication_consumption_mode(&mut self) {
        self.communication_consumption
            .set_mode(self.config.communication_replay_mode);
    }

    fn allocate_send_sequence(&mut self, edge: &Edge) -> u64 {
        if !self.communication_replay_enabled() {
            // Off mode preserves legacy behavior and avoids replay bookkeeping.
            return 0;
        }
        self.sync_communication_consumption_mode();
        self.communication_consumption.allocate_send_sequence(edge)
    }

    fn consume_receive_identity(
        &mut self,
        identity: CommunicationIdentity,
    ) -> Result<CommunicationConsumeResult, CommunicationReplayError> {
        if !self.communication_replay_enabled() {
            // Off mode intentionally skips replay-consumption state and artifacts.
            return Ok(CommunicationConsumeResult {
                mode: CommunicationReplayMode::Off,
                pre_root: self.communication_consumption.root(),
                post_root: self.communication_consumption.root(),
                consumed_nullifier: None,
            });
        }
        self.sync_communication_consumption_mode();
        let result = self.communication_consumption.consume_receive(&identity)?;
        self.communication_consumption_artifacts.push(
            CommunicationConsumptionArtifact {
                tick: self.clock.tick,
                identity,
                mode: result.mode,
                pre_root: result.pre_root,
                post_root: result.post_root,
            },
            &self.config.observability_retention,
        );
        Ok(result)
    }

    fn session_open_plan(
        &mut self,
        image: &CodeImage,
    ) -> &crate::session::SessionOpenPlan {
        let key = format!("{image:p}");
        self.session_open_plans
            .entry(key)
            .or_insert_with(|| crate::session::SessionOpenPlan::new(&image.roles(), &image.local_types))
    }

    fn open_choreography_session(
        &mut self,
        plan: &crate::session::SessionOpenPlan,
    ) -> (SessionId, Vec<String>) {
        let sid = self.sessions.next_session_id();
        let roles = plan.roles().to_vec();
        self.sessions
            .open_with_sid_from_plan(sid, plan, &self.config.buffer_config);
        (sid, roles)
    }

    fn finalize_open_choreography_session(
        &mut self,
        sid: SessionId,
        roles: &[String],
        plan: &crate::session::SessionOpenPlan,
    ) -> Result<(), VMError> {
        self.next_session_id = self.sessions.next_session_id();
        self.bind_default_handlers_for_session(sid);
        self.intern_load_plan_symbols(plan, sid);
        self.monitor.set_kind(sid, SessionKind::Peer);
        self.resource_states
            .entry(sid)
            .or_default();
        self.apply_open_delta(sid)
            .map_err(VMError::PersistenceError)?;
        self.obs_trace.push(
            ObsEvent::Opened {
                tick: self.clock.tick,
                session: sid,
                roles: roles.to_vec(),
            },
            &self.config.observability_retention,
        );
        Ok(())
    }

    fn spawn_coroutine_for_role(
        &mut self,
        image: &CodeImage,
        sid: SessionId,
        role: &str,
    ) -> Result<(), VMError> {
        if self.coroutines.len() >= self.config.max_coroutines {
            return Err(VMError::TooManyCoroutines {
                max: self.config.max_coroutines,
            });
        }

        let program_id = self
            .programs
            .intern(image.programs.get(role).cloned().unwrap_or_default());
        if self.code.is_none() {
            let program = self
                .programs
                .get(program_id)
                .expect("interned program must exist")
                .clone();
            self.code = Some(program);
        }

        let coro_id = self.next_coro_id;
        self.next_coro_id += 1;

        let endpoint = Endpoint {
            sid,
            role: role.to_string(),
        };
        self.role_coroutines
            .entry(role.to_string())
            .or_default()
            .push(coro_id);
        if self.paused_roles.contains(role) {
            self.paused_coro_ids.insert(coro_id);
        }
        if self.timed_out_sites.contains_key(role) {
            self.timed_out_coro_ids.insert(coro_id);
        }
        let mut coro = Coroutine::new(
            coro_id,
            program_id,
            sid,
            role.to_string(),
            self.config.num_registers,
            self.config.initial_cost_budget,
        );
        coro.owned_endpoints.push(endpoint.clone());
        if !coro.regs.is_empty() {
            coro.regs[0] = Value::Endpoint(endpoint);
        }
        self.sched.add_ready(coro_id);
        self.coroutines.push(coro);
        self.coro_slots.insert(coro_id, self.coroutines.len() - 1);
        self.sync_ready_eligibility_for(coro_id);
        Ok(())
    }

    fn spawn_session_coroutines(
        &mut self,
        image: &CodeImage,
        sid: SessionId,
        roles: &[String],
    ) -> Result<(), VMError> {
        for role in roles {
            self.spawn_coroutine_for_role(image, sid, role)?;
        }
        Ok(())
    }

    /// Load a choreography from a verified code image.
    ///
    /// Creates a session (with local types), spawns coroutines per role,
    /// and returns the session ID. Type state is initialized in the
    /// session store — no separate monitor needed.
    ///
    /// # Errors
    ///
    /// Returns an error if session or coroutine limits are exceeded.
    pub fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError> {
        self.ensure_session_capacity()?;
        image.validate_runtime_shape().map_err(|reason| VMError::InvalidCodeImage { reason })?;
        let plan = self.session_open_plan(image).clone();
        let (sid, roles) = self.open_choreography_session(&plan);
        self.finalize_open_choreography_session(sid, &roles, &plan)?;
        self.programs.reserve(image.programs.len());
        self.coroutines.reserve(roles.len());
        self.spawn_session_coroutines(image, sid, &roles)?;
        Ok(sid)
    }

    /// Execute one scheduler round: advance at most one ready coroutine.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        #[cfg(debug_assertions)]
        debug_assert!(self.wf_vm_state().is_ok());
        if n == 0 {
            return Err(VMError::InvalidConcurrency { n });
        }
        self.last_sched_step = None;
        self.clock.advance();
        if self.all_done() {
            return Ok(StepResult::AllDone);
        }

        // Event ordering contract: topology effects ingress first each round,
        // before unblocking and scheduler selection.
        self.ingest_topology_events(handler)?;
        self.prune_expired_timeouts();
        self.try_unblock_receivers();
        self.ensure_ready_eligibility();
        #[cfg(debug_assertions)]
        self.debug_assert_ready_eligibility_consistent();
        if !self.sched.has_eligible_ready() {
            return Ok(StepResult::Stuck);
        }
        let coroutines = &self.coroutines;
        let coro_slots = &self.coro_slots;
        let Some(coro_id) = self.sched.pick_eligible_runnable(|id| {
            coro_slots
                .get(&id)
                .and_then(|idx| coroutines.get(*idx))
                .or_else(|| coroutines.get(id).filter(|coro| coro.id == id))
                .or_else(|| coroutines.iter().find(|coro| coro.id == id))
                .is_some_and(|coro| !coro.progress_tokens.is_empty())
        }) else {
            return Ok(StepResult::Stuck);
        };
        #[cfg(debug_assertions)]
        self.eligible_ready.remove(&coro_id);

        let result = self.exec_instr(coro_id, handler);

        match result {
            Ok(ExecOutcome::Continue) => {
                self.last_sched_step = Some(SchedStepDebug {
                    selected_coro: coro_id,
                    exec_status: SchedExecStatus::Continue,
                });
                self.sched.reschedule(coro_id);
                self.sync_ready_eligibility_for(coro_id);
            }
            Ok(ExecOutcome::Blocked(reason)) => {
                let yielded = matches!(reason, BlockReason::Spawn);
                self.last_sched_step = Some(SchedStepDebug {
                    selected_coro: coro_id,
                    exec_status: if yielded {
                        SchedExecStatus::Yielded
                    } else {
                        SchedExecStatus::Blocked
                    },
                });
                if yielded {
                    self.sched.reschedule(coro_id);
                    self.sync_ready_eligibility_for(coro_id);
                } else {
                    self.sched.mark_blocked(coro_id, reason);
                    #[cfg(debug_assertions)]
                    self.eligible_ready.remove(&coro_id);
                }
            }
            Ok(ExecOutcome::Halted) => {
                self.last_sched_step = Some(SchedStepDebug {
                    selected_coro: coro_id,
                    exec_status: SchedExecStatus::Halted,
                });
                self.sched.mark_done(coro_id);
                #[cfg(debug_assertions)]
                self.eligible_ready.remove(&coro_id);
                self.obs_trace.push(
                    ObsEvent::Halted {
                        tick: self.clock.tick,
                        coro_id,
                    },
                    &self.config.observability_retention,
                );
            }
            Err(fault) => {
                self.last_sched_step = Some(SchedStepDebug {
                    selected_coro: coro_id,
                    exec_status: SchedExecStatus::Faulted,
                });
                self.obs_trace.push(
                    ObsEvent::Faulted {
                        tick: self.clock.tick,
                        coro_id,
                        fault: fault.clone(),
                    },
                    &self.config.observability_retention,
                );
                let Some(idx) = self.coro_index(coro_id) else {
                    return Err(VMError::Fault { coro_id, fault });
                };
                self.coroutines[idx].status = CoroStatus::Faulted(fault.clone());
                self.sched.mark_done(coro_id);
                #[cfg(debug_assertions)]
                self.eligible_ready.remove(&coro_id);
                return Err(VMError::Fault { coro_id, fault });
            }
        }

        if self.all_done() {
            #[cfg(debug_assertions)]
            self.debug_assert_ready_eligibility_consistent();
            #[cfg(debug_assertions)]
            debug_assert!(self.wf_vm_state().is_ok());
            Ok(StepResult::AllDone)
        } else {
            #[cfg(debug_assertions)]
            self.debug_assert_ready_eligibility_consistent();
            #[cfg(debug_assertions)]
            debug_assert!(self.wf_vm_state().is_ok());
            Ok(StepResult::Continue)
        }
    }

    /// Execute one scheduler step: pick a coroutine, run one instruction.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn step(&mut self, handler: &dyn EffectHandler) -> Result<StepResult, VMError> {
        self.step_round(handler, 1)
    }

    /// Execute one scheduler round through the canonical kernel API.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        VMKernel::step_round(self, handler, n)
    }

    /// Run the VM until all coroutines complete or an error occurs, with concurrency N.
    ///
    /// `max_rounds` prevents infinite loops.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run_concurrent(
        &mut self,
        handler: &dyn EffectHandler,
        max_rounds: usize,
        concurrency: usize,
    ) -> Result<RunStatus, VMError> {
        VMKernel::run_concurrent(self, handler, max_rounds, concurrency)
    }

    /// Run the VM until all coroutines complete or an error occurs.
    ///
    /// `max_steps` prevents infinite loops.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_steps: usize,
    ) -> Result<RunStatus, VMError> {
        VMKernel::run(self, handler, max_steps)
    }

    /// Run with replayed effect outcomes captured from a prior execution.
    ///
    /// The `fallback` handler is only used for optional hooks not encoded in
    /// replay entries.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if replay data is exhausted/mismatched or a coroutine faults.
    pub fn run_replay(
        &mut self,
        fallback: &dyn EffectHandler,
        replay_trace: &[EffectTraceEntry],
        max_steps: usize,
    ) -> Result<RunStatus, VMError> {
        self.run_replay_shared(
            fallback,
            Arc::<[EffectTraceEntry]>::from(replay_trace),
            max_steps,
        )
    }

    /// Run with replayed effect outcomes using shared trace storage.
    ///
    /// Accepts an `Arc`-backed trace to avoid cloning when callers already hold
    /// shared replay buffers.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if replay data is exhausted/mismatched or a coroutine faults.
    pub fn run_replay_shared(
        &mut self,
        fallback: &dyn EffectHandler,
        replay_trace: Arc<[EffectTraceEntry]>,
        max_steps: usize,
    ) -> Result<RunStatus, VMError> {
        let replay = ReplayEffectHandler::with_fallback(replay_trace, fallback);
        self.run(&replay, max_steps)
    }

    /// Run concurrently with replayed effect outcomes.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if replay data is exhausted/mismatched or a coroutine faults.
    pub fn run_concurrent_replay(
        &mut self,
        fallback: &dyn EffectHandler,
        replay_trace: &[EffectTraceEntry],
        max_rounds: usize,
        concurrency: usize,
    ) -> Result<RunStatus, VMError> {
        self.run_concurrent_replay_shared(
            fallback,
            Arc::<[EffectTraceEntry]>::from(replay_trace),
            max_rounds,
            concurrency,
        )
    }

    /// Run concurrently with replayed outcomes using shared trace storage.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if replay data is exhausted/mismatched or a coroutine faults.
    pub fn run_concurrent_replay_shared(
        &mut self,
        fallback: &dyn EffectHandler,
        replay_trace: Arc<[EffectTraceEntry]>,
        max_rounds: usize,
        concurrency: usize,
    ) -> Result<RunStatus, VMError> {
        let replay = ReplayEffectHandler::with_fallback(replay_trace, fallback);
        self.run_concurrent(&replay, max_rounds, concurrency)
    }

    /// Get the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        self.obs_trace.as_slice()
    }

    /// Reap closed sessions once all associated coroutines are terminal.
    pub fn reap_closed_sessions(&mut self) -> Vec<ClosedSessionSummary> {
        let eligible: Vec<SessionId> = self
            .sessions
            .closed_session_ids()
            .into_iter()
            .filter(|sid| {
                self.coroutines
                    .iter()
                    .filter(|coro| coro.session_id == *sid)
                    .all(Coroutine::is_terminal)
            })
            .collect();
        if eligible.is_empty() {
            return Vec::new();
        }

        for sid in &eligible {
            self.monitor.remove_kind(*sid);
            self.resource_states.remove(sid);
            self.communication_consumption.prune_session(*sid);
        }
        self.coroutines.retain(|coro| {
            !(eligible.contains(&coro.session_id) && coro.is_terminal())
        });
        self.rebuild_coroutine_indexes();
        self.sessions.reap_sessions(&eligible)
    }

    /// Lean-aligned observable trace accessor.
    #[must_use]
    pub fn obs_trace(&self) -> &[ObsEvent] {
        self.obs_trace.as_slice()
    }

    /// Number of interned role symbols.
    #[must_use]
    pub fn role_symbol_count(&self) -> usize {
        self.role_symbols.len()
    }

    /// Number of interned label symbols.
    #[must_use]
    pub fn label_symbol_count(&self) -> usize {
        self.label_symbols.len()
    }

    /// Number of interned handler symbols.
    #[must_use]
    pub fn handler_symbol_count(&self) -> usize {
        self.handler_symbols.len()
    }

    /// Number of interned edge symbols.
    #[must_use]
    pub fn edge_symbol_count(&self) -> usize {
        self.edge_symbols.len()
    }

    /// Access VM configuration.
    #[must_use]
    pub fn config(&self) -> &VMConfig {
        &self.config
    }

    /// Last scheduler-dispatched step metadata, if any coroutine ran.
    #[must_use]
    pub fn last_sched_step(&self) -> Option<&SchedStepDebug> {
        self.last_sched_step.as_ref()
    }

    /// Scheduler-dispatched step counter.
    #[must_use]
    pub fn scheduler_step_count(&self) -> usize {
        self.sched.step_count()
    }

    /// Number of coroutine records in the VM.
    #[must_use]
    pub fn coroutine_count(&self) -> usize {
        self.coroutines.len()
    }

    /// Next session identifier reserved for allocation.
    #[must_use]
    pub fn next_session_id(&self) -> SessionId {
        self.sessions.next_session_id()
    }

    /// Number of active sessions in the VM.
    #[must_use]
    pub fn session_count(&self) -> usize {
        self.sessions.active_count()
    }

    /// Number of sessions still resident in the VM, including closed ones.
    #[must_use]
    pub fn live_session_count(&self) -> usize {
        self.sessions.live_count()
    }

    /// Approximate retained state for the VM runtime.
    #[must_use]
    pub fn memory_usage(&self) -> VmMemoryUsage {
        let session_store = self.sessions.memory_usage();
        let retained_bytes = self.retained_bytes(session_store.retained_bytes.total);
        VmMemoryUsage {
            session_store,
            coroutine_records: self.coroutines.len(),
            terminal_coroutines: self.coroutines.iter().filter(|coro| coro.is_terminal()).count(),
            program_count: self.programs.len(),
            program_instruction_count: self.programs.instruction_count(),
            obs_events: self.obs_trace.len(),
            effect_trace_entries: self.effect_trace.len(),
            communication_artifacts: self.communication_consumption_artifacts.len(),
            output_condition_checks: self.output_condition_checks.len(),
            retained_bytes,
        }
    }

    fn retained_bytes(&self, session_store_bytes: usize) -> VmRetainedBytes {
        let mut retained_bytes = VmRetainedBytes {
            session_store: session_store_bytes,
            coroutines: self.coroutines.iter().map(vm_serialized_bytes).sum(),
            programs: vm_serialized_bytes(&self.programs)
                .saturating_add(vm_serialized_bytes(&self.code)),
            resource_states: vm_serialized_bytes(&self.resource_states),
            traces: vm_serialized_bytes(&self.obs_trace)
                .saturating_add(vm_serialized_bytes(&self.effect_trace)),
            replay: vm_serialized_bytes(&self.communication_consumption)
                .saturating_add(vm_serialized_bytes(&self.communication_consumption_artifacts)),
            output_condition_checks: vm_serialized_bytes(&self.output_condition_checks),
            scheduler_and_control: vm_serialized_bytes(&self.sched)
                .saturating_add(vm_serialized_bytes(&self.eligible_ready))
                .saturating_add(vm_serialized_bytes(&self.paused_roles))
                .saturating_add(vm_serialized_bytes(&self.crashed_sites))
                .saturating_add(vm_serialized_bytes(&self.partitioned_edges))
                .saturating_add(vm_serialized_bytes(&self.corrupted_edges))
                .saturating_add(vm_serialized_bytes(&self.timed_out_sites))
                .saturating_add(vm_serialized_bytes(&self.clock))
                .saturating_add(vm_serialized_bytes(&self.last_sched_step))
                .saturating_add(vm_serialized_bytes(&self.handler_identity_anchor))
                .saturating_add(vm_serialized_bytes(&self.next_coro_id))
                .saturating_add(vm_serialized_bytes(&self.next_session_id)),
            symbols: vm_serialized_bytes(&self.role_symbols)
                .saturating_add(vm_serialized_bytes(&self.label_symbols))
                .saturating_add(vm_serialized_bytes(&self.handler_symbols))
                .saturating_add(vm_serialized_bytes(&self.edge_symbols)),
            guard_layer: vm_serialized_bytes(&self.guard_layer),
            monitor: vm_serialized_bytes(&self.monitor),
            arena: vm_serialized_bytes(&self.arena),
            total: 0,
        };
        retained_bytes.total = Self::retained_bytes_total(&retained_bytes);
        retained_bytes
    }

    fn retained_bytes_total(retained_bytes: &VmRetainedBytes) -> usize {
        retained_bytes
            .session_store
            .saturating_add(retained_bytes.coroutines)
            .saturating_add(retained_bytes.programs)
            .saturating_add(retained_bytes.resource_states)
            .saturating_add(retained_bytes.traces)
            .saturating_add(retained_bytes.replay)
            .saturating_add(retained_bytes.output_condition_checks)
            .saturating_add(retained_bytes.scheduler_and_control)
            .saturating_add(retained_bytes.symbols)
            .saturating_add(retained_bytes.guard_layer)
            .saturating_add(retained_bytes.monitor)
            .saturating_add(retained_bytes.arena)
    }

    /// Get recorded output-condition verification checks.
    #[must_use]
    pub fn output_condition_checks(&self) -> &[OutputConditionCheck] {
        self.output_condition_checks.as_slice()
    }

    /// Get recorded effect-trace entries.
    #[must_use]
    pub fn effect_trace(&self) -> &[EffectTraceEntry] {
        self.effect_trace.as_slice()
    }

    /// Deterministic communication replay-state root.
    #[must_use]
    pub fn communication_replay_root(&self) -> crate::verification::Hash {
        self.communication_consumption.root()
    }

    /// Receive-boundary replay-consumption artifacts.
    #[must_use]
    pub fn communication_consumption_artifacts(&self) -> &[CommunicationConsumptionArtifact] {
        self.communication_consumption_artifacts.as_slice()
    }

    /// Drain retained observable events in canonical insertion order.
    pub fn drain_obs_trace(&mut self) -> Vec<ObsEvent> {
        self.obs_trace.drain()
    }

    /// Drain retained effect-trace entries in canonical insertion order.
    pub fn drain_effect_trace(&mut self) -> Vec<EffectTraceEntry> {
        self.effect_trace.drain()
    }

    /// Drain retained output-condition diagnostics in canonical insertion order.
    pub fn drain_output_condition_checks(&mut self) -> Vec<OutputConditionCheck> {
        self.output_condition_checks.drain()
    }

    /// Drain retained communication replay-consumption artifacts in canonical insertion order.
    pub fn drain_communication_consumption_artifacts(
        &mut self,
    ) -> Vec<CommunicationConsumptionArtifact> {
        self.communication_consumption_artifacts.drain()
    }

    /// Canonical replay/state fragment for deterministic diffing and snapshots.
    #[must_use]
    pub fn canonical_replay_fragment(&self) -> CanonicalReplayFragmentV1 {
        let partitioned_edges = self.partitioned_edges.iter().cloned().collect();
        let corrupted_edges = self
            .corrupted_edges
            .iter()
            .map(|(edge, corruption)| (edge.clone(), *corruption))
            .collect();
        let timed_out_sites = self
            .timed_out_sites
            .iter()
            .map(|(site, until_tick)| (site.clone(), *until_tick))
            .collect();
        canonical_replay_fragment_v1(
            self.obs_trace.as_slice(),
            self.effect_trace.as_slice(),
            self.crashed_sites.iter().cloned().collect(),
            partitioned_edges,
            corrupted_edges,
            timed_out_sites,
            self.config.effect_determinism_tier,
            self.config.communication_replay_mode,
            Some(self.communication_consumption.root()),
            self.communication_consumption_artifacts.as_slice().to_vec(),
        )
    }

    /// Crashed sites currently active in topology state.
    #[must_use]
    pub fn crashed_sites(&self) -> &BTreeSet<SiteId> {
        &self.crashed_sites
    }

    /// Partitioned site-links currently active in topology state.
    #[must_use]
    pub fn partitioned_edges(&self) -> &BTreeSet<(SiteId, SiteId)> {
        &self.partitioned_edges
    }

    /// Corrupted directed edges currently active in topology state.
    #[must_use]
    pub fn corrupted_edges(&self) -> &BTreeMap<(SiteId, SiteId), CorruptionType> {
        &self.corrupted_edges
    }

    /// Active site timeouts.
    #[must_use]
    pub fn timed_out_sites(&self) -> &BTreeMap<SiteId, u64> {
        &self.timed_out_sites
    }
}
