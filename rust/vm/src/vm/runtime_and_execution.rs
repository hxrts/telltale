impl VM {
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
    }

    fn ensure_session_capacity(&self) -> Result<(), VMError> {
        if self.sessions.active_count() >= self.config.max_sessions {
            return Err(VMError::TooManySessions {
                max: self.config.max_sessions,
            });
        }
        Ok(())
    }

    fn open_choreography_session(
        &mut self,
        image: &CodeImage,
    ) -> Result<(SessionId, Vec<String>), VMError> {
        let roles = image.roles();
        let sid = self.sessions.next_session_id();
        self.sessions.open_with_sid(
            sid,
            roles.clone(),
            &self.config.buffer_config,
            &image.local_types,
        );
        self.next_session_id = self.sessions.next_session_id();
        self.bind_default_handlers_for_session(sid);
        self.monitor.set_kind(sid, SessionKind::Peer);
        self.resource_states
            .entry(sid)
            .or_default();
        self.apply_open_delta(sid)
            .map_err(VMError::PersistenceError)?;
        self.obs_trace.push(ObsEvent::Opened {
            tick: self.clock.tick,
            session: sid,
            roles: roles.clone(),
        });
        Ok((sid, roles))
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

        let program = image.programs.get(role).cloned().unwrap_or_default();
        let program_id = self.programs.len();
        self.programs.push(program.clone());
        if self.code.is_none() {
            self.code = Some(program);
        }

        let coro_id = self.next_coro_id;
        self.next_coro_id += 1;

        let endpoint = Endpoint {
            sid,
            role: role.to_string(),
        };
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
        let (sid, roles) = self.open_choreography_session(image)?;
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
        if self.coroutines.iter().all(|c| c.is_terminal()) {
            return Ok(StepResult::AllDone);
        }

        // Event ordering contract: topology effects ingress first each round,
        // before unblocking and scheduler selection.
        self.ingest_topology_events(handler)?;
        self.prune_expired_timeouts();
        self.try_unblock_receivers();

        let paused_roles = &self.paused_roles;
        let crashed_sites = &self.crashed_sites;
        let timed_out_sites = &self.timed_out_sites;
        let coroutines = &self.coroutines;
        let has_eligible = self.sched.any_ready(|id| {
            coroutines
                .get(id)
                .map(|c| {
                    !paused_roles.contains(&c.role)
                        && !crashed_sites.contains(&c.role)
                        && !timed_out_sites.contains_key(&c.role)
                })
                .unwrap_or(false)
        });
        if !has_eligible {
            return Ok(StepResult::Stuck);
        }
        let Some(coro_id) = VMKernel::select_ready_eligible(
            &mut self.sched,
            |id| {
                coroutines
                    .get(id)
                    .map(|c| !c.progress_tokens.is_empty())
                    .unwrap_or(false)
            },
            |id| {
                coroutines
                    .get(id)
                    .map(|c| {
                        !paused_roles.contains(&c.role)
                            && !crashed_sites.contains(&c.role)
                            && !timed_out_sites.contains_key(&c.role)
                    })
                    .unwrap_or(false)
            },
        ) else {
            return Ok(StepResult::Stuck);
        };

        let result = self.exec_instr(coro_id, handler);

        match result {
            Ok(ExecOutcome::Continue) => {
                self.last_sched_step = Some(SchedStepDebug {
                    selected_coro: coro_id,
                    exec_status: SchedExecStatus::Continue,
                });
                self.sched.reschedule(coro_id);
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
                } else {
                    self.sched.mark_blocked(coro_id, reason);
                }
            }
            Ok(ExecOutcome::Halted) => {
                self.last_sched_step = Some(SchedStepDebug {
                    selected_coro: coro_id,
                    exec_status: SchedExecStatus::Halted,
                });
                self.sched.mark_done(coro_id);
                self.obs_trace.push(ObsEvent::Halted {
                    tick: self.clock.tick,
                    coro_id,
                });
            }
            Err(fault) => {
                self.last_sched_step = Some(SchedStepDebug {
                    selected_coro: coro_id,
                    exec_status: SchedExecStatus::Faulted,
                });
                self.obs_trace.push(ObsEvent::Faulted {
                    tick: self.clock.tick,
                    coro_id,
                    fault: fault.clone(),
                });
                let idx = self.coro_index(coro_id);
                self.coroutines[idx].status = CoroStatus::Faulted(fault.clone());
                self.sched.mark_done(coro_id);
                return Err(VMError::Fault { coro_id, fault });
            }
        }

        if self.coroutines.iter().all(|c| c.is_terminal()) {
            #[cfg(debug_assertions)]
            debug_assert!(self.wf_vm_state().is_ok());
            Ok(StepResult::AllDone)
        } else {
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
        &self.obs_trace
    }

    /// Lean-aligned observable trace accessor.
    #[must_use]
    pub fn obs_trace(&self) -> &[ObsEvent] {
        &self.obs_trace
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

    /// Get recorded output-condition verification checks.
    #[must_use]
    pub fn output_condition_checks(&self) -> &[OutputConditionCheck] {
        &self.output_condition_checks
    }

    /// Get recorded effect-trace entries.
    #[must_use]
    pub fn effect_trace(&self) -> &[EffectTraceEntry] {
        &self.effect_trace
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
            &self.obs_trace,
            &self.effect_trace,
            self.crashed_sites.iter().cloned().collect(),
            partitioned_edges,
            corrupted_edges,
            timed_out_sites,
            self.config.effect_determinism_tier,
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
