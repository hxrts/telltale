impl VM {
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

}
