impl ThreadedVM {
    pub fn auto(config: VMConfig) -> Self {
        let workers = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        Self::with_workers(config, workers)
    }

    /// Create with explicit worker count.
    ///
    /// # Panics
    ///
    /// Panics if the thread pool cannot be created.
    #[must_use]
    pub fn with_workers(config: VMConfig, workers: usize) -> Self {
        config.assert_invariants();
        let worker_count = workers.max(1);
        let pool = ThreadPoolBuilder::new()
            .num_threads(worker_count)
            .build()
            .expect("thread pool build failed");
        let tick_duration = config.tick_duration;
        let scheduler = Scheduler::new(config.sched_policy.clone());
        let mut guard_resources = BTreeMap::new();
        for layer in &config.guard_layers {
            guard_resources.insert(layer.id.clone(), Value::Unit);
        }
        Self {
            config,
            programs: Vec::new(),
            coroutines: Vec::new(),
            sessions: ThreadedSessionStore::new(),
            scheduler,
            trace: Vec::new(),
            role_symbols: SymbolTable::new(),
            label_symbols: SymbolTable::new(),
            clock: SimClock::new(tick_duration),
            next_coro_id: 0,
            pool,
            workers: worker_count,
            lane_count: worker_count,
            guard_resources: Arc::new(Mutex::new(guard_resources)),
            resource_states: Arc::new(Mutex::new(BTreeMap::new())),
            effect_trace: Vec::new(),
            next_effect_id: 0,
            output_condition_checks: Vec::new(),
            crashed_sites: BTreeSet::new(),
            partitioned_edges: BTreeSet::new(),
            corrupted_edges: BTreeMap::new(),
            timed_out_sites: BTreeMap::new(),
            lane_trace: Vec::new(),
            pending_handoffs: VecDeque::new(),
            handoff_trace_log: Vec::new(),
            next_handoff_id: 0,
            contention_metrics: ContentionMetrics::default(),
            force_invalid_wave_certificate_once: false,
            handler_identity_anchor: None,
        }
    }

    /// Load a choreography into the VM.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if session or coroutine limits are exceeded.
    ///
    /// # Panics
    ///
    /// Panics if a session lock is poisoned.
    fn ensure_session_capacity(&self) -> Result<(), VMError> {
        if self.sessions.active_count() >= self.config.max_sessions {
            return Err(VMError::TooManySessions {
                max: self.config.max_sessions,
            });
        }
        Ok(())
    }

    fn ensure_coroutine_capacity(&self) -> Result<(), VMError> {
        if self.coroutines.len() >= self.config.max_coroutines {
            return Err(VMError::TooManyCoroutines {
                max: self.config.max_coroutines,
            });
        }
        Ok(())
    }

    fn bind_default_handlers_for_session(&mut self, sid: SessionId, roles: &[String]) {
        if let Some(session) = self.sessions.get(sid) {
            let mut session_guard = session.lock().expect("session lock poisoned");
            for sender in roles {
                for receiver in roles {
                    session_guard.edge_handlers.insert(
                        Edge::new(sid, sender.clone(), receiver.clone()),
                        "default_handler".to_string(),
                    );
                }
            }
        }
    }

    fn spawn_role_coroutine(
        &mut self,
        sid: SessionId,
        role: &str,
        image: &CodeImage,
    ) -> Result<(), VMError> {
        self.ensure_coroutine_capacity()?;
        let role_key = role.to_string();
        let program = image.programs.get(&role_key).cloned().unwrap_or_default();
        let program_id = self.programs.len();
        self.programs.push(program);
        let coro_id = self.next_coro_id;
        self.next_coro_id += 1;

        let ep = Endpoint {
            sid,
            role: role_key.clone(),
        };
        let mut coro = Coroutine::new(
            coro_id,
            program_id,
            sid,
            role_key,
            self.config.num_registers,
            self.config.initial_cost_budget,
        );
        coro.owned_endpoints.push(ep.clone());
        if !coro.regs.is_empty() {
            coro.regs[0] = Value::Endpoint(ep);
        }
        self.scheduler.add_ready(coro_id);
        self.coroutines.push(Arc::new(Mutex::new(coro)));
        Ok(())
    }

    pub fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError> {
        self.ensure_session_capacity()?;

        let roles = image.roles();
        let sid = self.sessions.open(
            roles.clone(),
            &self.config.buffer_config,
            &image.local_types,
        );
        self.bind_default_handlers_for_session(sid, &roles);
        self.resource_states
            .lock()
            .expect("resource state lock poisoned")
            .entry(sid)
            .or_default();

        self.trace.push(ObsEvent::Opened {
            tick: self.clock.tick,
            session: sid,
            roles: roles.clone(),
        });

        for role in &roles {
            self.spawn_role_coroutine(sid, role, image)?;
        }

        Ok(sid)
    }

    /// Execute one scheduler round: advance up to `n` ready coroutines.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub(crate) fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        if n == 0 {
            return Err(VMError::InvalidConcurrency { n });
        }
        self.clock.advance();
        let tick = self.clock.tick;
        if self.all_done() {
            return Ok(StepResult::AllDone);
        }

        // Event ordering contract: topology effects ingress first each round,
        // before unblocking and scheduler selection.
        self.ingest_topology_events(handler)?;
        self.prune_expired_timeouts();
        self.try_unblock_receivers();

        let mut progressed = false;
        let mut remaining = match self.config.threaded_round_semantics {
            ThreadedRoundSemantics::CanonicalOneStep => 1,
            ThreadedRoundSemantics::WaveParallelExtension => n,
        };
        let mut wave = 0_u64;
        let enforce_certified_wave = remaining > 1;

        // Run in parallel waves. Each wave schedules at most one coroutine per session,
        // and at most one coroutine per lane. A session may execute again in a later wave.
        while remaining > 0 {
            let Some(planned_wave) = self.plan_next_wave(remaining, enforce_certified_wave)? else {
                break;
            };

            let stop_after_wave = planned_wave.stop_after_wave;
            let picks = planned_wave.picks;
            self.record_lane_trace(&picks, tick, wave);
            let picks_len = picks.len();
            progressed |= self.execute_picks(picks, handler, tick)?;

            remaining = remaining.saturating_sub(picks_len);
            wave = wave.saturating_add(1);
            if stop_after_wave {
                break;
            }
        }

        if self.all_done() {
            Ok(StepResult::AllDone)
        } else if progressed {
            Ok(StepResult::Continue)
        } else {
            Ok(StepResult::Stuck)
        }
    }

    fn plan_next_wave(
        &mut self,
        budget: usize,
        enforce_certified_wave: bool,
    ) -> Result<Option<PlannedWave>, VMError> {
        self.contention_metrics
            .observe_ready_depth(self.scheduler.ready_count());
        let ready_before_pick = self.scheduler.ready_set_snapshot();
        let picks = self.pick_ready(budget)?;
        if picks.is_empty() {
            return Ok(None);
        }

        if enforce_certified_wave {
            let cert = WaveCertificate {
                waves: vec![picks.iter().map(|pick| pick.coro_id).collect()],
                planner_step: self.scheduler.step_count(),
            };
            if !self.check_wave_certificate(&cert, &ready_before_pick) {
                self.restore_picks_to_ready(&picks);
                let fallback = self.pick_ready(1)?;
                if fallback.is_empty() {
                    return Ok(None);
                }
                return Ok(Some(PlannedWave {
                    picks: fallback,
                    stop_after_wave: true,
                }));
            }
        }

        Ok(Some(PlannedWave {
            picks,
            stop_after_wave: false,
        }))
    }

    fn execute_picks(
        &mut self,
        picks: Vec<Picked>,
        handler: &dyn EffectHandler,
        tick: u64,
    ) -> Result<bool, VMError> {
        let handler_identity = handler.handler_identity();
        self.enforce_handler_identity_contract(&handler_identity)?;
        self.contention_metrics.observe_wave_width(picks.len());
        let step_ctx = ThreadedStepCtx {
            config: &self.config,
            guard_resources: &self.guard_resources,
            resource_states: &self.resource_states,
            crashed_sites: &self.crashed_sites,
            partitioned_edges: &self.partitioned_edges,
            corrupted_edges: &self.corrupted_edges,
            timed_out_sites: &self.timed_out_sites,
            handler,
            tick,
        };
        let exec_ctx = ThreadedExecCtx {
            store: &self.sessions,
            programs: &self.programs,
            step: step_ctx,
        };
        let results: Vec<Result<(StepPack, Option<OutputConditionHint>), Fault>> =
            self.pool.install(|| {
                picks
                    .par_iter()
                    .map(|pick| exec_instr(&pick.coro, &pick.session, &exec_ctx))
                    .collect()
            });

        let mut progressed = false;
        for (pick, result) in picks.into_iter().zip(results.into_iter()) {
            match result {
                Ok((pack, output_hint)) => {
                    progressed = true;
                    match self.commit_pack(
                        &pick.coro,
                        &pick.session,
                        pack,
                        output_hint,
                        &handler_identity,
                    ) {
                        Ok(outcome) => match outcome {
                            ExecOutcome::Continue => {
                                self.scheduler.reschedule(pick.coro_id);
                            }
                            ExecOutcome::Blocked(reason) => {
                                self.scheduler.mark_blocked(pick.coro_id, reason);
                            }
                            ExecOutcome::Halted => {
                                self.scheduler.mark_done(pick.coro_id);
                                self.trace.push(ObsEvent::Halted {
                                    tick,
                                    coro_id: pick.coro_id,
                                });
                            }
                        },
                        Err(fault) => {
                            self.trace.push(ObsEvent::Faulted {
                                tick,
                                coro_id: pick.coro_id,
                                fault: fault.clone(),
                            });
                            let mut coro = pick.coro.lock().expect("coroutine lock poisoned");
                            coro.status = CoroStatus::Faulted(fault.clone());
                            self.scheduler.mark_done(pick.coro_id);
                            return Err(VMError::Fault {
                                coro_id: pick.coro_id,
                                fault,
                            });
                        }
                    }
                }
                Err(fault) => {
                    self.trace.push(ObsEvent::Faulted {
                        tick,
                        coro_id: pick.coro_id,
                        fault: fault.clone(),
                    });
                    let mut coro = pick.coro.lock().expect("coroutine lock poisoned");
                    coro.status = CoroStatus::Faulted(fault.clone());
                    self.scheduler.mark_done(pick.coro_id);
                    return Err(VMError::Fault {
                        coro_id: pick.coro_id,
                        fault,
                    });
                }
            }
        }
        Ok(progressed)
    }

    fn record_lane_trace(&mut self, picks: &[Picked], tick: u64, wave: u64) {
        for pick in picks {
            self.lane_trace.push(LaneSelection {
                tick,
                wave,
                coro_id: pick.coro_id,
                session: pick.sid,
                lane: pick.lane,
            });
        }
    }

    fn restore_picks_to_ready(&mut self, picks: &[Picked]) {
        for pick in picks {
            self.scheduler.reschedule(pick.coro_id);
        }
    }

    fn check_wave_certificate(
        &mut self,
        cert: &WaveCertificate,
        ready_before_pick: &BTreeSet<usize>,
    ) -> bool {
        if self.force_invalid_wave_certificate_once {
            self.force_invalid_wave_certificate_once = false;
            return false;
        }
        if cert.planner_step != self.scheduler.step_count() {
            return false;
        }
        let mut seen = BTreeSet::new();
        for wave in &cert.waves {
            for coro_id in wave {
                if !seen.insert(*coro_id) {
                    return false;
                }
            }
            if !self.check_wave_admissible(wave, ready_before_pick) {
                return false;
            }
        }
        true
    }

    fn check_wave_admissible(&self, wave: &[usize], ready_before_pick: &BTreeSet<usize>) -> bool {
        let mut seen = BTreeSet::new();
        let mut lanes = BTreeSet::new();
        let mut footprint = BTreeSet::new();

        for coro_id in wave {
            if !seen.insert(*coro_id) || !ready_before_pick.contains(coro_id) {
                return false;
            }
            let Some(coro) = self.coroutines.get(*coro_id) else {
                return false;
            };
            let guard = coro.lock().expect("coroutine lock poisoned");
            if !matches!(guard.status, CoroStatus::Ready | CoroStatus::Speculating) {
                return false;
            }
            let lane = *coro_id % self.lane_count.max(1);
            if !lanes.insert(lane) {
                return false;
            }
            for endpoint in &guard.owned_endpoints {
                let key = (endpoint.sid, endpoint.role.clone());
                if !footprint.insert(key) {
                    return false;
                }
            }
        }
        true
    }

    /// Execute one scheduler round through the canonical kernel API.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        VMKernel::step_round(self, handler, n)
    }

    /// Run the VM until completion, using the configured worker count.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run(
        &mut self,
        handler: &dyn EffectHandler,
        max_rounds: usize,
    ) -> Result<RunStatus, VMError> {
        self.run_concurrent(handler, max_rounds, self.workers.max(1))
    }

    /// Run the VM using replayed effect outcomes from a prior execution.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if replay data is exhausted/mismatched or any coroutine faults.
    pub fn run_replay(
        &mut self,
        fallback: &dyn EffectHandler,
        replay_trace: &[EffectTraceEntry],
        max_rounds: usize,
    ) -> Result<RunStatus, VMError> {
        self.run_replay_shared(
            fallback,
            Arc::<[EffectTraceEntry]>::from(replay_trace),
            max_rounds,
        )
    }

    /// Run the VM with replayed outcomes using shared trace storage.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if replay data is exhausted/mismatched or any coroutine faults.
    pub fn run_replay_shared(
        &mut self,
        fallback: &dyn EffectHandler,
        replay_trace: Arc<[EffectTraceEntry]>,
        max_rounds: usize,
    ) -> Result<RunStatus, VMError> {
        let replay = ReplayEffectHandler::with_fallback(replay_trace, fallback);
        self.run(&replay, max_rounds)
    }

    /// Run the VM with explicit concurrency.
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

    /// Test/debug hook: force the next wave-certificate check to fail.
    pub fn force_invalid_wave_certificate_once(&mut self) {
        self.force_invalid_wave_certificate_once = true;
    }

    /// Run with explicit concurrency and replayed effect outcomes.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if replay data is exhausted/mismatched or any coroutine faults.
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

    /// Run with explicit concurrency and replayed outcomes using shared trace storage.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if replay data is exhausted/mismatched or any coroutine faults.
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
}
