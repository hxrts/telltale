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
    pub fn trace(&self) -> &[ObsEvent] {
        &self.trace
    }

    /// Get recorded effect-trace entries.
    #[must_use]
    pub fn effect_trace(&self) -> &[EffectTraceEntry] {
        &self.effect_trace
    }

    /// Canonical replay/state fragment for deterministic diffing and snapshots.
    #[must_use]
    pub fn canonical_replay_fragment(&self) -> CanonicalReplayFragmentV1 {
        let corrupted_edges = self
            .corrupted_edges
            .iter()
            .map(|(edge, corruption)| (edge.clone(), corruption.clone()))
            .collect();
        let timed_out_sites = self
            .timed_out_sites
            .iter()
            .map(|(site, until_tick)| (site.clone(), *until_tick))
            .collect();
        canonical_replay_fragment_v1(
            &self.trace,
            &self.effect_trace,
            self.crashed_sites.iter().cloned().collect(),
            self.partitioned_edges.iter().cloned().collect(),
            corrupted_edges,
            timed_out_sites,
            self.config.effect_determinism_tier,
        )
    }

    /// Get recorded output-condition verification checks.
    #[must_use]
    pub fn output_condition_checks(&self) -> &[OutputConditionCheck] {
        &self.output_condition_checks
    }

    /// Crashed sites currently active in topology state.
    #[must_use]
    pub fn crashed_sites(&self) -> &BTreeSet<String> {
        &self.crashed_sites
    }

    /// Partitioned site-links currently active in topology state.
    #[must_use]
    pub fn partitioned_edges(&self) -> &BTreeSet<(String, String)> {
        &self.partitioned_edges
    }

    /// Corruption policy by directed edge currently active in topology state.
    #[must_use]
    pub fn corrupted_edges(&self) -> &BTreeMap<(String, String), CorruptionType> {
        &self.corrupted_edges
    }

    /// Active timeout horizon by site.
    #[must_use]
    pub fn timed_out_sites(&self) -> &BTreeMap<String, u64> {
        &self.timed_out_sites
    }

    /// Get deterministic lane-selection trace.
    #[must_use]
    pub fn lane_trace(&self) -> &[LaneSelection] {
        &self.lane_trace
    }

    /// Get deterministic handoff records emitted by transfer/delegation.
    #[must_use]
    pub fn handoff_trace(&self) -> &[LaneHandoff] {
        &self.handoff_trace_log
    }

    /// Get contention and scheduling metrics.
    #[must_use]
    pub fn contention_metrics(&self) -> &ContentionMetrics {
        &self.contention_metrics
    }

    /// Deterministic lane assignment for a coroutine id.
    #[must_use]
    pub fn lane_of_coro(&self, coro_id: usize) -> Option<LaneId> {
        self.coroutines.get(coro_id)?;
        Some(self.assign_lane(coro_id))
    }

    /// Lean-aligned lane accessor.
    #[must_use]
    pub fn lane_of(&self, coro_id: usize) -> Option<LaneId> {
        self.lane_of_coro(coro_id)
    }

    /// Lane-partitioned view of the global ready queue.
    #[must_use]
    pub fn lane_queues(&self) -> BTreeMap<LaneId, Vec<usize>> {
        let lane_count = self.lane_count.max(1);
        let mut out: BTreeMap<LaneId, Vec<usize>> =
            (0..lane_count).map(|lane| (lane, Vec::new())).collect();
        for coro_id in self.scheduler.ready_snapshot() {
            let lane = self.assign_lane(coro_id);
            out.entry(lane).or_default().push(coro_id);
        }
        out
    }

    /// Compatibility shim: migrate the global ready queue view into lane queues.
    #[must_use]
    pub fn migrate_ready_queue_to_lane_queues(&self) -> BTreeMap<LaneId, Vec<usize>> {
        self.lane_queues()
    }

    /// Lean-aligned cross-lane handoff trace accessor.
    #[must_use]
    pub fn cross_lane_handoff(&self) -> &[LaneHandoff] {
        &self.handoff_trace_log
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

    /// Serializable snapshot of current lane scheduler state.
    #[must_use]
    pub fn lane_scheduler_state(&self) -> LaneSchedulerState {
        LaneSchedulerState {
            lane_count: self.lane_count.max(1),
            lane_queues: self.lane_queues(),
            blocked: self.scheduler.blocked_snapshot(),
            step_count: self.scheduler.step_count(),
        }
    }

    /// Access the simulation clock.
    #[must_use]
    pub fn clock(&self) -> &SimClock {
        &self.clock
    }

    fn assign_lane(&self, coro_id: usize) -> LaneId {
        coro_id % self.lane_count.max(1)
    }

    fn all_done(&self) -> bool {
        self.coroutines
            .iter()
            .all(|coro| coro.lock().expect("coroutine lock poisoned").is_terminal())
    }

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
        self.timed_out_sites
            .retain(|_, until_tick| *until_tick > tick);
    }

    fn apply_site_failure(&mut self, site: &str) {
        let reason = format!("site {site} crashed");

        let sessions = self
            .sessions
            .sessions
            .read()
            .expect("session store lock poisoned");
        for session in sessions.values() {
            let mut session_guard = session.lock().expect("session lock poisoned");
            if !session_guard.roles.iter().any(|role| role == site) {
                continue;
            }
            if matches!(
                session_guard.status,
                SessionStatus::Closed | SessionStatus::Cancelled | SessionStatus::Faulted { .. }
            ) {
                continue;
            }
            session_guard.status = SessionStatus::Faulted {
                reason: reason.clone(),
            };
        }

        let mut faulted = Vec::new();
        for coro in &self.coroutines {
            let mut guard = coro.lock().expect("coroutine lock poisoned");
            if guard.role == site && !guard.is_terminal() {
                let fault = Fault::Invoke {
                    message: reason.clone(),
                };
                guard.status = CoroStatus::Faulted(fault.clone());
                faulted.push((guard.id, fault));
            }
        }
        for (coro_id, fault) in faulted {
            self.scheduler.mark_done(coro_id);
            self.trace.push(ObsEvent::Faulted {
                tick: self.clock.tick,
                coro_id,
                fault,
            });
        }
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

    fn apply_topology_event(&mut self, event: &TopologyPerturbation) {
        if let Some(site) = event.crashed_site() {
            self.crashed_sites.insert(site.to_string());
            self.apply_site_failure(site);
            return;
        }
        if let Some((from, to)) = event.partition_pair() {
            self.partitioned_edges
                .insert((from.to_string(), to.to_string()));
            self.partitioned_edges
                .insert((to.to_string(), from.to_string()));
            return;
        }
        if let Some((from, to)) = event.healed_pair() {
            self.partitioned_edges
                .remove(&(from.to_string(), to.to_string()));
            self.partitioned_edges
                .remove(&(to.to_string(), from.to_string()));
            self.corrupted_edges
                .remove(&(from.to_string(), to.to_string()));
            self.corrupted_edges
                .remove(&(to.to_string(), from.to_string()));
            return;
        }
        if let Some((from, to, corruption)) = event.corruption_edge() {
            self.corrupted_edges
                .insert((from.to_string(), to.to_string()), corruption);
            return;
        }
        if let Some((site, duration)) = event.timeout_site() {
            let until_tick = self
                .clock
                .tick
                .saturating_add(self.duration_to_ticks(duration));
            self.timed_out_sites.insert(site.to_string(), until_tick);
        }
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
