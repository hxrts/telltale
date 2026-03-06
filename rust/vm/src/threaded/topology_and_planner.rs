impl ThreadedVM {
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

    fn note_status_transition(&mut self, was_terminal: bool, is_terminal: bool) {
        if !was_terminal && is_terminal {
            self.non_terminal_coroutines = self.non_terminal_coroutines.saturating_sub(1);
        } else if was_terminal && !is_terminal {
            self.non_terminal_coroutines = self.non_terminal_coroutines.saturating_add(1);
        }
    }

    fn all_done(&self) -> bool {
        self.non_terminal_coroutines == 0
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
            .expect("threaded VM lock poisoned");
        for session in sessions.values() {
            let mut session_guard = session.lock().expect("threaded VM lock poisoned");
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
        let mut newly_terminal = 0_usize;
        for coro in &self.coroutines {
            let mut guard = coro.lock().expect("threaded VM lock poisoned");
            if guard.role == site && !guard.is_terminal() {
                let fault = Fault::Invoke {
                    message: reason.clone(),
                };
                guard.status = CoroStatus::Faulted(fault.clone());
                newly_terminal = newly_terminal.saturating_add(1);
                faulted.push((guard.id, fault));
            }
        }
        self.non_terminal_coroutines = self
            .non_terminal_coroutines
            .saturating_sub(newly_terminal);
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
                let guard = coro.lock().expect("threaded VM lock poisoned");
                self.crashed_sites.contains(&guard.role)
                    || self.timed_out_sites.contains_key(&guard.role)
            });
            if should_skip {
                continue;
            }
            let reason = self.scheduler.block_reason(coro_id).cloned();
            if let Some(BlockReason::Recv { token, .. }) = reason {
                if let Some(session) = self.sessions.get(token.sid) {
                    let session = session.lock().expect("threaded VM lock poisoned");
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
        let coro_guard = coro.lock().expect("threaded VM lock poisoned");
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
            .ok_or(VMError::Fault {
                coro_id,
                fault: Fault::Speculation {
                    message: "scheduler selected missing coroutine".to_string(),
                },
            })?;
        let sid = {
            let coro_guard = coro.lock().expect("threaded VM lock poisoned");
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
        let mut planner = WavePlannerState::new(
            self.lane_count.max(1),
            self.config.footprint_guided_wave_widening,
        );

        while picks.len() < n {
            let Some(coro_id) = ({
                let coros = &self.coroutines;
                VMKernel::select_ready_eligible(
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
                )
            }) else {
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
}
