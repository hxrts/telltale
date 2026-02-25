pub type LaneId = usize;

/// Deterministic lane selection record for one scheduled coroutine.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneSelection {
    /// Scheduler tick for this selection.
    pub tick: u64,
    /// Parallel wave index within this scheduler round.
    pub wave: u64,
    /// Chosen coroutine id.
    pub coro_id: usize,
    /// Session id of the chosen coroutine.
    pub session: SessionId,
    /// Lane selected for execution.
    pub lane: LaneId,
}

/// Deterministic lane handoff record created by transfer/delegation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneHandoff {
    /// Monotonic handoff sequence id.
    pub handoff_id: u64,
    /// Scheduler tick where the handoff was emitted.
    pub tick: u64,
    /// Session carrying the endpoint.
    pub session: SessionId,
    /// Endpoint role being handed off.
    pub endpoint_role: String,
    /// Source coroutine id.
    pub from_coro: usize,
    /// Destination coroutine id.
    pub to_coro: usize,
    /// Source lane id.
    pub from_lane: LaneId,
    /// Destination lane id.
    pub to_lane: LaneId,
}

/// Serializable snapshot of lane-aware scheduler state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneSchedulerState {
    /// Configured lane count.
    pub lane_count: usize,
    /// Ready queue partitioned by lane.
    pub lane_queues: BTreeMap<LaneId, Vec<usize>>,
    /// Blocked coroutine reasons.
    pub blocked: BTreeMap<usize, BlockReason>,
    /// Scheduler step counter.
    pub step_count: usize,
}

/// Certificate for one threaded scheduler wave plan.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveCertificate {
    /// Planned waves for this round.
    pub waves: Vec<Vec<usize>>,
    /// Scheduler step at planning time.
    pub planner_step: usize,
}

/// Runtime contention and scheduling metrics for threaded execution.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContentionMetrics {
    /// Aggregate contention count for backward-compatible dashboards.
    pub lock_contention_events: u64,
    /// Number of mutex lock-contention observations (`try_lock` would block).
    pub mutex_lock_contention_events: u64,
    /// Number of planner conflicts (lane/session/footprint admissions).
    pub planner_conflict_events: u64,
    /// Maximum scheduler ready-queue depth observed.
    pub max_ready_queue_depth: usize,
    /// Maximum parallel wave width observed.
    pub max_wave_width: usize,
    /// Number of cross-lane endpoint transfer handoffs.
    pub cross_lane_transfer_count: u64,
    /// Number of handoff records that have been applied.
    pub handoff_applied_count: u64,
}

impl ContentionMetrics {
    fn observe_ready_depth(&mut self, depth: usize) {
        self.max_ready_queue_depth = self.max_ready_queue_depth.max(depth);
    }

    fn observe_wave_width(&mut self, width: usize) {
        self.max_wave_width = self.max_wave_width.max(width);
    }
}

/// Threaded VM runtime. Uses OS threads for coroutine execution.
pub struct ThreadedVM {
    config: VMConfig,
    programs: Vec<Program>,
    coroutines: Vec<Arc<Mutex<Coroutine>>>,
    sessions: ThreadedSessionStore,
    scheduler: Scheduler,
    trace: Vec<ObsEvent>,
    role_symbols: SymbolTable,
    label_symbols: SymbolTable,
    clock: SimClock,
    next_coro_id: usize,
    pool: ThreadPool,
    workers: usize,
    lane_count: usize,
    guard_resources: Arc<Mutex<BTreeMap<String, Value>>>,
    resource_states: Arc<Mutex<BTreeMap<SessionId, ResourceState>>>,
    effect_trace: Vec<EffectTraceEntry>,
    next_effect_id: u64,
    output_condition_checks: Vec<OutputConditionCheck>,
    crashed_sites: BTreeSet<String>,
    partitioned_edges: BTreeSet<(String, String)>,
    corrupted_edges: BTreeMap<(String, String), CorruptionType>,
    timed_out_sites: BTreeMap<String, u64>,
    lane_trace: Vec<LaneSelection>,
    pending_handoffs: VecDeque<LaneHandoff>,
    handoff_trace_log: Vec<LaneHandoff>,
    next_handoff_id: u64,
    contention_metrics: ContentionMetrics,
    force_invalid_wave_certificate_once: bool,
    handler_identity_anchor: Option<String>,
}

impl KernelMachine for ThreadedVM {
    fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        ThreadedVM::kernel_step_round(self, handler, n)
    }
}

/// Session-scoped locks for concurrent execution.
#[derive(Debug, Default)]
pub struct SessionLock {
    locks: BTreeMap<SessionId, Mutex<()>>,
}

impl SessionLock {
    /// Create an empty lock table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Ensure a lock exists for a session.
    pub fn ensure(&mut self, sid: SessionId) {
        self.locks.entry(sid).or_insert_with(|| Mutex::new(()));
    }
}

#[derive(Debug, Default)]
struct ThreadedSessionStore {
    sessions: RwLock<BTreeMap<SessionId, Arc<Mutex<SessionState>>>>,
    next_id: AtomicUsize,
}

impl ThreadedSessionStore {
    fn new() -> Self {
        Self::default()
    }

    fn open(
        &self,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> SessionId {
        let sid = self.next_id.fetch_add(1, Ordering::SeqCst);

        let mut local_types = BTreeMap::new();
        for role in &roles {
            if let Some(lt) = initial_types.get(role) {
                let ep = Endpoint {
                    sid,
                    role: role.clone(),
                };
                local_types.insert(
                    ep,
                    TypeEntry {
                        current: unfold_mu(lt),
                        original: lt.clone(),
                    },
                );
            }
        }

        let mut buffers = BTreeMap::new();
        for from in &roles {
            for to in &roles {
                if from != to {
                    let edge = Edge::new(sid, from.clone(), to.clone());
                    buffers.insert(edge, BoundedBuffer::new(buffer_config));
                }
            }
        }

        let state = SessionState {
            sid,
            roles,
            local_types,
            buffers,
            auth_leaves: BTreeMap::new(),
            auth_trees: BTreeMap::new(),
            auth_roots: BTreeMap::new(),
            edge_handlers: BTreeMap::new(),
            edge_traces: BTreeMap::new(),
            status: SessionStatus::Active,
            epoch: 0,
        };

        let mut sessions = self.sessions.write().expect("session store lock poisoned");
        sessions.insert(sid, Arc::new(Mutex::new(state)));
        sid
    }

    fn get(&self, sid: SessionId) -> Option<Arc<Mutex<SessionState>>> {
        self.sessions
            .read()
            .expect("session store lock poisoned")
            .get(&sid)
            .cloned()
    }

    fn active_count(&self) -> usize {
        let sessions = self.sessions.read().expect("session store lock poisoned");
        sessions
            .values()
            .filter(|session| {
                session.lock().expect("session lock poisoned").status == SessionStatus::Active
            })
            .count()
    }
}

struct Picked {
    coro_id: usize,
    sid: SessionId,
    lane: LaneId,
    coro: Arc<Mutex<Coroutine>>,
    session: Arc<Mutex<SessionState>>,
}

struct PlannedWave {
    picks: Vec<Picked>,
    /// When true, stop this round after executing this wave to preserve
    /// canonical single-step fallback semantics.
    stop_after_wave: bool,
}

/// How to update the coroutine after an instruction.
enum CoroUpdate {
    /// Advance PC by 1, status = Ready.
    AdvancePc,
    /// Set PC to target (for Jmp), status = Ready.
    SetPc(PC),
    /// Block with given reason. PC unchanged.
    Block(BlockReason),
    /// Halt (Done). PC unchanged.
    Halt,
    /// Advance PC by 1, write a value to a register, status = Ready.
    AdvancePcWriteReg { reg: u16, val: Value },
    /// Advance PC by 1 and spawn a child coroutine.
    AdvancePcSpawnChild { target: PC, args: Vec<u16> },
}

/// Type update action for commit.
enum TypeUpdate {
    /// Advance to a new local type.
    Advance(LocalTypeR),
    /// Advance to a new local type and update the original (for Mu unfolding).
    AdvanceWithOriginal(LocalTypeR, LocalTypeR),
    /// Remove the type entry (endpoint completed).
    Remove,
}

/// Resolve a continuation and build the appropriate `TypeUpdate`.
fn resolve_type_update(
    cont: &LocalTypeR,
    original: &LocalTypeR,
    ep: &Endpoint,
) -> (LocalTypeR, Option<(Endpoint, TypeUpdate)>) {
    let (resolved, new_scope) = unfold_if_var_with_scope(cont, original);
    let update = if let Some(mu) = new_scope {
        Some((
            ep.clone(),
            TypeUpdate::AdvanceWithOriginal(resolved.clone(), mu),
        ))
    } else {
        Some((ep.clone(), TypeUpdate::Advance(resolved.clone())))
    };
    (resolved, update)
}

fn coro_has_progress(coros: &[Arc<Mutex<Coroutine>>], coro_id: usize) -> bool {
    coros
        .get(coro_id)
        .map(|coro| {
            !coro
                .lock()
                .expect("coroutine lock poisoned")
                .progress_tokens
                .is_empty()
        })
        .unwrap_or(false)
}

/// Atomic result of executing one instruction.
struct StepPack {
    /// How to update the coroutine.
    coro_update: CoroUpdate,
    /// Type advancement, if any. `None` means no type change (e.g., block, control flow).
    type_update: Option<(Endpoint, TypeUpdate)>,
    /// Observable events to emit.
    events: Vec<ObsEvent>,
}

/// Internal outcome after committing a `StepPack`.
enum ExecOutcome {
    /// Instruction completed, coroutine continues.
    Continue,
    /// Coroutine blocked on a resource.
    Blocked(BlockReason),
    /// Coroutine halted normally.
    Halted,
}

struct WavePlannerState {
    used_sessions: BTreeSet<SessionId>,
    used_lanes: BTreeSet<usize>,
    used_footprints: BTreeSet<(SessionId, u64)>,
    conflict_events: u64,
    lane_count: usize,
    allow_same_session_disjoint: bool,
}

impl WavePlannerState {
    fn new(lane_count: usize, allow_same_session_disjoint: bool) -> Self {
        Self {
            used_sessions: BTreeSet::new(),
            used_lanes: BTreeSet::new(),
            used_footprints: BTreeSet::new(),
            conflict_events: 0,
            lane_count,
            allow_same_session_disjoint,
        }
    }

    fn note_conflict(&mut self) {
        self.conflict_events = self.conflict_events.saturating_add(1);
    }
}

impl ThreadedVM {
    /// Create with thread pool sized to available OS parallelism.
    #[must_use]
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
