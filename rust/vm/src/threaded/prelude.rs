/// Logical lane identifier used by threaded scheduler records.
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
    programs: ProgramStore,
    coroutines: Vec<Arc<Mutex<Coroutine>>>,
    sessions: ThreadedSessionStore,
    scheduler: Scheduler,
    trace: Vec<ObsEvent>,
    role_symbols: SymbolTable,
    label_symbols: SymbolTable,
    handler_symbols: SymbolTable,
    edge_symbols: EdgeSymbolTable,
    clock: SimClock,
    next_coro_id: usize,
    non_terminal_coroutines: usize,
    pool: ThreadPool,
    workers: usize,
    lane_count: usize,
    guard_resources: Arc<Mutex<BTreeMap<String, Value>>>,
    resource_states: Arc<Mutex<BTreeMap<SessionId, ResourceState>>>,
    communication_consumption: Arc<Mutex<DefaultCommunicationConsumption>>,
    communication_consumption_artifacts: Arc<Mutex<Vec<CommunicationConsumptionArtifact>>>,
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

    #[allow(clippy::needless_pass_by_value)]
    fn open(
        &self,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> SessionId {
        let plan = SessionOpenPlan::new(&roles, initial_types);
        self.open_from_plan(&plan, buffer_config)
    }

    fn open_from_plan(
        &self,
        plan: &SessionOpenPlan,
        buffer_config: &BufferConfig,
    ) -> SessionId {
        let sid = self.next_id.fetch_add(1, Ordering::SeqCst);
        let state = SessionState::from_open_plan(sid, plan, buffer_config);

        let mut sessions = self.sessions.write().expect("threaded VM lock poisoned");
        sessions.insert(sid, Arc::new(Mutex::new(state)));
        sid
    }

    fn get(&self, sid: SessionId) -> Option<Arc<Mutex<SessionState>>> {
        self.sessions
            .read()
            .expect("threaded VM lock poisoned")
            .get(&sid)
            .cloned()
    }

    fn active_count(&self) -> usize {
        let sessions = self.sessions.read().expect("threaded VM lock poisoned");
        sessions
            .values()
            .filter(|session| {
                session.lock().expect("threaded VM lock poisoned").status == SessionStatus::Active
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

fn write_coro_reg(coro: &mut Coroutine, reg: u16, value: Value) -> Result<(), Fault> {
    let slot = coro
        .regs
        .get_mut(usize::from(reg))
        .ok_or(Fault::OutOfRegisters)?;
    *slot = value;
    Ok(())
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
                .expect("threaded VM lock poisoned")
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
