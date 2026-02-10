//! Threaded VM backend (feature-gated, adapter runtime).
//!
//! Executes one coroutine per session per round in parallel, preserving
//! per-session trace equivalence with the cooperative VM.
//!
//! Semantic ownership remains in the canonical `VMKernel` contract.

use rayon::prelude::*;
use rayon::{ThreadPool, ThreadPoolBuilder};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock, TryLockError};

use telltale_types::LocalTypeR;

use crate::buffer::{BoundedBuffer, BufferConfig, EnqueueResult};
use crate::clock::SimClock;
use crate::coroutine::{BlockReason, CoroStatus, Coroutine, Fault, Value};
use crate::effect::{
    EffectHandler, EffectTraceEntry, ReplayEffectHandler, SendDecision, TopologyPerturbation,
};
use crate::instr::{Endpoint, Instr, PC};
use crate::intern::{StringId, SymbolTable};
use crate::kernel::{KernelMachine, VMKernel};
use crate::loader::CodeImage;
use crate::output_condition::{
    verify_output_condition, OutputConditionCheck, OutputConditionHint, OutputConditionMeta,
};
use crate::scheduler::Scheduler;
use crate::session::{
    unfold_if_var_with_scope, unfold_mu, Edge, SessionId, SessionState, SessionStatus, TypeEntry,
};
use crate::vm::{MonitorMode, ObsEvent, Program, StepResult, VMConfig, VMError};

/// Lane identifier in the threaded runtime.
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

/// Runtime contention and scheduling metrics for threaded execution.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContentionMetrics {
    /// Number of lock-contention observations (`try_lock` would block).
    pub lock_contention_events: u64,
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
    effect_trace: Vec<EffectTraceEntry>,
    next_effect_id: u64,
    output_condition_checks: Vec<OutputConditionCheck>,
    crashed_sites: BTreeSet<String>,
    partitioned_edges: BTreeSet<(String, String)>,
    lane_trace: Vec<LaneSelection>,
    pending_handoffs: VecDeque<LaneHandoff>,
    handoff_trace_log: Vec<LaneHandoff>,
    next_handoff_id: u64,
    contention_metrics: ContentionMetrics,
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
            effect_trace: Vec::new(),
            next_effect_id: 0,
            output_condition_checks: Vec::new(),
            crashed_sites: BTreeSet::new(),
            partitioned_edges: BTreeSet::new(),
            lane_trace: Vec::new(),
            pending_handoffs: VecDeque::new(),
            handoff_trace_log: Vec::new(),
            next_handoff_id: 0,
            contention_metrics: ContentionMetrics::default(),
        }
    }

    /// Load a choreography into the VM.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if session or coroutine limits are exceeded.
    pub fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError> {
        if self.sessions.active_count() >= self.config.max_sessions {
            return Err(VMError::TooManySessions {
                max: self.config.max_sessions,
            });
        }

        let roles = image.roles();
        let sid = self.sessions.open(
            roles.clone(),
            &self.config.buffer_config,
            &image.local_types,
        );

        self.trace.push(ObsEvent::Opened {
            tick: self.clock.tick,
            session: sid,
            roles: roles.clone(),
        });

        for role in &roles {
            if self.coroutines.len() >= self.config.max_coroutines {
                return Err(VMError::TooManyCoroutines {
                    max: self.config.max_coroutines,
                });
            }

            let program = image.programs.get(role).cloned().unwrap_or_default();
            let program_id = self.programs.len();
            self.programs.push(program);
            let coro_id = self.next_coro_id;
            self.next_coro_id += 1;

            let ep = Endpoint {
                sid,
                role: role.clone(),
            };
            let mut coro = Coroutine::new(
                coro_id,
                program_id,
                sid,
                role.clone(),
                self.config.num_registers,
                self.config.initial_cost_budget,
            );
            coro.owned_endpoints.push(ep);

            self.scheduler.add_ready(coro_id);
            self.coroutines.push(Arc::new(Mutex::new(coro)));
        }

        Ok(sid)
    }

    /// Execute one scheduler round: advance up to `n` ready coroutines.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    #[allow(clippy::too_many_lines)]
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
        self.try_unblock_receivers();

        let mut progressed = false;
        let mut remaining = n;
        let mut wave = 0_u64;

        // Run in parallel waves. Each wave schedules at most one coroutine per session,
        // and at most one coroutine per lane. A session may execute again in a later wave.
        while remaining > 0 {
            self.contention_metrics
                .observe_ready_depth(self.scheduler.ready_count());
            let picks = self.pick_ready(remaining)?;
            if picks.is_empty() {
                break;
            }
            self.contention_metrics.observe_wave_width(picks.len());
            for pick in &picks {
                self.lane_trace.push(LaneSelection {
                    tick,
                    wave,
                    coro_id: pick.coro_id,
                    session: pick.sid,
                    lane: pick.lane,
                });
            }

            let results: Vec<Result<(StepPack, Option<OutputConditionHint>), Fault>> =
                self.pool.install(|| {
                    picks
                        .par_iter()
                        .map(|pick| {
                            exec_instr(
                                &pick.coro,
                                &pick.session,
                                &self.sessions,
                                &self.programs,
                                &self.config,
                                &self.guard_resources,
                                handler,
                                tick,
                            )
                        })
                        .collect()
                });

            for (pick, result) in picks.iter().zip(results.into_iter()) {
                match result {
                    Ok((pack, output_hint)) => {
                        progressed = true;
                        match self.commit_pack(
                            &pick.coro,
                            &pick.session,
                            pack,
                            output_hint,
                            &handler.handler_identity(),
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

            remaining = remaining.saturating_sub(picks.len());
            wave = wave.saturating_add(1);
        }

        if self.all_done() {
            Ok(StepResult::AllDone)
        } else if progressed {
            Ok(StepResult::Continue)
        } else {
            Ok(StepResult::Stuck)
        }
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
    pub fn run(&mut self, handler: &dyn EffectHandler, max_rounds: usize) -> Result<(), VMError> {
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
    ) -> Result<(), VMError> {
        let replay = ReplayEffectHandler::with_fallback(replay_trace.to_vec(), fallback);
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
    ) -> Result<(), VMError> {
        VMKernel::run_concurrent(self, handler, max_rounds, concurrency)
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
    ) -> Result<(), VMError> {
        let replay = ReplayEffectHandler::with_fallback(replay_trace.to_vec(), fallback);
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

    fn apply_topology_event(&mut self, event: &TopologyPerturbation) {
        event.apply_to(&mut self.crashed_sites, &mut self.partitioned_edges);
    }

    fn ingest_topology_events(&mut self, handler: &dyn EffectHandler) -> Result<(), VMError> {
        let tick = self.clock.tick;
        let events = handler
            .topology_events(tick)
            .map_err(VMError::HandlerError)?;
        for event in events {
            self.apply_topology_event(&event);
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
                handler_identity: handler.handler_identity(),
                ordering_key: self.next_effect_id,
                topology: Some(event),
            });
            self.next_effect_id = self.next_effect_id.saturating_add(1);
        }
        Ok(())
    }

    fn try_unblock_receivers(&mut self) {
        let blocked_ids = self.scheduler.blocked_ids();
        for coro_id in blocked_ids {
            let reason = self.scheduler.block_reason(coro_id).cloned();
            if let Some(BlockReason::RecvWait { token, .. }) = reason {
                if let Some(session) = self.sessions.get(token.sid) {
                    let session = session.lock().expect("session lock poisoned");
                    let has_msg = session.roles.iter().any(|sender| {
                        sender != &token.role && session.has_message(sender, &token.role)
                    });
                    if has_msg {
                        self.scheduler.unblock(coro_id);
                    }
                }
            }
        }
    }

    fn pick_ready(&mut self, n: usize) -> Result<Vec<Picked>, VMError> {
        let mut picks = Vec::new();
        let mut used_sessions = BTreeSet::new();
        let mut used_lanes = BTreeSet::new();
        let mut used_footprints: BTreeSet<(SessionId, String)> = BTreeSet::new();
        let coros = &self.coroutines;
        let lane_count = self.lane_count.max(1);

        while picks.len() < n {
            let Some(coro_id) = VMKernel::select_ready_eligible(
                &mut self.scheduler,
                |id| coro_has_progress(coros, id),
                |id| {
                    let Some(coro) = coros.get(id) else {
                        return false;
                    };
                    let coro_guard = coro.lock().expect("coroutine lock poisoned");
                    let sid = coro_guard.session_id;
                    let lane = id % lane_count;
                    if used_sessions.contains(&sid) || used_lanes.contains(&lane) {
                        return false;
                    }

                    // Frame/diamond-inspired eligibility: picks within the same wave must
                    // have disjoint endpoint footprints to commute safely.
                    let footprint: Vec<(SessionId, String)> = coro_guard
                        .owned_endpoints
                        .iter()
                        .map(|ep| (ep.sid, ep.role.clone()))
                        .collect();
                    if footprint
                        .iter()
                        .any(|entry| used_footprints.contains(entry))
                    {
                        return false;
                    }
                    for entry in footprint {
                        used_footprints.insert(entry);
                    }
                    true
                },
            ) else {
                break;
            };

            if picks.len() >= n {
                break;
            }

            let coro = self
                .coroutines
                .get(coro_id)
                .cloned()
                .expect("coroutine exists");
            let sid = {
                let coro_guard = coro.lock().expect("coroutine lock poisoned");
                coro_guard.session_id
            };
            let lane = coro_id % lane_count;

            let session = self
                .sessions
                .get(sid)
                .ok_or(VMError::SessionNotFound(sid))?;
            used_sessions.insert(sid);
            used_lanes.insert(lane);
            picks.push(Picked {
                coro_id,
                sid,
                lane,
                coro,
                session,
            });
        }

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
            let digest = format!("events:{}:tick:{}", pack.events.len(), self.clock.tick);
            let meta = match output_hint {
                Some(h) => OutputConditionMeta::from_hint(h, digest),
                None => OutputConditionMeta::default_observable(digest),
            };
            let passed = verify_output_condition(&self.config.output_condition_policy, &meta);
            self.output_condition_checks.push(OutputConditionCheck {
                meta: meta.clone(),
                passed,
            });
            self.trace.push(ObsEvent::OutputConditionChecked {
                tick: self.clock.tick,
                predicate_ref: meta.predicate_ref.clone(),
                witness_ref: meta.witness_ref.clone(),
                output_digest: meta.output_digest.clone(),
                passed,
            });
            if !passed {
                return Err(Fault::OutputConditionFault {
                    predicate_ref: meta.predicate_ref,
                });
            }
        }

        for ev in &pack.events {
            self.intern_obs_event(ev);
            let maybe_entry = match ev {
                ObsEvent::Sent {
                    session,
                    from,
                    to,
                    label,
                    ..
                } => Some(EffectTraceEntry {
                    effect_id: self.next_effect_id,
                    effect_kind: "send_decision".to_string(),
                    inputs: json!({
                        "session": session,
                        "from": from,
                        "to": to,
                        "label": label,
                    }),
                    outputs: json!({"committed": true}),
                    handler_identity: handler_identity.to_string(),
                    ordering_key: self.clock.tick,
                    topology: None,
                }),
                ObsEvent::Received {
                    session,
                    from,
                    to,
                    label,
                    ..
                } => Some(EffectTraceEntry {
                    effect_id: self.next_effect_id,
                    effect_kind: "handle_recv".to_string(),
                    inputs: json!({
                        "session": session,
                        "from": from,
                        "to": to,
                        "label": label,
                    }),
                    outputs: json!({"committed": true}),
                    handler_identity: handler_identity.to_string(),
                    ordering_key: self.clock.tick,
                    topology: None,
                }),
                ObsEvent::Invoked { coro_id, role, .. } => Some(EffectTraceEntry {
                    effect_id: self.next_effect_id,
                    effect_kind: "invoke_step".to_string(),
                    inputs: json!({
                        "coro_id": coro_id,
                        "role": role,
                    }),
                    outputs: json!({"ok": true}),
                    handler_identity: handler_identity.to_string(),
                    ordering_key: self.clock.tick,
                    topology: None,
                }),
                ObsEvent::Acquired {
                    session,
                    role,
                    layer,
                    ..
                } => Some(EffectTraceEntry {
                    effect_id: self.next_effect_id,
                    effect_kind: "handle_acquire".to_string(),
                    inputs: json!({
                        "session": session,
                        "role": role,
                        "layer": layer,
                    }),
                    outputs: json!({"granted": true}),
                    handler_identity: handler_identity.to_string(),
                    ordering_key: self.clock.tick,
                    topology: None,
                }),
                ObsEvent::Released {
                    session,
                    role,
                    layer,
                    ..
                } => Some(EffectTraceEntry {
                    effect_id: self.next_effect_id,
                    effect_kind: "handle_release".to_string(),
                    inputs: json!({
                        "session": session,
                        "role": role,
                        "layer": layer,
                    }),
                    outputs: json!({"ok": true}),
                    handler_identity: handler_identity.to_string(),
                    ordering_key: self.clock.tick,
                    topology: None,
                }),
                _ => None,
            };
            if let Some(entry) = maybe_entry {
                self.effect_trace.push(entry);
                self.next_effect_id = self.next_effect_id.saturating_add(1);
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
                return Err(Fault::TransferFault {
                    message: "transfer source mismatch".into(),
                });
            }
            if !coro_guard.owned_endpoints.contains(endpoint) {
                return Err(Fault::TransferFault {
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
        let from_lane = self.lane_of_coro(from_coro).ok_or(Fault::TransferFault {
            message: "transfer source coroutine not found".into(),
        })?;
        let to_lane = self.lane_of_coro(to_coro).ok_or(Fault::TransferFault {
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
                    .ok_or(Fault::TransferFault {
                        message: "transfer source coroutine not found".into(),
                    })?;
            let mut source = lock_with_contention(&source_arc, &mut self.contention_metrics);
            move_endpoint_bundle(&endpoint, &mut source, None)
        } else {
            let source_arc =
                self.coroutines
                    .get(handoff.from_coro)
                    .cloned()
                    .ok_or(Fault::TransferFault {
                        message: "transfer source coroutine not found".into(),
                    })?;
            let target_arc =
                self.coroutines
                    .get(handoff.to_coro)
                    .cloned()
                    .ok_or(Fault::TransferFault {
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
            arc.lock().expect("mutex lock poisoned after contention")
        }
    }
}

fn move_endpoint_bundle(
    endpoint: &Endpoint,
    source: &mut Coroutine,
    target: Option<&mut Coroutine>,
) -> Result<(), Fault> {
    if !source.owned_endpoints.contains(endpoint) {
        return Err(Fault::TransferFault {
            message: "endpoint not owned".into(),
        });
    }

    let mut moved_tokens = Vec::new();
    source.progress_tokens.retain(|token| {
        if token == endpoint {
            moved_tokens.push(token.clone());
            false
        } else {
            true
        }
    });
    let mut moved_knowledge = Vec::new();
    source.knowledge_set.retain(|fact| {
        if fact.endpoint == *endpoint {
            moved_knowledge.push(fact.clone());
            false
        } else {
            true
        }
    });
    source.owned_endpoints.retain(|e| e != endpoint);

    if let Some(target) = target {
        target.owned_endpoints.push(endpoint.clone());
        target.progress_tokens.extend(moved_tokens);
        target.knowledge_set.extend(moved_knowledge);
    } else {
        source.owned_endpoints.push(endpoint.clone());
        source.progress_tokens.extend(moved_tokens);
        source.knowledge_set.extend(moved_knowledge);
    }

    Ok(())
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn exec_instr(
    coro: &Arc<Mutex<Coroutine>>,
    session: &Arc<Mutex<SessionState>>,
    store: &ThreadedSessionStore,
    programs: &[Vec<Instr>],
    config: &VMConfig,
    guard_resources: &Arc<Mutex<BTreeMap<String, Value>>>,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<(StepPack, Option<OutputConditionHint>), Fault> {
    let mut coro_guard = coro.lock().expect("coroutine lock poisoned");
    let pc = coro_guard.pc;
    let program = programs
        .get(coro_guard.program_id)
        .ok_or(Fault::PcOutOfBounds)?;
    if pc >= program.len() {
        return Err(Fault::PcOutOfBounds);
    }
    let instr = program[pc].clone();
    let ep = coro_guard
        .owned_endpoints
        .first()
        .cloned()
        .ok_or(Fault::PcOutOfBounds)?;
    let role = coro_guard.role.clone();
    let sid = coro_guard.session_id;

    monitor_precheck(config.monitor_mode, session, &ep, &role, &instr)?;
    if coro_guard.cost_budget < config.instruction_cost {
        return Err(Fault::OutOfCredits);
    }
    coro_guard.cost_budget -= config.instruction_cost;

    let pack = match instr {
        Instr::Send { val, .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_send(
                &mut coro_guard,
                &mut session_guard,
                &ep,
                &role,
                sid,
                val,
                handler,
                tick,
            )
        }
        Instr::Receive { dst, .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_recv(
                &mut coro_guard,
                &mut session_guard,
                &ep,
                &role,
                sid,
                dst,
                handler,
                tick,
            )
        }
        Instr::Halt => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_halt(&mut session_guard, &ep, tick)
        }
        Instr::Jump { target } => Ok(StepPack {
            coro_update: CoroUpdate::SetPc(target),
            type_update: None,
            events: vec![],
        }),
        Instr::Yield => Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![],
        }),
        Instr::Invoke { .. } => step_invoke(&mut coro_guard, &role, handler, tick),
        Instr::Acquire { layer, dst } => step_acquire(
            &mut coro_guard,
            &ep,
            &role,
            sid,
            &layer,
            dst,
            config,
            guard_resources,
            handler,
            tick,
        ),
        Instr::Release { layer, evidence } => step_release(
            &mut coro_guard,
            &ep,
            &role,
            sid,
            &layer,
            evidence,
            config,
            guard_resources,
            handler,
            tick,
        ),
        Instr::Fork { ghost } => step_fork(&mut coro_guard, &role, sid, ghost, config, tick),
        Instr::Join => step_join(&mut coro_guard, sid, tick),
        Instr::Abort => step_abort(&mut coro_guard, sid, tick),
        Instr::Transfer {
            endpoint,
            target,
            bundle,
        } => step_transfer(&mut coro_guard, &role, endpoint, target, bundle, tick),
        Instr::Tag { fact, dst } => step_tag(&mut coro_guard, &role, fact, dst, tick),
        Instr::Check {
            knowledge,
            target,
            dst,
        } => step_check(&mut coro_guard, &role, knowledge, target, dst, tick),
        Instr::Set { dst, val } => {
            let v = match val {
                crate::instr::ImmValue::Unit => Value::Unit,
                crate::instr::ImmValue::Int(i) => Value::Int(i),
                crate::instr::ImmValue::Real(r) => Value::Real(r),
                crate::instr::ImmValue::Bool(b) => Value::Bool(b),
                crate::instr::ImmValue::Str(s) => Value::Str(s),
            };
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst, val: v },
                type_update: None,
                events: vec![],
            })
        }
        Instr::Move { dst, src } => {
            let v = coro_guard.regs[usize::from(src)].clone();
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst, val: v },
                type_update: None,
                events: vec![],
            })
        }
        Instr::Choose { ref table, .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_choose(
                &mut coro_guard,
                &mut session_guard,
                &ep,
                &role,
                sid,
                table,
                handler,
                tick,
            )
        }
        Instr::Offer { ref label, .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_offer(
                &mut session_guard,
                &ep,
                &role,
                sid,
                label,
                &coro_guard.regs,
                handler,
                tick,
            )
        }
        Instr::Spawn { .. } => Err(Fault::SpecFault {
            message: "spawn not implemented in threaded VM".to_string(),
        }),
        Instr::Close { .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_close(&mut session_guard, &ep, sid, tick)
        }
        Instr::Open {
            ref roles,
            ref endpoints,
        } => step_open(&mut coro_guard, &role, store, roles, endpoints, tick),
    }?;

    let output_hint = if pack.events.is_empty() {
        None
    } else {
        Some(
            handler
                .output_condition_hint(sid, role.as_str(), &coro_guard.regs)
                .unwrap_or(OutputConditionHint {
                    predicate_ref: "vm.observable_output".to_string(),
                    witness_ref: None,
                }),
        )
    };

    Ok((pack, output_hint))
}

fn monitor_precheck(
    mode: MonitorMode,
    session: &Arc<Mutex<SessionState>>,
    ep: &Endpoint,
    role: &str,
    instr: &Instr,
) -> Result<(), Fault> {
    if mode == MonitorMode::Off {
        return Ok(());
    }
    match instr {
        Instr::Send { .. } | Instr::Offer { .. } => {
            let session_guard = session.lock().expect("session lock poisoned");
            let local_type = session_guard
                .local_types
                .get(ep)
                .ok_or_else(|| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: no type registered"),
                })?
                .current
                .clone();
            if matches!(local_type, LocalTypeR::Send { .. }) {
                Ok(())
            } else {
                Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: expected Send state, got {local_type:?}"),
                })
            }
        }
        Instr::Receive { .. } | Instr::Choose { .. } => {
            let session_guard = session.lock().expect("session lock poisoned");
            let local_type = session_guard
                .local_types
                .get(ep)
                .ok_or_else(|| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: no type registered"),
                })?
                .current
                .clone();
            if matches!(local_type, LocalTypeR::Recv { .. }) {
                Ok(())
            } else {
                Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("[monitor] {role}: expected Recv state, got {local_type:?}"),
                })
            }
        }
        _ => Ok(()),
    }
}

#[allow(clippy::too_many_arguments)]
fn step_send(
    coro: &mut Coroutine,
    session: &mut SessionState,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    _val_reg: u16,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let local_type = session
        .local_types
        .get(ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

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

    let (label, _vt, continuation) = branches
        .first()
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: send has no branches"),
        })?
        .clone();

    let decision = handler
        .send_decision(sid, role, &partner, &label.name, &coro.regs, None)
        .map_err(|e| Fault::InvokeFault { message: e })?;

    let enqueue = match decision {
        SendDecision::Deliver(payload) => session
            .send(role, &partner, payload)
            .map_err(|e| Fault::InvokeFault { message: e })?,
        SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
    };

    match enqueue {
        EnqueueResult::Ok => {}
        EnqueueResult::WouldBlock => {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::SendWait {
                    edge: Edge::new(sid, role.to_string(), partner.clone()),
                }),
                type_update: None,
                events: vec![],
            });
        }
        EnqueueResult::Full => {
            return Err(Fault::BufferFull {
                endpoint: ep.clone(),
            });
        }
        EnqueueResult::Dropped => {}
    }

    let original = session
        .local_types
        .get(ep)
        .map(|entry| &entry.original)
        .unwrap_or(&LocalTypeR::End);
    let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update,
        events: vec![ObsEvent::Sent {
            tick,
            edge: Edge::new(sid, role.to_string(), partner.clone()),
            session: sid,
            from: role.to_string(),
            to: partner,
            label: label.name.clone(),
        }],
    })
}

#[allow(clippy::too_many_arguments)]
fn step_recv(
    coro: &mut Coroutine,
    session: &mut SessionState,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    dst_reg: u16,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let local_type = session
        .local_types
        .get(ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    let (partner, branches) = match &local_type {
        LocalTypeR::Recv {
            partner, branches, ..
        } => (partner.clone(), branches.clone()),
        other => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: expected Recv, got {other:?}"),
            })
        }
    };

    let (label, _vt, continuation) = branches
        .first()
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: recv has no branches"),
        })?
        .clone();

    if !session.has_message(&partner, role) {
        return Ok(StepPack {
            coro_update: CoroUpdate::Block(BlockReason::RecvWait {
                edge: Edge::new(sid, partner.clone(), role.to_string()),
                token: ep.clone(),
            }),
            type_update: None,
            events: vec![],
        });
    }

    let val = session
        .recv(&partner, role)
        .ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;

    handler
        .handle_recv(role, &partner, &label.name, &mut coro.regs, &val)
        .map_err(|e| Fault::InvokeFault { message: e })?;

    let original = session
        .local_types
        .get(ep)
        .map(|entry| &entry.original)
        .unwrap_or(&LocalTypeR::End);
    let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst_reg, val },
        type_update,
        events: vec![ObsEvent::Received {
            tick,
            edge: Edge::new(sid, partner.clone(), role.to_string()),
            session: sid,
            from: partner,
            to: role.to_string(),
            label: label.name.clone(),
        }],
    })
}

fn step_halt(session: &mut SessionState, ep: &Endpoint, _tick: u64) -> Result<StepPack, Fault> {
    if let Some(lt) = session.local_types.get(ep) {
        if !matches!(lt.current, LocalTypeR::End) {
            // V1: permissive
        }
    }
    Ok(StepPack {
        coro_update: CoroUpdate::Halt,
        type_update: Some((ep.clone(), TypeUpdate::Remove)),
        events: vec![],
    })
}

fn step_invoke(
    coro: &mut Coroutine,
    role: &str,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let coro_id = coro.id;
    handler
        .step(role, &mut coro.regs)
        .map_err(|e| Fault::InvokeFault { message: e })?;

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Invoked {
            tick,
            coro_id,
            role: role.to_string(),
        }],
    })
}

fn guard_active(config: &VMConfig, layer: &str) -> Result<(), Fault> {
    if config.guard_layers.is_empty() {
        return Ok(());
    }
    match config.guard_layers.iter().find(|cfg| cfg.id == layer) {
        None => Err(Fault::AcquireFault {
            layer: layer.to_string(),
            message: "unknown layer".into(),
        }),
        Some(cfg) if !cfg.active => Err(Fault::AcquireFault {
            layer: layer.to_string(),
            message: "inactive layer".into(),
        }),
        Some(_) => Ok(()),
    }
}

#[allow(clippy::too_many_arguments)]
fn step_acquire(
    coro: &mut Coroutine,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    layer: &str,
    dst: u16,
    config: &VMConfig,
    guard_resources: &Arc<Mutex<BTreeMap<String, Value>>>,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    guard_active(config, layer)?;
    {
        let mut resources = guard_resources
            .lock()
            .expect("guard resources lock poisoned");
        resources.entry(layer.to_string()).or_insert(Value::Unit);
    }
    let decision = handler
        .handle_acquire(sid, role, layer, &coro.regs)
        .map_err(|e| Fault::AcquireFault {
            layer: layer.to_string(),
            message: e,
        })?;
    match decision {
        crate::effect::AcquireDecision::Grant(evidence) => {
            let mut resources = guard_resources
                .lock()
                .expect("guard resources lock poisoned");
            resources.insert(layer.to_string(), evidence.clone());
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg {
                    reg: dst,
                    val: evidence,
                },
                type_update: None,
                events: vec![ObsEvent::Acquired {
                    tick,
                    session: ep.sid,
                    role: role.to_string(),
                    layer: layer.to_string(),
                }],
            })
        }
        crate::effect::AcquireDecision::Block => Ok(StepPack {
            coro_update: CoroUpdate::Block(BlockReason::AcquireDenied {
                layer: layer.to_string(),
            }),
            type_update: None,
            events: vec![],
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn step_release(
    coro: &mut Coroutine,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    layer: &str,
    evidence: u16,
    config: &VMConfig,
    guard_resources: &Arc<Mutex<BTreeMap<String, Value>>>,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    guard_active(config, layer)?;
    {
        let mut resources = guard_resources
            .lock()
            .expect("guard resources lock poisoned");
        resources.entry(layer.to_string()).or_insert(Value::Unit);
    }
    let ev = coro
        .regs
        .get(usize::from(evidence))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    handler
        .handle_release(sid, role, layer, &ev, &coro.regs)
        .map_err(|e| Fault::AcquireFault {
            layer: layer.to_string(),
            message: e,
        })?;
    {
        let mut resources = guard_resources
            .lock()
            .expect("guard resources lock poisoned");
        resources.insert(layer.to_string(), ev.clone());
    }
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Released {
            tick,
            session: ep.sid,
            role: role.to_string(),
            layer: layer.to_string(),
        }],
    })
}

fn step_fork(
    coro: &mut Coroutine,
    role: &str,
    sid: SessionId,
    ghost: u16,
    config: &VMConfig,
    tick: u64,
) -> Result<StepPack, Fault> {
    if !config.speculation_enabled {
        return Err(Fault::SpecFault {
            message: "speculation disabled".into(),
        });
    }
    let ghost_val = coro
        .regs
        .get(usize::from(ghost))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let ghost_sid = match ghost_val {
        Value::Int(v) if v >= 0 => usize::try_from(v).map_err(|_| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: fork ghost id out of range"),
        })?,
        _ => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: fork expects integer ghost id"),
            })
        }
    };
    coro.spec_state = Some(crate::coroutine::SpeculationState {
        ghost_sid,
        depth: 0,
    });
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Forked {
            tick,
            session: sid,
            ghost: ghost_sid,
        }],
    })
}

fn step_join(coro: &mut Coroutine, sid: SessionId, tick: u64) -> Result<StepPack, Fault> {
    coro.spec_state = None;
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Joined { tick, session: sid }],
    })
}

fn step_abort(coro: &mut Coroutine, sid: SessionId, tick: u64) -> Result<StepPack, Fault> {
    coro.spec_state = None;
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Aborted { tick, session: sid }],
    })
}

fn step_transfer(
    coro: &mut Coroutine,
    role: &str,
    endpoint: u16,
    target: u16,
    _bundle: u16,
    tick: u64,
) -> Result<StepPack, Fault> {
    let ep_val = coro
        .regs
        .get(usize::from(endpoint))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let ep = match ep_val {
        Value::Endpoint(ep) => ep,
        _ => {
            return Err(Fault::TransferFault {
                message: format!("{role}: transfer expects endpoint register"),
            })
        }
    };
    let target_val = coro
        .regs
        .get(usize::from(target))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let target_id = match target_val {
        Value::Int(v) if v >= 0 => usize::try_from(v).map_err(|_| Fault::TransferFault {
            message: format!("{role}: target id out of range"),
        })?,
        _ => {
            return Err(Fault::TransferFault {
                message: format!("{role}: transfer expects target coroutine id"),
            })
        }
    };
    if !coro.owned_endpoints.contains(&ep) {
        return Err(Fault::TransferFault {
            message: "endpoint not owned".into(),
        });
    }

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Transferred {
            tick,
            session: ep.sid,
            role: role.to_string(),
            from: coro.id,
            to: target_id,
        }],
    })
}

fn step_tag(
    coro: &mut Coroutine,
    role: &str,
    fact_reg: u16,
    dst: u16,
    tick: u64,
) -> Result<StepPack, Fault> {
    let fact_val = coro
        .regs
        .get(usize::from(fact_reg))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let (endpoint, fact) = match fact_val {
        Value::Knowledge { endpoint, fact } => (endpoint, fact),
        _ => {
            return Err(Fault::TransferFault {
                message: format!("{role}: tag expects knowledge value"),
            })
        }
    };
    coro.knowledge_set.push(crate::coroutine::KnowledgeFact {
        endpoint: endpoint.clone(),
        fact: fact.clone(),
    });
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePcWriteReg {
            reg: dst,
            val: Value::Bool(true),
        },
        type_update: None,
        events: vec![ObsEvent::Tagged {
            tick,
            session: endpoint.sid,
            role: role.to_string(),
            fact,
        }],
    })
}

fn step_check(
    coro: &mut Coroutine,
    role: &str,
    knowledge: u16,
    target: u16,
    dst: u16,
    tick: u64,
) -> Result<StepPack, Fault> {
    let know_val = coro
        .regs
        .get(usize::from(knowledge))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let (endpoint, fact) = match know_val {
        Value::Knowledge { endpoint, fact } => (endpoint, fact),
        _ => {
            return Err(Fault::TransferFault {
                message: format!("{role}: check expects knowledge value"),
            })
        }
    };
    let target_val = coro
        .regs
        .get(usize::from(target))
        .ok_or(Fault::OutOfRegisters)?
        .clone();
    let target_role = match target_val {
        Value::Str(s) => s,
        _ => {
            return Err(Fault::TransferFault {
                message: format!("{role}: check expects target role string"),
            })
        }
    };
    let permitted = coro
        .knowledge_set
        .iter()
        .any(|k| k.endpoint == endpoint && k.fact == fact);
    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePcWriteReg {
            reg: dst,
            val: Value::Bool(permitted),
        },
        type_update: None,
        events: vec![ObsEvent::Checked {
            tick,
            session: endpoint.sid,
            role: role.to_string(),
            target: target_role,
            permitted,
        }],
    })
}

#[allow(clippy::too_many_arguments)]
fn step_choose(
    coro: &mut Coroutine,
    session: &mut SessionState,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    table: &[(String, PC)],
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let local_type = session
        .local_types
        .get(ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    let (partner, branches) = match &local_type {
        LocalTypeR::Recv {
            partner, branches, ..
        } => (partner.clone(), branches.clone()),
        other => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: Choose expects Recv, got {other:?}"),
            })
        }
    };

    if !session.has_message(&partner, role) {
        return Ok(StepPack {
            coro_update: CoroUpdate::Block(BlockReason::RecvWait {
                edge: Edge::new(sid, partner.clone(), role.to_string()),
                token: ep.clone(),
            }),
            type_update: None,
            events: vec![],
        });
    }

    let val = session
        .recv(&partner, role)
        .ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
    let label = match &val {
        Value::Label(l) => l.clone(),
        _ => {
            return Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: Choose expected Label value, got {val:?}"),
            })
        }
    };

    let (_lbl, _vt, continuation) = branches
        .iter()
        .find(|(l, _, _)| l.name == label)
        .ok_or_else(|| Fault::UnknownLabel {
            label: label.clone(),
        })?
        .clone();

    let target_pc = table
        .iter()
        .find(|(l, _)| *l == label)
        .map(|(_, pc)| *pc)
        .ok_or_else(|| Fault::UnknownLabel {
            label: label.clone(),
        })?;

    handler
        .handle_recv(role, &partner, &label, &mut coro.regs, &val)
        .map_err(|e| Fault::InvokeFault { message: e })?;

    let original = session
        .local_types
        .get(ep)
        .map(|entry| &entry.original)
        .unwrap_or(&LocalTypeR::End);
    let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

    Ok(StepPack {
        coro_update: CoroUpdate::SetPc(target_pc),
        type_update,
        events: vec![
            ObsEvent::Received {
                tick,
                edge: Edge::new(sid, partner.clone(), role.to_string()),
                session: sid,
                from: partner.clone(),
                to: role.to_string(),
                label: label.clone(),
            },
            ObsEvent::Chose {
                tick,
                edge: Edge::new(sid, partner, role.to_string()),
                label,
            },
        ],
    })
}

#[allow(clippy::too_many_arguments)]
fn step_offer(
    session: &mut SessionState,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    label: &str,
    state: &[Value],
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let local_type = session
        .local_types
        .get(ep)
        .ok_or_else(|| Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    match &local_type {
        LocalTypeR::Send {
            partner, branches, ..
        } => {
            let partner = partner.clone();
            let branches = branches.clone();

            let (_lbl, _vt, continuation) = branches
                .iter()
                .find(|(l, _, _)| l.name == label)
                .ok_or_else(|| Fault::UnknownLabel {
                    label: label.to_string(),
                })?
                .clone();

            let decision = handler
                .send_decision(
                    sid,
                    role,
                    &partner,
                    label,
                    state,
                    Some(Value::Label(label.to_string())),
                )
                .map_err(|e| Fault::InvokeFault { message: e })?;
            let enqueue = match decision {
                SendDecision::Deliver(payload) => session
                    .send(role, &partner, payload)
                    .map_err(|e| Fault::InvokeFault { message: e })?,
                SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
            };
            match enqueue {
                EnqueueResult::Ok => {}
                EnqueueResult::WouldBlock => {
                    return Ok(StepPack {
                        coro_update: CoroUpdate::Block(BlockReason::SendWait {
                            edge: Edge::new(sid, role.to_string(), partner.clone()),
                        }),
                        type_update: None,
                        events: vec![],
                    });
                }
                EnqueueResult::Full => {
                    return Err(Fault::BufferFull {
                        endpoint: ep.clone(),
                    });
                }
                EnqueueResult::Dropped => {}
            }

            let original = session
                .local_types
                .get(ep)
                .map(|entry| &entry.original)
                .unwrap_or(&LocalTypeR::End);
            let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePc,
                type_update,
                events: vec![
                    ObsEvent::Sent {
                        tick,
                        edge: Edge::new(sid, role.to_string(), partner.clone()),
                        session: sid,
                        from: role.to_string(),
                        to: partner.clone(),
                        label: label.to_string(),
                    },
                    ObsEvent::Offered {
                        tick,
                        edge: Edge::new(sid, role.to_string(), partner),
                        label: label.to_string(),
                    },
                ],
            })
        }
        other => Err(Fault::TypeViolation {
            expected: telltale_types::ValType::Unit,
            actual: telltale_types::ValType::Unit,
            message: format!("{role}: Offer expects Send, got {other:?}"),
        }),
    }
}

fn step_close(
    session: &mut SessionState,
    ep: &Endpoint,
    sid: SessionId,
    tick: u64,
) -> Result<StepPack, Fault> {
    let has_pending = session.buffers.values().any(|b| !b.is_empty());
    if has_pending {
        session.status = SessionStatus::Draining;
    } else {
        session.status = SessionStatus::Closed;
    }
    session.epoch = session.epoch.saturating_add(1);

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: Some((ep.clone(), TypeUpdate::Remove)),
        events: vec![
            ObsEvent::Closed { tick, session: sid },
            ObsEvent::EpochAdvanced {
                tick,
                sid,
                epoch: session.epoch,
            },
        ],
    })
}

fn step_open(
    coro: &mut Coroutine,
    role: &str,
    store: &ThreadedSessionStore,
    roles: &[String],
    endpoints: &[(String, u16)],
    tick: u64,
) -> Result<StepPack, Fault> {
    let sid = store.open(roles.to_vec(), &BufferConfig::default(), &BTreeMap::new());
    let mut coro_update = CoroUpdate::AdvancePc;
    if let Some((_, reg)) = endpoints.iter().find(|(r, _)| r == role) {
        if usize::from(*reg) >= coro.regs.len() {
            return Err(Fault::OutOfRegisters);
        }
        let ep = Endpoint {
            sid,
            role: role.to_string(),
        };
        coro_update = CoroUpdate::AdvancePcWriteReg {
            reg: *reg,
            val: Value::Endpoint(ep),
        };
    }

    Ok(StepPack {
        coro_update,
        type_update: None,
        events: vec![ObsEvent::Opened {
            tick,
            session: sid,
            roles: roles.to_vec(),
        }],
    })
}
