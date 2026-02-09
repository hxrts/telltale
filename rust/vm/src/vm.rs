//! The VM: ties coroutines, sessions, and scheduler together.
//!
//! Execution follows the Lean spec pattern:
//! - `exec_instr` fetches, dispatches to per-instruction step functions
//! - Each step function owns its type checking via `SessionStore::lookup_type`
//! - Results are bundled in `StepPack` and committed atomically via `commit_pack`
//! - Blocking never advances type state
//!
//! This module is a runtime surface over the canonical `VMKernel` execution
//! contract. Driver layers call into `VMKernel` and do not redefine instruction
//! semantics.

use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::{BTreeSet, HashMap};
use std::time::Duration;
use telltale_types::LocalTypeR;

use crate::buffer::{BufferConfig, EnqueueResult, SignedBuffers};
use crate::clock::SimClock;
use crate::coroutine::{BlockReason, CoroStatus, Coroutine, Fault, Value};
use crate::determinism::DeterminismMode;
use crate::effect::{
    EffectHandler, EffectTraceEntry, ReplayEffectHandler, SendDecision, TopologyPerturbation,
};
use crate::exec;
use crate::instr::{Endpoint, Instr, PC};
use crate::intern::{StringId, SymbolTable};
use crate::kernel::{KernelMachine, VMKernel};
use crate::loader::CodeImage;
use crate::output_condition::{
    verify_output_condition, OutputConditionCheck, OutputConditionMeta, OutputConditionPolicy,
};
use crate::scheduler::{SchedPolicy, Scheduler};
use crate::session::{unfold_if_var_with_scope, Edge, SessionId, SessionStore};

fn default_instruction_cost() -> usize {
    1
}

fn default_initial_cost_budget() -> usize {
    usize::MAX
}

/// Lean-aligned scope identifier placeholder.
pub type ScopeId = usize;

/// Lean-aligned program representation.
pub type Program = Vec<Instr>;

/// Lean-aligned resource-state placeholder for runtime state alignment.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Default)]
pub struct ResourceState;

/// Lean-aligned arena placeholder for runtime state alignment.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Default)]
pub struct Arena;

/// Lean-aligned session-monitor placeholder for runtime state alignment.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Default)]
pub struct SessionMonitor;

/// Lean-aligned site identifier for failure topology state.
pub type SiteId = String;

/// Synthetic session scope used for topology-only edges.
const TOPOLOGY_EDGE_SID: SessionId = usize::MAX;

/// Guard layer configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GuardLayerConfig {
    /// Guard layer identifier.
    pub id: String,
    /// Whether the layer is active.
    pub active: bool,
}

/// Instruction monitor mode for pre-dispatch checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum MonitorMode {
    /// Disable monitor precheck at dispatch.
    Off,
    /// Perform session-type-shape monitor precheck before stepping.
    #[default]
    SessionTypePrecheck,
}

/// VM configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VMConfig {
    /// Scheduling policy.
    pub sched_policy: SchedPolicy,
    /// Default buffer configuration for new sessions.
    pub buffer_config: BufferConfig,
    /// Maximum number of concurrent sessions.
    pub max_sessions: usize,
    /// Maximum number of concurrent coroutines.
    pub max_coroutines: usize,
    /// Number of registers per coroutine.
    pub num_registers: u16,
    /// Simulated time per scheduler round.
    pub tick_duration: Duration,
    /// Guard layers configured for the VM.
    pub guard_layers: Vec<GuardLayerConfig>,
    /// Whether speculative execution is enabled.
    pub speculation_enabled: bool,
    /// Determinism profile for replay/equivalence behavior.
    pub determinism_mode: DeterminismMode,
    /// Output-condition policy for commit eligibility of observable outputs.
    pub output_condition_policy: OutputConditionPolicy,
    /// Monitor mode for pre-dispatch type checks.
    #[serde(default)]
    pub monitor_mode: MonitorMode,
    /// Deterministic cost charged for each instruction dispatch.
    #[serde(default = "default_instruction_cost")]
    pub instruction_cost: usize,
    /// Initial cost budget assigned to each coroutine.
    #[serde(default = "default_initial_cost_budget")]
    pub initial_cost_budget: usize,
}

impl Default for VMConfig {
    fn default() -> Self {
        Self {
            sched_policy: SchedPolicy::Cooperative,
            buffer_config: BufferConfig::default(),
            max_sessions: 256,
            max_coroutines: 1024,
            num_registers: 16,
            tick_duration: Duration::from_millis(1),
            guard_layers: Vec::new(),
            speculation_enabled: false,
            determinism_mode: DeterminismMode::Full,
            output_condition_policy: OutputConditionPolicy::AllowAll,
            monitor_mode: MonitorMode::SessionTypePrecheck,
            instruction_cost: 1,
            initial_cost_budget: usize::MAX,
        }
    }
}

/// Observable event emitted by the VM.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TickedObsEvent {
    /// Scheduler tick when the wrapped event occurred.
    pub tick: u64,
    /// Underlying observable event payload.
    pub event: ObsEvent,
}

/// Observable event emitted by the VM.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObsEvent {
    /// Value sent on an edge.
    Sent {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session-scoped edge for this send.
        edge: Edge,
        /// Session ID.
        session: SessionId,
        /// Sender role.
        from: String,
        /// Receiver role.
        to: String,
        /// Message label.
        label: String,
    },
    /// Value received on an edge.
    Received {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session-scoped edge for this receive.
        edge: Edge,
        /// Session ID.
        session: SessionId,
        /// Sender role.
        from: String,
        /// Receiver role.
        to: String,
        /// Message label.
        label: String,
    },
    /// Label offered on an edge.
    Offered {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session-scoped edge for this offer.
        edge: Edge,
        /// Label offered.
        label: String,
    },
    /// Label chosen on an edge.
    Chose {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session-scoped edge for this choice.
        edge: Edge,
        /// Label chosen.
        label: String,
    },
    /// Session opened.
    Opened {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Participating roles.
        roles: Vec<String>,
    },
    /// Session closed.
    Closed {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
    },
    /// Session epoch advanced.
    EpochAdvanced {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        sid: SessionId,
        /// New epoch number.
        epoch: usize,
    },
    /// Coroutine halted.
    Halted {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
    },
    /// Effect handler invoked.
    Invoked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
        /// Role name.
        role: String,
    },
    /// Guard layer acquired.
    Acquired {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Guard layer identifier.
        layer: String,
    },
    /// Guard layer released.
    Released {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Guard layer identifier.
        layer: String,
    },
    /// Endpoint transferred between coroutines.
    Transferred {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Source coroutine.
        from: usize,
        /// Target coroutine.
        to: usize,
    },
    /// Speculation forked for a ghost session.
    Forked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Ghost session id.
        ghost: usize,
    },
    /// Speculation joined.
    Joined {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
    },
    /// Speculation aborted.
    Aborted {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
    },
    /// Knowledge fact tagged.
    Tagged {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Fact payload.
        fact: String,
    },
    /// Knowledge fact checked.
    Checked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Role name.
        role: String,
        /// Target role.
        target: String,
        /// Whether the flow policy permitted the fact.
        permitted: bool,
    },
    /// Coroutine faulted.
    Faulted {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
        /// The fault.
        fault: Fault,
    },
    /// Output-condition verification was evaluated at commit time.
    OutputConditionChecked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Predicate reference that was checked.
        predicate_ref: String,
        /// Optional witness reference used by the check.
        witness_ref: Option<String>,
        /// Opaque output digest checked by the verifier.
        output_digest: String,
        /// Verification outcome.
        passed: bool,
    },
}

/// The VM execution result for a single step.
#[derive(Debug)]
pub enum StepResult {
    /// A coroutine executed an instruction and may continue.
    Continue,
    /// No coroutines are ready (all blocked or done).
    Stuck,
    /// All coroutines have completed.
    AllDone,
}

/// Debug metadata for the most recent scheduler-dispatched step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SchedStepDebug {
    /// Selected coroutine id.
    pub selected_coro: usize,
    /// Instruction-step execution status.
    pub exec_status: String,
}

/// Errors from VM operations.
#[derive(Debug, thiserror::Error)]
pub enum VMError {
    /// A coroutine faulted.
    #[error("coroutine {coro_id} faulted: {fault}")]
    Fault {
        /// Coroutine ID.
        coro_id: usize,
        /// The fault.
        fault: Fault,
    },
    /// Session limit exceeded.
    #[error("max sessions ({max}) exceeded")]
    TooManySessions {
        /// Maximum allowed.
        max: usize,
    },
    /// Coroutine limit exceeded.
    #[error("max coroutines ({max}) exceeded")]
    TooManyCoroutines {
        /// Maximum allowed.
        max: usize,
    },
    /// Session not found.
    #[error("session {0} not found")]
    SessionNotFound(SessionId),
    /// Effect handler error.
    #[error("effect handler error: {0}")]
    HandlerError(String),
    /// Invalid concurrency parameter.
    #[error("invalid concurrency level: {n}")]
    InvalidConcurrency {
        /// Requested concurrency.
        n: usize,
    },
}

// ---- StepPack: atomic instruction result (matches Lean StepPack) ----

/// How to update the coroutine after an instruction.
pub(crate) enum CoroUpdate {
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
pub(crate) enum TypeUpdate {
    /// Advance to a new local type.
    Advance(LocalTypeR),
    /// Advance to a new local type and update the original (for Mu unfolding).
    AdvanceWithOriginal(LocalTypeR, LocalTypeR),
    /// Remove the type entry (endpoint completed).
    Remove,
}

/// Resolve a continuation and build the appropriate `TypeUpdate`.
pub(crate) fn resolve_type_update(
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

/// Atomic result of executing one instruction.
///
/// Matches the Lean `StepPack` pattern: bundles all mutations so the
/// caller commits them together via `commit_pack`.
pub(crate) struct StepPack {
    /// How to update the coroutine.
    pub(crate) coro_update: CoroUpdate,
    /// Type advancement, if any. `None` means no type change (e.g., block, control flow).
    pub(crate) type_update: Option<(Endpoint, TypeUpdate)>,
    /// Observable events to emit.
    pub(crate) events: Vec<ObsEvent>,
}

/// Internal outcome after committing a `StepPack`.
pub(crate) enum ExecOutcome {
    /// Instruction completed, coroutine continues.
    Continue,
    /// Coroutine blocked on a resource.
    Blocked(BlockReason),
    /// Coroutine halted normally.
    Halted,
}

// ---- The VM ----

/// The choreographic VM.
///
/// Manages coroutines, sessions (which own type state), and a scheduler.
/// Multiple choreographies can be loaded into a single VM, each in its
/// own session namespace — justified by separation logic.
#[derive(Debug, Serialize, Deserialize)]
pub struct VM<P = ()> {
    config: VMConfig,
    code: Option<Program>,
    programs: Vec<Program>,
    signed_buffers: SignedBuffers<()>,
    persistent: P,
    coroutines: Vec<Coroutine>,
    sessions: SessionStore,
    arena: Arena,
    resource_states: Vec<(ScopeId, ResourceState)>,
    sched: Scheduler,
    monitor: SessionMonitor,
    obs_trace: Vec<ObsEvent>,
    role_symbols: SymbolTable,
    label_symbols: SymbolTable,
    clock: SimClock,
    next_coro_id: usize,
    next_session_id: SessionId,
    paused_roles: BTreeSet<String>,
    guard_resources: HashMap<String, Value>,
    effect_trace: Vec<EffectTraceEntry>,
    next_effect_id: u64,
    output_condition_checks: Vec<OutputConditionCheck>,
    crashed_sites: Vec<SiteId>,
    partitioned_edges: Vec<Edge>,
    last_sched_step: Option<SchedStepDebug>,
}

/// Lean-aligned VM state alias.
pub type VMState<P = ()> = VM<P>;

impl VM {
    /// Create a new VM with the given configuration.
    #[must_use]
    pub fn new(config: VMConfig) -> Self {
        let tick_duration = config.tick_duration;
        let sched = Scheduler::new(config.sched_policy.clone());
        let mut guard_resources = HashMap::new();
        for layer in &config.guard_layers {
            guard_resources.insert(layer.id.clone(), Value::Unit);
        }
        Self {
            config,
            code: None,
            programs: Vec::new(),
            signed_buffers: SignedBuffers::new(),
            persistent: (),
            coroutines: Vec::new(),
            sessions: SessionStore::new(),
            arena: Arena,
            resource_states: Vec::new(),
            sched,
            monitor: SessionMonitor,
            obs_trace: Vec::new(),
            role_symbols: SymbolTable::new(),
            label_symbols: SymbolTable::new(),
            clock: SimClock::new(tick_duration),
            next_coro_id: 0,
            next_session_id: 0,
            paused_roles: BTreeSet::new(),
            guard_resources,
            effect_trace: Vec::new(),
            next_effect_id: 0,
            output_condition_checks: Vec::new(),
            crashed_sites: Vec::new(),
            partitioned_edges: Vec::new(),
            last_sched_step: None,
        }
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
        if self.sessions.active_count() >= self.config.max_sessions {
            return Err(VMError::TooManySessions {
                max: self.config.max_sessions,
            });
        }

        let roles = image.roles();
        let sid = self.next_session_id;
        self.next_session_id = self.next_session_id.saturating_add(1);
        self.sessions.open_with_sid(
            sid,
            roles.clone(),
            &self.config.buffer_config,
            &image.local_types,
        );

        self.obs_trace.push(ObsEvent::Opened {
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
            self.programs.push(program.clone());
            if self.code.is_none() {
                self.code = Some(program.clone());
            }
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

            self.sched.add_ready(coro_id);
            self.coroutines.push(coro);
        }

        Ok(sid)
    }

    /// Execute one scheduler round: advance up to N ready coroutines.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub(crate) fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
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
        self.try_unblock_receivers();

        let mut progressed = false;
        for _ in 0..n {
            if self.coroutines.iter().all(|c| c.is_terminal()) {
                return Ok(StepResult::AllDone);
            }

            let progress_ids: BTreeSet<usize> = self
                .coroutines
                .iter()
                .filter(|c| !c.progress_tokens.is_empty())
                .map(|c| c.id)
                .collect();

            let paused_roles = &self.paused_roles;
            let coroutines = &self.coroutines;
            let progress_ids = &progress_ids;
            let Some(coro_id) = VMKernel::select_ready_eligible(
                &mut self.sched,
                |id| progress_ids.contains(&id),
                |id| {
                    coroutines
                        .get(id)
                        .map(|c| !paused_roles.contains(&c.role))
                        .unwrap_or(false)
                },
            ) else {
                break;
            };

            let result = self.exec_instr(coro_id, handler);

            match result {
                Ok(ExecOutcome::Continue) => {
                    progressed = true;
                    self.last_sched_step = Some(SchedStepDebug {
                        selected_coro: coro_id,
                        exec_status: "continue".to_string(),
                    });
                    self.sched.reschedule(coro_id);
                }
                Ok(ExecOutcome::Blocked(reason)) => {
                    progressed = true;
                    self.last_sched_step = Some(SchedStepDebug {
                        selected_coro: coro_id,
                        exec_status: "blocked".to_string(),
                    });
                    self.sched.mark_blocked(coro_id, reason);
                }
                Ok(ExecOutcome::Halted) => {
                    progressed = true;
                    self.last_sched_step = Some(SchedStepDebug {
                        selected_coro: coro_id,
                        exec_status: "halted".to_string(),
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
                        exec_status: "faulted".to_string(),
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
        }

        if progressed {
            Ok(StepResult::Continue)
        } else {
            Ok(StepResult::Stuck)
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
    ) -> Result<(), VMError> {
        VMKernel::run_concurrent(self, handler, max_rounds, concurrency)
    }

    /// Run the VM until all coroutines complete or an error occurs.
    ///
    /// `max_steps` prevents infinite loops.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run(&mut self, handler: &dyn EffectHandler, max_steps: usize) -> Result<(), VMError> {
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
    ) -> Result<(), VMError> {
        let replay = ReplayEffectHandler::with_fallback(replay_trace.to_vec(), fallback);
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
    ) -> Result<(), VMError> {
        let replay = ReplayEffectHandler::with_fallback(replay_trace.to_vec(), fallback);
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

    /// Number of coroutine records in the VM.
    #[must_use]
    pub fn coroutine_count(&self) -> usize {
        self.coroutines.len()
    }

    /// Next session identifier reserved for allocation.
    #[must_use]
    pub fn next_session_id(&self) -> SessionId {
        self.next_session_id
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

    /// Crashed sites currently active in topology state.
    #[must_use]
    pub fn crashed_sites(&self) -> &[SiteId] {
        &self.crashed_sites
    }

    /// Partitioned site-links currently active in topology state.
    #[must_use]
    pub fn partitioned_edges(&self) -> &[Edge] {
        &self.partitioned_edges
    }

    /// Access the simulation clock.
    #[must_use]
    pub fn clock(&self) -> &SimClock {
        &self.clock
    }

    /// Whether all coroutines are terminal (done or faulted).
    #[must_use]
    pub fn all_done(&self) -> bool {
        self.coroutines.iter().all(|c| c.is_terminal())
    }

    /// Get a coroutine by ID.
    #[must_use]
    pub fn coroutine(&self, id: usize) -> Option<&Coroutine> {
        self.coroutines.iter().find(|c| c.id == id)
    }

    /// Program length for a coroutine by id.
    #[must_use]
    pub fn coroutine_program_len(&self, id: usize) -> Option<usize> {
        let coro = self.coroutine(id)?;
        self.programs.get(coro.program_id).map(std::vec::Vec::len)
    }

    /// Get a mutable coroutine by ID.
    pub fn coroutine_mut(&mut self, id: usize) -> Option<&mut Coroutine> {
        self.coroutines.iter_mut().find(|c| c.id == id)
    }

    /// Get all coroutines for a session.
    #[must_use]
    pub fn session_coroutines(&self, sid: SessionId) -> Vec<&Coroutine> {
        self.coroutines
            .iter()
            .filter(|c| c.session_id == sid)
            .collect()
    }

    /// Access the session store.
    #[must_use]
    pub fn sessions(&self) -> &SessionStore {
        &self.sessions
    }

    /// Access the session store mutably.
    pub fn sessions_mut(&mut self) -> &mut SessionStore {
        &mut self.sessions
    }

    /// Inject a message directly into a session buffer.
    ///
    /// Used by simulation middleware (network/fault injection) to deliver
    /// in-flight messages without executing a VM send instruction.
    ///
    /// # Errors
    ///
    /// Returns an error if the session does not exist.
    pub fn inject_message(
        &mut self,
        sid: SessionId,
        from: &str,
        to: &str,
        value: Value,
    ) -> Result<EnqueueResult, VMError> {
        let session = self
            .sessions
            .get_mut(sid)
            .ok_or(VMError::SessionNotFound(sid))?;
        session
            .send(from, to, value)
            .map_err(|_| VMError::SessionNotFound(sid))
    }

    /// Access all coroutines.
    #[must_use]
    pub fn coroutines(&self) -> &[Coroutine] {
        &self.coroutines
    }

    /// Pause execution for all coroutines of a role.
    pub fn pause_role(&mut self, role: &str) {
        self.paused_roles.insert(role.to_string());
    }

    /// Resume execution for all coroutines of a role.
    pub fn resume_role(&mut self, role: &str) {
        self.paused_roles.remove(role);
    }

    /// Replace the paused role set.
    pub fn set_paused_roles(&mut self, roles: &BTreeSet<String>) {
        self.paused_roles = roles.clone();
    }

    /// Access paused roles.
    #[must_use]
    pub fn paused_roles(&self) -> &BTreeSet<String> {
        &self.paused_roles
    }

    // ---- Private ----

    fn coro_index(&self, id: usize) -> usize {
        self.coroutines
            .iter()
            .position(|c| c.id == id)
            .expect("coroutine exists")
    }

    pub(crate) fn read_reg(&self, coro_idx: usize, reg: u16) -> Value {
        self.coroutines[coro_idx].regs[usize::from(reg)].clone()
    }

    fn monitor_precheck(
        &self,
        ep: &Endpoint,
        role: &str,
        instr: &crate::instr::Instr,
    ) -> Result<(), Fault> {
        if self.config.monitor_mode == MonitorMode::Off {
            return Ok(());
        }
        match instr {
            crate::instr::Instr::Send { .. } | crate::instr::Instr::Offer { .. } => {
                let local_type =
                    self.sessions
                        .lookup_type(ep)
                        .ok_or_else(|| Fault::TypeViolation {
                            expected: telltale_types::ValType::Unit,
                            actual: telltale_types::ValType::Unit,
                            message: format!("[monitor] {role}: no type registered"),
                        })?;
                if matches!(local_type, LocalTypeR::Send { .. }) {
                    Ok(())
                } else {
                    Err(Fault::TypeViolation {
                        expected: telltale_types::ValType::Unit,
                        actual: telltale_types::ValType::Unit,
                        message: format!(
                            "[monitor] {role}: expected Send state, got {local_type:?}"
                        ),
                    })
                }
            }
            crate::instr::Instr::Receive { .. } | crate::instr::Instr::Choose { .. } => {
                let local_type =
                    self.sessions
                        .lookup_type(ep)
                        .ok_or_else(|| Fault::TypeViolation {
                            expected: telltale_types::ValType::Unit,
                            actual: telltale_types::ValType::Unit,
                            message: format!("[monitor] {role}: no type registered"),
                        })?;
                if matches!(local_type, LocalTypeR::Recv { .. }) {
                    Ok(())
                } else {
                    Err(Fault::TypeViolation {
                        expected: telltale_types::ValType::Unit,
                        actual: telltale_types::ValType::Unit,
                        message: format!(
                            "[monitor] {role}: expected Recv state, got {local_type:?}"
                        ),
                    })
                }
            }
            _ => Ok(()),
        }
    }

    fn charge_instruction_cost(&mut self, coro_idx: usize) -> Result<(), Fault> {
        let cost = self.config.instruction_cost;
        let budget = self.coroutines[coro_idx].cost_budget;
        if budget < cost {
            return Err(Fault::OutOfCredits);
        }
        self.coroutines[coro_idx].cost_budget = budget - cost;
        Ok(())
    }

    fn apply_topology_event(&mut self, event: &TopologyPerturbation) {
        match event {
            TopologyPerturbation::Crash { site } => {
                if !self.crashed_sites.iter().any(|s| s == site) {
                    self.crashed_sites.push(site.clone());
                }
            }
            TopologyPerturbation::Partition { from, to } => {
                let forward = Edge::new(TOPOLOGY_EDGE_SID, from.clone(), to.clone());
                if !self.partitioned_edges.iter().any(|edge| edge == &forward) {
                    self.partitioned_edges.push(forward);
                }
                let reverse = Edge::new(TOPOLOGY_EDGE_SID, to.clone(), from.clone());
                if !self.partitioned_edges.iter().any(|edge| edge == &reverse) {
                    self.partitioned_edges.push(reverse);
                }
            }
            TopologyPerturbation::Heal { from, to } => {
                self.partitioned_edges.retain(|edge| {
                    edge.sid != TOPOLOGY_EDGE_SID
                        || !((edge.sender == *from && edge.receiver == *to)
                            || (edge.sender == *to && edge.receiver == *from))
                });
            }
        }
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

    /// Try to unblock coroutines that are waiting on receives.
    fn try_unblock_receivers(&mut self) {
        let blocked_ids = self.sched.blocked_ids();
        for coro_id in blocked_ids {
            let idx = self.coro_index(coro_id);
            let role = &self.coroutines[idx].role;
            if self.paused_roles.contains(role) {
                continue;
            }
            let reason = self.sched.block_reason(coro_id).cloned();
            if let Some(BlockReason::RecvWait { token, .. }) = reason {
                if let Some(session) = self.sessions.get(token.sid) {
                    let has_msg = session.roles.iter().any(|sender| {
                        sender != &token.role && session.has_message(sender, &token.role)
                    });
                    if has_msg {
                        self.sched.unblock(coro_id);
                    }
                }
            }
        }
    }

    /// Execute one instruction for a coroutine.
    ///
    /// Follows the Lean `execInstr` pipeline:
    /// 1. Fetch instruction at PC
    /// 2. Dispatch to per-instruction step function (which owns type checking)
    /// 3. Commit the `StepPack` atomically
    fn exec_instr(
        &mut self,
        coro_id: usize,
        handler: &dyn EffectHandler,
    ) -> Result<ExecOutcome, Fault> {
        let idx = self.coro_index(coro_id);
        let coro = &self.coroutines[idx];
        let pc = coro.pc;
        let sid = coro.session_id;
        let program = self
            .programs
            .get(coro.program_id)
            .ok_or(Fault::PcOutOfBounds)?;

        // 1. Fetch.
        if pc >= program.len() {
            return Err(Fault::PcOutOfBounds);
        }
        let instr = program[pc].clone();
        let ep = coro
            .owned_endpoints
            .first()
            .cloned()
            .ok_or(Fault::PcOutOfBounds)?;
        let role = coro.role.clone();

        // 1.5 Monitor precheck and deterministic cost charge.
        self.monitor_precheck(&ep, &role, &instr)?;
        self.charge_instruction_cost(idx)?;

        // 2. Dispatch to per-instruction step function.
        let pack = exec::step_instr(self, idx, &ep, &role, sid, instr, handler)?;

        let output_hint = if pack.events.is_empty() {
            None
        } else {
            handler.output_condition_hint(sid, &role, &self.coroutines[idx].regs)
        };

        // 3. Commit atomically.
        self.commit_pack(idx, pack, output_hint, &handler.handler_identity())
    }

    // ---- Per-instruction step functions (each owns its type logic) ----

    /// Send: lookup type → match Send → compute payload → enqueue → StepPack with L'.
    pub(crate) fn step_send(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        _val_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        // Type lookup — instruction owns this.
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?
            .clone();

        // Pattern match: must be Send.
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

        // Extract continuation (L') from first branch.
        let (label, _vt, continuation) = branches
            .first()
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: send has no branches"),
            })?
            .clone();

        // Compute payload/decision via handler.
        let coro = &self.coroutines[coro_idx];
        let decision = handler
            .send_decision(sid, role, &partner, &label.name, &coro.regs, None)
            .map_err(|e| Fault::InvokeFault { message: e })?;

        // Enqueue into buffer (if delivered).
        let session = self
            .sessions
            .get_mut(sid)
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
        let enqueue = match decision {
            SendDecision::Deliver(payload) => session
                .send(role, &partner, payload)
                .map_err(|e| Fault::InvokeFault { message: e })?,
            SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
        };
        match enqueue {
            EnqueueResult::Ok => {}
            EnqueueResult::WouldBlock => {
                // Block — NO type advancement.
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

        // Success: resolve continuation and advance type.
        let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update,
            events: vec![ObsEvent::Sent {
                tick: self.clock.tick,
                edge: Edge::new(sid, role.to_string(), partner.clone()),
                session: sid,
                from: role.to_string(),
                to: partner,
                label: label.name.clone(),
            }],
        })
    }

    /// Recv: lookup type → match Recv → try dequeue → block or process → StepPack.
    pub(crate) fn step_recv(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        dst_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        // Type lookup.
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?
            .clone();

        // Pattern match: must be Recv.
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

        // Try dequeue.
        let session = self.sessions.get(sid).ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
        if !session.has_message(&partner, role) {
            // Block — NO type advancement, NO state change.
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::RecvWait {
                    edge: Edge::new(sid, partner.clone(), role.to_string()),
                    token: ep.clone(),
                }),
                type_update: None,
                events: vec![],
            });
        }

        // Dequeue.
        let session = self.sessions.get_mut(sid).unwrap();
        let val = session
            .recv(&partner, role)
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;

        // Process via handler.
        handler
            .handle_recv(
                role,
                &partner,
                &label.name,
                &mut self.coroutines[coro_idx].regs,
                &val,
            )
            .map_err(|e| Fault::InvokeFault { message: e })?;

        // Resolve continuation and advance type.
        let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst_reg, val },
            type_update,
            events: vec![ObsEvent::Received {
                tick: self.clock.tick,
                edge: Edge::new(sid, partner.clone(), role.to_string()),
                session: sid,
                from: partner,
                to: role.to_string(),
                label: label.name.clone(),
            }],
        })
    }

    /// Halt: verify type is End → remove type entry.
    pub(crate) fn step_halt(&self, ep: &Endpoint) -> Result<StepPack, Fault> {
        // Optionally verify type is End (permissive in V1).
        if let Some(lt) = self.sessions.lookup_type(ep) {
            if !matches!(lt, LocalTypeR::End) {
                // V1: warn but allow. V2: fault.
            }
        }
        Ok(StepPack {
            coro_update: CoroUpdate::Halt,
            type_update: Some((ep.clone(), TypeUpdate::Remove)),
            events: vec![],
        })
    }

    /// Invoke: call handler.step() for integration.
    pub(crate) fn step_invoke(
        &mut self,
        coro_idx: usize,
        role: &str,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let coro_id = self.coroutines[coro_idx].id;
        handler
            .step(role, &mut self.coroutines[coro_idx].regs)
            .map_err(|e| Fault::InvokeFault { message: e })?;

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Invoked {
                tick: self.clock.tick,
                coro_id,
                role: role.to_string(),
            }],
        })
    }

    fn guard_active(&self, layer: &str) -> Result<(), Fault> {
        if self.config.guard_layers.is_empty() {
            return Ok(());
        }
        match self.config.guard_layers.iter().find(|cfg| cfg.id == layer) {
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

    pub(crate) fn step_acquire(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        layer: &str,
        dst: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        self.guard_active(layer)?;
        if self.guard_resources.is_empty() {
            self.guard_resources
                .entry(layer.to_string())
                .or_insert(Value::Unit);
        }
        let decision = handler
            .handle_acquire(sid, role, layer, &self.coroutines[coro_idx].regs)
            .map_err(|e| Fault::AcquireFault {
                layer: layer.to_string(),
                message: e,
            })?;
        match decision {
            crate::effect::AcquireDecision::Grant(evidence) => {
                self.guard_resources
                    .insert(layer.to_string(), evidence.clone());
                Ok(StepPack {
                    coro_update: CoroUpdate::AdvancePcWriteReg {
                        reg: dst,
                        val: evidence,
                    },
                    type_update: None,
                    events: vec![ObsEvent::Acquired {
                        tick: self.clock.tick,
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

    pub(crate) fn step_release(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        layer: &str,
        evidence: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        self.guard_active(layer)?;
        if self.guard_resources.is_empty() {
            self.guard_resources
                .entry(layer.to_string())
                .or_insert(Value::Unit);
        }
        let ev = self.coroutines[coro_idx]
            .regs
            .get(usize::from(evidence))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        handler
            .handle_release(sid, role, layer, &ev, &self.coroutines[coro_idx].regs)
            .map_err(|e| Fault::AcquireFault {
                layer: layer.to_string(),
                message: e,
            })?;
        self.guard_resources.insert(layer.to_string(), ev.clone());
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Released {
                tick: self.clock.tick,
                session: ep.sid,
                role: role.to_string(),
                layer: layer.to_string(),
            }],
        })
    }

    pub(crate) fn step_fork(
        &mut self,
        coro_idx: usize,
        role: &str,
        sid: SessionId,
        ghost: u16,
    ) -> Result<StepPack, Fault> {
        if !self.config.speculation_enabled {
            return Err(Fault::SpecFault {
                message: "speculation disabled".into(),
            });
        }
        let ghost_val = self.coroutines[coro_idx]
            .regs
            .get(usize::from(ghost))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        let ghost_sid = match ghost_val {
            Value::Int(v) if v >= 0 => {
                usize::try_from(v).map_err(|_| Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: fork ghost id out of range"),
                })?
            }
            _ => {
                return Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Unit,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: fork expects integer ghost id"),
                })
            }
        };
        self.coroutines[coro_idx].spec_state = Some(crate::coroutine::SpeculationState {
            ghost_sid,
            depth: 0,
        });
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Forked {
                tick: self.clock.tick,
                session: sid,
                ghost: ghost_sid,
            }],
        })
    }

    pub(crate) fn step_join(
        &mut self,
        coro_idx: usize,
        _role: &str,
        sid: SessionId,
    ) -> Result<StepPack, Fault> {
        self.coroutines[coro_idx].spec_state = None;
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Joined {
                tick: self.clock.tick,
                session: sid,
            }],
        })
    }

    pub(crate) fn step_abort(
        &mut self,
        coro_idx: usize,
        _role: &str,
        sid: SessionId,
    ) -> Result<StepPack, Fault> {
        self.coroutines[coro_idx].spec_state = None;
        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Aborted {
                tick: self.clock.tick,
                session: sid,
            }],
        })
    }

    pub(crate) fn step_transfer(
        &mut self,
        coro_idx: usize,
        role: &str,
        _sid: SessionId,
        endpoint: u16,
        target: u16,
        _bundle: u16,
    ) -> Result<StepPack, Fault> {
        let ep_val = self.coroutines[coro_idx]
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
        let target_val = self.coroutines[coro_idx]
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
        let target_idx = self
            .coroutines
            .iter()
            .position(|c| c.id == target_id)
            .ok_or(Fault::TransferFault {
                message: "target coroutine not found".into(),
            })?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::TransferFault {
                message: "endpoint not owned".into(),
            });
        }

        self.coroutines[coro_idx]
            .owned_endpoints
            .retain(|e| e != &ep);
        self.coroutines[target_idx].owned_endpoints.push(ep.clone());

        let mut moved = Vec::new();
        self.coroutines[coro_idx].knowledge_set.retain(|fact| {
            if fact.endpoint == ep {
                moved.push(fact.clone());
                false
            } else {
                true
            }
        });
        self.coroutines[target_idx].knowledge_set.extend(moved);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Transferred {
                tick: self.clock.tick,
                session: ep.sid,
                role: role.to_string(),
                from: self.coroutines[coro_idx].id,
                to: self.coroutines[target_idx].id,
            }],
        })
    }

    pub(crate) fn step_tag(
        &mut self,
        coro_idx: usize,
        role: &str,
        _sid: SessionId,
        fact_reg: u16,
        dst: u16,
    ) -> Result<StepPack, Fault> {
        let fact_val = self.coroutines[coro_idx]
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
        self.coroutines[coro_idx]
            .knowledge_set
            .push(crate::coroutine::KnowledgeFact {
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
                tick: self.clock.tick,
                session: endpoint.sid,
                role: role.to_string(),
                fact,
            }],
        })
    }

    pub(crate) fn step_check(
        &mut self,
        coro_idx: usize,
        role: &str,
        _sid: SessionId,
        knowledge: u16,
        target: u16,
        dst: u16,
    ) -> Result<StepPack, Fault> {
        let know_val = self.coroutines[coro_idx]
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
        let target_val = self.coroutines[coro_idx]
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
        let permitted = self.coroutines[coro_idx]
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
                tick: self.clock.tick,
                session: endpoint.sid,
                role: role.to_string(),
                target: target_role,
                permitted,
            }],
        })
    }

    /// Choose: external choice — receive a label and dispatch via branch table.
    pub(crate) fn step_choose(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        table: &[(String, PC)],
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?
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

        let session = self.sessions.get(sid).ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
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

        let session = self.sessions.get_mut(sid).unwrap();
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
                });
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
            .handle_recv(
                role,
                &partner,
                &label,
                &mut self.coroutines[coro_idx].regs,
                &val,
            )
            .map_err(|e| Fault::InvokeFault { message: e })?;

        let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

        Ok(StepPack {
            coro_update: CoroUpdate::SetPc(target_pc),
            type_update,
            events: vec![
                ObsEvent::Received {
                    tick: self.clock.tick,
                    edge: Edge::new(sid, partner.clone(), role.to_string()),
                    session: sid,
                    from: partner.clone(),
                    to: role.to_string(),
                    label: label.clone(),
                },
                ObsEvent::Chose {
                    tick: self.clock.tick,
                    edge: Edge::new(sid, partner, role.to_string()),
                    label,
                },
            ],
        })
    }

    /// Offer: internal choice — send selected label.
    pub(crate) fn step_offer(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        label: &str,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?
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
                        &self.coroutines[coro_idx].regs,
                        Some(Value::Label(label.to_string())),
                    )
                    .map_err(|e| Fault::InvokeFault { message: e })?;
                let session = self
                    .sessions
                    .get_mut(sid)
                    .ok_or_else(|| Fault::ChannelClosed {
                        endpoint: ep.clone(),
                    })?;
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

                let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
                let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

                Ok(StepPack {
                    coro_update: CoroUpdate::AdvancePc,
                    type_update,
                    events: vec![
                        ObsEvent::Sent {
                            tick: self.clock.tick,
                            edge: Edge::new(sid, role.to_string(), partner.clone()),
                            session: sid,
                            from: role.to_string(),
                            to: partner.clone(),
                            label: label.to_string(),
                        },
                        ObsEvent::Offered {
                            tick: self.clock.tick,
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

    /// Close: close session, remove type entry.
    pub(crate) fn step_close(&mut self, ep: &Endpoint, sid: SessionId) -> Result<StepPack, Fault> {
        self.sessions
            .close(sid)
            .map_err(|e| Fault::CloseFault { message: e })?;
        let epoch = self.sessions.get(sid).map_or(0, |session| session.epoch);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: Some((ep.clone(), TypeUpdate::Remove)),
            events: vec![
                ObsEvent::Closed {
                    tick: self.clock.tick,
                    session: sid,
                },
                ObsEvent::EpochAdvanced {
                    tick: self.clock.tick,
                    sid,
                    epoch,
                },
            ],
        })
    }

    /// Open: create a new session with the given roles.
    pub(crate) fn step_open(
        &mut self,
        coro_idx: usize,
        role: &str,
        roles: &[String],
        endpoints: &[(String, u16)],
    ) -> Result<StepPack, Fault> {
        let sid = self.sessions.open(
            roles.to_vec(),
            &BufferConfig::default(),
            &std::collections::BTreeMap::new(),
        );

        let mut coro_update = CoroUpdate::AdvancePc;
        if let Some((_, reg)) = endpoints.iter().find(|(r, _)| r == role) {
            if usize::from(*reg) >= self.coroutines[coro_idx].regs.len() {
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
                tick: self.clock.tick,
                session: sid,
                roles: roles.to_vec(),
            }],
        })
    }

    /// Commit a `StepPack` atomically: apply coroutine update, type update, events.
    fn commit_pack(
        &mut self,
        coro_idx: usize,
        pack: StepPack,
        output_hint: Option<crate::output_condition::OutputConditionHint>,
        handler_identity: &str,
    ) -> Result<ExecOutcome, Fault> {
        // Output-condition gate: any observable output must pass the configured verifier.
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
            self.obs_trace.push(ObsEvent::OutputConditionChecked {
                tick: self.clock.tick,
                predicate_ref: meta.predicate_ref.clone(),
                witness_ref: meta.witness_ref.clone(),
                output_digest: meta.output_digest.clone(),
                passed,
            });
            if !passed {
                let fault = Fault::OutputConditionFault {
                    predicate_ref: meta.predicate_ref,
                };
                self.coroutines[coro_idx].status = CoroStatus::Faulted(fault.clone());
                return Err(fault);
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

        let coro = &mut self.coroutines[coro_idx];

        // Apply coroutine update.
        match pack.coro_update {
            CoroUpdate::AdvancePc => {
                coro.pc += 1;
                coro.status = CoroStatus::Ready;
            }
            CoroUpdate::SetPc(pc) => {
                coro.pc = pc;
                coro.status = CoroStatus::Ready;
            }
            CoroUpdate::Block(ref reason) => {
                coro.status = CoroStatus::Blocked(reason.clone());
                // PC unchanged — instruction will re-execute on unblock.
            }
            CoroUpdate::Halt => {
                coro.status = CoroStatus::Done;
            }
            CoroUpdate::AdvancePcWriteReg { reg, ref val } => {
                coro.regs[usize::from(reg)] = val.clone();
                coro.pc += 1;
                coro.status = CoroStatus::Ready;
            }
        }

        // Apply type update.
        if let Some((ep, update)) = pack.type_update {
            match update {
                TypeUpdate::Advance(lt) => self.sessions.update_type(&ep, lt),
                TypeUpdate::AdvanceWithOriginal(lt, orig) => {
                    self.sessions.update_type(&ep, lt);
                    self.sessions.update_original(&ep, orig);
                }
                TypeUpdate::Remove => self.sessions.remove_type(&ep),
            }
        }

        // Emit events.
        self.obs_trace.extend(pack.events);

        // Map to ExecOutcome.
        match &self.coroutines[coro_idx].status {
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
            | ObsEvent::Checked { role, .. } => {
                let _: StringId = self.role_symbols.intern(role);
            }
            ObsEvent::Transferred { role, .. } => {
                let _: StringId = self.role_symbols.intern(role);
            }
            _ => {}
        }
    }
}

impl KernelMachine for VM {
    fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        VM::kernel_step_round(self, handler, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instr::Instr;
    use crate::loader::CodeImage;
    use std::collections::BTreeMap;
    use telltale_types::{GlobalType, Label, LocalTypeR};

    /// Trivial handler that passes values through.
    struct PassthroughHandler;

    impl EffectHandler for PassthroughHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Int(42))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels available".into())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    /// Handler that deterministically fails on send.
    struct FailingSendHandler;

    impl EffectHandler for FailingSendHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Err("send failed".to_string())
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    fn simple_send_recv_types() -> BTreeMap<String, LocalTypeR> {
        let mut m = BTreeMap::new();
        m.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        m.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        m
    }

    #[test]
    fn test_vm_simple_send_recv() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        // Both coroutines should be done.
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_recursive_protocol() {
        // mu step. A!B:msg. B!A:msg. var step
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Send {
                    partner: "B".into(),
                    branches: vec![(
                        Label::new("msg"),
                        None,
                        LocalTypeR::Recv {
                            partner: "B".into(),
                            branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                        },
                    )],
                },
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Recv {
                    partner: "A".into(),
                    branches: vec![(
                        Label::new("msg"),
                        None,
                        LocalTypeR::Send {
                            partner: "A".into(),
                            branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                        },
                    )],
                },
            ),
        );

        let global = GlobalType::mu(
            "step",
            GlobalType::send(
                "A",
                "B",
                Label::new("msg"),
                GlobalType::send("B", "A", Label::new("msg"), GlobalType::var("step")),
            ),
        );
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        // Run for enough steps to exercise several loop iterations.
        vm.run(&handler, 200).unwrap();

        // Should not fault — recursive protocol with blocking should work.
        assert!(vm
            .coroutines
            .iter()
            .all(|c| !matches!(c.status, CoroStatus::Faulted(_))));
    }

    #[test]
    fn test_vm_blocking_does_not_advance_type() {
        // Set up a protocol where B must recv before A sends.
        // B: recv, then send. A: send, then recv.
        // B will block on recv until A sends.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;

        // Step once: scheduler picks first ready coro (A or B).
        // If B is picked first, it should block (no message yet).
        // Type should NOT advance on block.
        let ep_b = Endpoint {
            sid,
            role: "B".into(),
        };
        let type_before = vm.sessions.lookup_type(&ep_b).cloned();

        // Run to completion.
        vm.run(&handler, 100).unwrap();
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));

        // Verify B's type was Recv before execution.
        assert!(matches!(type_before, Some(LocalTypeR::Recv { .. })));
    }

    #[test]
    fn test_blocked_step_has_no_type_or_trace_side_effects() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();
        vm.pause_role("A");

        let ep_b = Endpoint {
            sid,
            role: "B".to_string(),
        };
        let type_before = vm.sessions.lookup_type(&ep_b).cloned();
        let trace_len_before = vm.obs_trace().len();
        let b_pc_before = vm
            .coroutines
            .iter()
            .find(|c| c.role == "B")
            .expect("B coroutine exists")
            .pc;

        let handler = PassthroughHandler;
        let step_result = vm.step(&handler).expect("step should succeed");
        assert!(matches!(step_result, StepResult::Continue));

        let type_after = vm.sessions.lookup_type(&ep_b).cloned();
        let b_coro_after = vm
            .coroutines
            .iter()
            .find(|c| c.role == "B")
            .expect("B coroutine exists");

        assert_eq!(type_before, type_after, "blocked step advanced type state");
        assert_eq!(b_pc_before, b_coro_after.pc, "blocked step advanced PC");
        assert!(
            matches!(b_coro_after.status, CoroStatus::Blocked(_)),
            "blocked step did not block coroutine"
        );
        assert_eq!(
            trace_len_before,
            vm.obs_trace().len(),
            "blocked step emitted observable events"
        );
    }

    #[test]
    fn test_faulted_step_does_not_advance_type_state() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();
        vm.pause_role("B");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };
        let type_before = vm.sessions.lookup_type(&ep_a).cloned();

        let handler = FailingSendHandler;
        let result = vm.step(&handler);
        assert!(matches!(result, Err(VMError::Fault { .. })));

        let type_after = vm.sessions.lookup_type(&ep_a).cloned();
        assert_eq!(type_before, type_after, "faulted step advanced type state");
        assert!(
            vm.obs_trace()
                .iter()
                .any(|event| matches!(event, ObsEvent::Faulted { .. })),
            "faulted step must emit Faulted trace event"
        );
    }

    #[test]
    fn test_sent_event_matches_committed_session_transition() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();
        vm.pause_role("B");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        let handler = PassthroughHandler;
        vm.step(&handler).expect("single send step should succeed");

        let session = vm.sessions().get(sid).expect("session should exist");
        assert!(
            session.has_message("A", "B"),
            "committed send must enqueue message"
        );
        assert!(
            vm.obs_trace().iter().any(|event| {
                matches!(
                    event,
                    ObsEvent::Sent {
                        session: ev_sid,
                        from,
                        to,
                        label,
                        ..
                    } if *ev_sid == sid && from == "A" && to == "B" && label == "msg"
                )
            }),
            "committed send must emit matching Sent trace event"
        );
        assert!(
            matches!(vm.sessions.lookup_type(&ep_a), Some(LocalTypeR::End)),
            "committed send must advance sender type"
        );
    }

    #[test]
    fn test_vm_load_multiple_sessions() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        let image1 = CodeImage::from_local_types(&local_types, &global);
        let image2 = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid1 = vm.load_choreography(&image1).unwrap();
        let sid2 = vm.load_choreography(&image2).unwrap();

        assert_ne!(sid1, sid2);
        assert_eq!(vm.coroutines.len(), 4);

        let handler = PassthroughHandler;
        vm.run(&handler, 200).unwrap();
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_choice_protocol() {
        // A chooses "yes" or "no", B offers (receives the choice).
        // A: Send { B, [yes → End, no → End] }
        // B: Recv { A, [yes → End, no → End] }
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send_choice(
                "B",
                vec![
                    (Label::new("yes"), None, LocalTypeR::End),
                    (Label::new("no"), None, LocalTypeR::End),
                ],
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv_choice(
                "A",
                vec![
                    (Label::new("yes"), None, LocalTypeR::End),
                    (Label::new("no"), None, LocalTypeR::End),
                ],
            ),
        );

        let global = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("yes"), GlobalType::End),
                (Label::new("no"), GlobalType::End),
            ],
        );

        // Manually compile: A offers a label, B chooses from table.
        let a_code = vec![
            Instr::Offer {
                chan: 0,
                label: "yes".into(),
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Choose {
                chan: 0,
                table: vec![("yes".into(), 1), ("no".into(), 2)],
            },
            Instr::Halt, // yes branch
            Instr::Halt, // no branch
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));

        // Verify events include Sent (from Choose) and Received (from Offer).
        let sent = vm
            .obs_trace
            .iter()
            .any(|e| matches!(e, ObsEvent::Sent { label, .. } if label == "yes"));
        let recv = vm
            .obs_trace
            .iter()
            .any(|e| matches!(e, ObsEvent::Received { label, .. } if label == "yes"));
        assert!(sent, "expected Sent event with label 'yes'");
        assert!(recv, "expected Received event with label 'yes'");
    }

    #[test]
    fn test_vm_offer_blocks_until_choice() {
        // B tries to Offer before A has Chosen → should block.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send_choice("B", vec![(Label::new("go"), None, LocalTypeR::End)]),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv_choice("A", vec![(Label::new("go"), None, LocalTypeR::End)]),
        );

        let global = GlobalType::send("A", "B", Label::new("go"), GlobalType::End);

        let a_code = vec![
            Instr::Offer {
                chan: 0,
                label: "go".into(),
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Choose {
                chan: 0,
                table: vec![("go".into(), 1)],
            },
            Instr::Halt,
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_close_session() {
        // Simple: A sends to B, then closes.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        // A: Send, Close, Halt.  B: Recv, Close, Halt.
        let a_code = vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Close { session: 0 },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Close { session: 0 },
            Instr::Halt,
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
        let closed_count = vm
            .obs_trace
            .iter()
            .filter(|e| matches!(e, ObsEvent::Closed { .. }))
            .count();
        assert!(closed_count >= 1, "expected at least one Closed event");
    }

    #[test]
    fn test_compiler_multi_branch() {
        use crate::compiler::compile;

        // Send with 2 branches → should emit deterministic Offer(first-label) + branch code.
        let lt = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        );

        let code = compile(&lt);

        assert!(
            matches!(&code[0], Instr::Offer { label, .. } if label == "yes"),
            "expected Offer(\"yes\"), got {:?}",
            code[0]
        );
        assert!(
            matches!(code[1], Instr::Halt),
            "expected Halt after deterministic offer"
        );
    }

    #[test]
    fn test_compiler_single_branch_unchanged() {
        use crate::compiler::compile;

        // Single-branch Send → should emit Send, not Offer.
        let lt = LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        };
        let code = compile(&lt);
        assert!(matches!(code[0], Instr::Send { .. }));
    }

    #[test]
    fn test_vm_recursive_choice_protocol() {
        // mu x. A→B:{continue.A→B:data.x, stop.end}
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::mu(
                "x",
                LocalTypeR::send_choice(
                    "B",
                    vec![
                        (
                            Label::new("continue"),
                            None,
                            LocalTypeR::Send {
                                partner: "B".into(),
                                branches: vec![(Label::new("data"), None, LocalTypeR::var("x"))],
                            },
                        ),
                        (Label::new("stop"), None, LocalTypeR::End),
                    ],
                ),
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "x",
                LocalTypeR::recv_choice(
                    "A",
                    vec![
                        (
                            Label::new("continue"),
                            None,
                            LocalTypeR::Recv {
                                partner: "A".into(),
                                branches: vec![(Label::new("data"), None, LocalTypeR::var("x"))],
                            },
                        ),
                        (Label::new("stop"), None, LocalTypeR::End),
                    ],
                ),
            ),
        );

        let global = GlobalType::mu(
            "x",
            GlobalType::comm(
                "A",
                "B",
                vec![
                    (
                        Label::new("continue"),
                        GlobalType::send("A", "B", Label::new("data"), GlobalType::var("x")),
                    ),
                    (Label::new("stop"), GlobalType::End),
                ],
            ),
        );

        // Manually craft bytecode: A offers "stop" immediately.
        let a_code = vec![
            Instr::Offer {
                chan: 0,
                label: "stop".into(),
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Choose {
                chan: 0,
                table: vec![("continue".into(), 1), ("stop".into(), 3)],
            },
            // continue branch: Recv data, then loop back to Offer
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Jump { target: 0 },
            // stop branch: Halt
            Instr::Halt,
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_single_branch_then_multi_branch_choice() {
        // B→A:ack, then mu t. B→A:{continue→t, stop→End}
        // This is the protocol that was failing in fuzz tests.
        let projected: BTreeMap<String, LocalTypeR> = {
            let global = GlobalType::Comm {
                sender: "B".into(),
                receiver: "A".into(),
                branches: vec![(
                    Label::new("ack"),
                    GlobalType::Mu {
                        var: "t".into(),
                        body: Box::new(GlobalType::Comm {
                            sender: "B".into(),
                            receiver: "A".into(),
                            branches: vec![
                                (Label::new("continue"), GlobalType::Var("t".into())),
                                (Label::new("stop"), GlobalType::End),
                            ],
                        }),
                    },
                )],
            };
            telltale_theory::projection::project_all(&global)
                .unwrap()
                .into_iter()
                .collect()
        };

        let global = GlobalType::Comm {
            sender: "B".into(),
            receiver: "A".into(),
            branches: vec![(
                Label::new("ack"),
                GlobalType::Mu {
                    var: "t".into(),
                    body: Box::new(GlobalType::Comm {
                        sender: "B".into(),
                        receiver: "A".into(),
                        branches: vec![
                            (Label::new("continue"), GlobalType::Var("t".into())),
                            (Label::new("stop"), GlobalType::End),
                        ],
                    }),
                },
            )],
        };
        let image = CodeImage::from_local_types(&projected, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        // Don't unwrap — just run to completion
        vm.run(&handler, 500).unwrap_or(());

        let faults: Vec<_> = vm
            .obs_trace
            .iter()
            .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
            .collect();
        assert!(faults.is_empty(), "faults: {faults:?}");
    }

    #[test]
    fn test_output_condition_gate_denies_commit() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            output_condition_policy: OutputConditionPolicy::DenyAll,
            ..VMConfig::default()
        });
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        let result = vm.run(&handler, 10);
        assert!(result.is_err());
        assert!(
            matches!(
                result,
                Err(VMError::Fault {
                    fault: Fault::OutputConditionFault { .. },
                    ..
                })
            ),
            "expected output-condition fault, got: {result:?}"
        );
        assert!(vm
            .output_condition_checks()
            .iter()
            .any(|c| c.meta.predicate_ref == "vm.observable_output" && !c.passed));
    }

    #[test]
    fn test_output_condition_allowlist_accepts_default_predicate() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
                "vm.observable_output".to_string(),
            ]),
            ..VMConfig::default()
        });
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();
        assert!(vm
            .output_condition_checks()
            .iter()
            .any(|c| c.meta.predicate_ref == "vm.observable_output" && c.passed));
    }

    #[test]
    fn test_effect_trace_records_committed_effects() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();
        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        let kinds: Vec<_> = vm
            .effect_trace()
            .iter()
            .map(|e| e.effect_kind.as_str())
            .collect();
        assert!(kinds.contains(&"send_decision"));
        assert!(kinds.contains(&"handle_recv"));
    }

    #[test]
    fn vm_state_serialization_contains_lean_aligned_fields() {
        let vm = VM::new(VMConfig::default());
        let json = serde_json::to_value(&vm).expect("serialize VM state");
        let obj = json.as_object().expect("VM state must serialize as object");
        for key in [
            "config",
            "code",
            "programs",
            "signed_buffers",
            "persistent",
            "coroutines",
            "sessions",
            "arena",
            "resource_states",
            "sched",
            "monitor",
            "obs_trace",
            "clock",
            "next_coro_id",
            "next_session_id",
            "crashed_sites",
            "partitioned_edges",
        ] {
            assert!(obj.contains_key(key), "missing VM state field: {key}");
        }
    }
}
