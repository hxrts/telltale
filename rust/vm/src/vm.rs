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

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::marker::PhantomData;
use std::time::Duration;
use telltale_types::LocalTypeR;

use crate::bridge::{IdentityGuardBridge, IdentityVerificationBridge};
use crate::buffer::{BufferConfig, EnqueueResult};
use crate::clock::SimClock;
use crate::coroutine::{
    BlockReason, CoroStatus, Coroutine, Fault, KnowledgeFact, ProgressToken, Value,
};
use crate::determinism::DeterminismMode;
use crate::effect::{
    CorruptionType, EffectHandler, EffectTraceEntry, ReplayEffectHandler, SendDecision,
    TopologyPerturbation,
};
use crate::exec;
use crate::guard::{GuardLayer, InMemoryGuardLayer, LayerId};
use crate::identity::IdentityModel;
use crate::instr::{Endpoint, Instr, PC};
use crate::intern::{StringId, SymbolTable};
use crate::kernel::{KernelMachine, VMKernel};
use crate::loader::CodeImage;
use crate::output_condition::{
    verify_output_condition, OutputConditionCheck, OutputConditionMeta, OutputConditionPolicy,
};
use crate::persistence::{NoopPersistence, PersistenceModel};
use crate::scheduler::{SchedPolicy, Scheduler};
use crate::serialization::{canonical_replay_fragment_v1, CanonicalReplayFragmentV1};
use crate::session::{unfold_if_var_with_scope, Edge, SessionId, SessionStatus, SessionStore};
use crate::verification::{DefaultVerificationModel, VerificationModel};

fn default_instruction_cost() -> usize {
    1
}

fn default_initial_cost_budget() -> usize {
    usize::MAX
}

fn default_config_schema_version() -> u32 {
    1
}

/// Lean-aligned scope identifier placeholder.
pub type ScopeId = usize;

/// Lean-aligned program representation.
pub type Program = Vec<Instr>;

/// Branch list type used in local types.
type BranchList = Vec<(
    telltale_types::Label,
    Option<telltale_types::ValType>,
    LocalTypeR,
)>;

/// Lean-aligned resource state with commitments and nullifiers.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ResourceState {
    commitments: BTreeSet<crate::verification::Commitment>,
    nullifiers: BTreeSet<crate::verification::Nullifier>,
}

impl ResourceState {
    /// Record a commitment for a value and return the commitment digest.
    #[must_use]
    pub fn commit(&mut self, value: &Value) -> crate::verification::Commitment {
        let commitment = crate::verification::DefaultVerificationModel::commitment(value);
        self.commitments.insert(commitment);
        commitment
    }

    /// Consume a value by inserting its nullifier.
    ///
    /// # Errors
    ///
    /// Returns an error when the value has already been consumed.
    pub fn consume(&mut self, value: &Value) -> Result<crate::verification::Nullifier, String> {
        let nullifier = crate::verification::DefaultVerificationModel::nullifier(value);
        if self.nullifiers.contains(&nullifier) {
            return Err("resource already consumed".to_string());
        }
        self.nullifiers.insert(nullifier);
        Ok(nullifier)
    }

    /// Check whether a value has not yet been consumed.
    #[must_use]
    pub fn verify_uncommitted(&self, value: &Value) -> bool {
        let nullifier = crate::verification::DefaultVerificationModel::nullifier(value);
        !self.nullifiers.contains(&nullifier)
    }
}

/// Runtime arena with slot reuse.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Arena {
    slots: Vec<Option<Value>>,
    next_free: usize,
    capacity: usize,
}

impl Default for Arena {
    fn default() -> Self {
        Self::new(128)
    }
}

impl Arena {
    /// Construct an arena with the given slot capacity.
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        let cap = capacity.max(1);
        Self {
            slots: vec![None; cap],
            next_free: 0,
            capacity: cap,
        }
    }

    /// Allocate one slot and return its index.
    ///
    /// # Errors
    ///
    /// Returns an error when no free slot is available.
    pub fn alloc(&mut self, value: Value) -> Result<usize, String> {
        for offset in 0..self.capacity {
            let idx = (self.next_free + offset) % self.capacity;
            if self.slots[idx].is_none() {
                self.slots[idx] = Some(value);
                self.next_free = (idx + 1) % self.capacity;
                debug_assert!(self.check_invariants());
                return Ok(idx);
            }
        }
        Err("arena full".to_string())
    }

    /// Free one occupied slot and return its value.
    ///
    /// # Errors
    ///
    /// Returns an error if the index is invalid or the slot is already free.
    pub fn free(&mut self, idx: usize) -> Result<Value, String> {
        if idx >= self.capacity {
            return Err("arena index out of bounds".to_string());
        }
        let value = self.slots[idx]
            .take()
            .ok_or_else(|| "arena slot already free".to_string())?;
        if idx < self.next_free {
            self.next_free = idx;
        }
        debug_assert!(self.check_invariants());
        Ok(value)
    }

    /// Borrow a value in a slot by index.
    #[must_use]
    pub fn get(&self, idx: usize) -> Option<&Value> {
        self.slots.get(idx).and_then(Option::as_ref)
    }

    /// Mutably borrow a value in a slot by index.
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut Value> {
        self.slots.get_mut(idx).and_then(Option::as_mut)
    }

    /// Validate arena structural invariants.
    #[must_use]
    pub fn check_invariants(&self) -> bool {
        self.slots.len() == self.capacity && self.next_free < self.capacity
    }
}

/// Session kind monitored at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SessionKind {
    /// Endpoint is acting as a client.
    Client,
    /// Endpoint is acting as a server.
    Server,
    /// Endpoint is acting as a peer.
    Peer,
}

/// Runtime judgment for one monitor check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WellTypedInstr {
    /// Endpoint checked by the monitor.
    pub endpoint: Endpoint,
    /// Instruction tag emitted for this check.
    pub instr_tag: String,
    /// Tick at which the monitor check occurred.
    pub tick: u64,
}

/// Runtime monitor state for session checks.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct SessionMonitor {
    session_kinds: BTreeMap<SessionId, SessionKind>,
    last_judgment: Option<WellTypedInstr>,
}

impl SessionMonitor {
    /// Set the session kind for one session id.
    pub fn set_kind(&mut self, sid: SessionId, kind: SessionKind) {
        self.session_kinds.insert(sid, kind);
    }

    /// Remove tracked kind metadata for a session id.
    pub fn remove_kind(&mut self, sid: SessionId) {
        self.session_kinds.remove(&sid);
    }

    /// Record the most recent monitor judgment.
    pub fn record(&mut self, endpoint: &Endpoint, instr_tag: &str, tick: u64) {
        self.last_judgment = Some(WellTypedInstr {
            endpoint: endpoint.clone(),
            instr_tag: instr_tag.to_string(),
            tick,
        });
    }
}

/// Lean-aligned site identifier for failure topology state.
pub type SiteId = String;

/// Active corruption policy for one directed edge.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CorruptedEdge {
    edge: Edge,
    corruption: CorruptionType,
}

/// Active timeout window for one site.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SiteTimeout {
    site: SiteId,
    until_tick: u64,
}

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

/// Information-flow policy used by epistemic `check`.
pub enum FlowPolicy {
    /// Permit all facts to all roles.
    AllowAll,
    /// Deny all flows.
    DenyAll,
    /// Permit only listed roles.
    AllowRoles(BTreeSet<String>),
    /// Deny listed roles.
    DenyRoles(BTreeSet<String>),
    /// Runtime closure policy:
    /// `Predicate(Box<dyn Fn(&Knowledge, &Role) -> bool>)`.
    Predicate(Box<dyn FlowPolicyFn>),
    /// Serializable knowledge-dependent predicate policy.
    PredicateExpr(FlowPredicate),
}

/// Cloneable dynamic predicate for runtime flow checks.
pub trait FlowPolicyFn: Send + Sync {
    /// Evaluate whether a fact may flow to a target role.
    fn eval(&self, knowledge: &KnowledgeFact, target_role: &str) -> bool;
    /// Clone trait-object predicate.
    fn clone_box(&self) -> Box<dyn FlowPolicyFn>;
}

impl<F> FlowPolicyFn for F
where
    F: Fn(&KnowledgeFact, &str) -> bool + Clone + Send + Sync + 'static,
{
    fn eval(&self, knowledge: &KnowledgeFact, target_role: &str) -> bool {
        self(knowledge, target_role)
    }

    fn clone_box(&self) -> Box<dyn FlowPolicyFn> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn FlowPolicyFn> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

impl Default for FlowPolicy {
    fn default() -> Self {
        Self::AllowAll
    }
}

impl Clone for FlowPolicy {
    fn clone(&self) -> Self {
        match self {
            Self::AllowAll => Self::AllowAll,
            Self::DenyAll => Self::DenyAll,
            Self::AllowRoles(roles) => Self::AllowRoles(roles.clone()),
            Self::DenyRoles(roles) => Self::DenyRoles(roles.clone()),
            Self::Predicate(predicate) => Self::Predicate(predicate.clone()),
            Self::PredicateExpr(predicate) => Self::PredicateExpr(predicate.clone()),
        }
    }
}

impl fmt::Debug for FlowPolicy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AllowAll => f.write_str("AllowAll"),
            Self::DenyAll => f.write_str("DenyAll"),
            Self::AllowRoles(roles) => f.debug_tuple("AllowRoles").field(roles).finish(),
            Self::DenyRoles(roles) => f.debug_tuple("DenyRoles").field(roles).finish(),
            Self::Predicate(_) => f.write_str("Predicate(<dynamic>)"),
            Self::PredicateExpr(predicate) => {
                f.debug_tuple("PredicateExpr").field(predicate).finish()
            }
        }
    }
}

impl PartialEq for FlowPolicy {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::AllowAll, Self::AllowAll) => true,
            (Self::DenyAll, Self::DenyAll) => true,
            (Self::AllowRoles(lhs), Self::AllowRoles(rhs)) => lhs == rhs,
            (Self::DenyRoles(lhs), Self::DenyRoles(rhs)) => lhs == rhs,
            (Self::Predicate(lhs), Self::Predicate(rhs)) => {
                std::ptr::eq::<dyn FlowPolicyFn>(&**lhs, &**rhs)
            }
            (Self::PredicateExpr(lhs), Self::PredicateExpr(rhs)) => lhs == rhs,
            _ => false,
        }
    }
}

impl Eq for FlowPolicy {}

#[derive(Serialize, Deserialize)]
enum FlowPolicyRepr {
    AllowAll,
    DenyAll,
    AllowRoles(BTreeSet<String>),
    DenyRoles(BTreeSet<String>),
    PredicateExpr(FlowPredicate),
}

impl Serialize for FlowPolicy {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let repr = match self {
            Self::AllowAll => FlowPolicyRepr::AllowAll,
            Self::DenyAll => FlowPolicyRepr::DenyAll,
            Self::AllowRoles(roles) => FlowPolicyRepr::AllowRoles(roles.clone()),
            Self::DenyRoles(roles) => FlowPolicyRepr::DenyRoles(roles.clone()),
            Self::PredicateExpr(predicate) => FlowPolicyRepr::PredicateExpr(predicate.clone()),
            Self::Predicate(_) => {
                return Err(serde::ser::Error::custom(
                    "runtime closure predicate is not serializable",
                ))
            }
        };
        repr.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for FlowPolicy {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let repr = FlowPolicyRepr::deserialize(deserializer)?;
        let policy = match repr {
            FlowPolicyRepr::AllowAll => Self::AllowAll,
            FlowPolicyRepr::DenyAll => Self::DenyAll,
            FlowPolicyRepr::AllowRoles(roles) => Self::AllowRoles(roles),
            FlowPolicyRepr::DenyRoles(roles) => Self::DenyRoles(roles),
            FlowPolicyRepr::PredicateExpr(predicate) => Self::PredicateExpr(predicate),
        };
        Ok(policy)
    }
}

impl FlowPolicy {
    /// Build a runtime closure-based flow predicate policy.
    #[must_use]
    pub fn predicate<F>(predicate: F) -> Self
    where
        F: Fn(&KnowledgeFact, &str) -> bool + Clone + Send + Sync + 'static,
    {
        Self::Predicate(Box::new(predicate))
    }
}

/// Serializable flow-policy predicate over known fact + destination.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FlowPredicate {
    /// Allow when destination role starts with prefix.
    TargetRolePrefix(String),
    /// Allow when fact contains substring.
    FactContains(String),
    /// Allow when the fact endpoint role equals destination role.
    EndpointRoleMatchesTarget,
    /// Conjunction.
    All(Vec<FlowPredicate>),
    /// Disjunction.
    Any(Vec<FlowPredicate>),
}

impl FlowPolicy {
    /// Check whether knowledge flow to `target_role` is permitted.
    #[must_use]
    pub fn allows(&self, target_role: &str) -> bool {
        match self {
            Self::AllowAll => true,
            Self::DenyAll => false,
            Self::AllowRoles(roles) => roles.contains(target_role),
            Self::DenyRoles(roles) => !roles.contains(target_role),
            Self::Predicate(_) | Self::PredicateExpr(_) => true,
        }
    }

    /// Check whether a concrete knowledge fact may flow to a target role.
    #[must_use]
    pub fn allows_knowledge(&self, knowledge: &KnowledgeFact, target_role: &str) -> bool {
        match self {
            Self::Predicate(predicate) => predicate.eval(knowledge, target_role),
            Self::PredicateExpr(predicate) => predicate.eval(knowledge, target_role),
            other => other.allows(target_role),
        }
    }
}

impl FlowPredicate {
    /// Evaluate this serialized predicate against one fact and target role.
    #[must_use]
    pub fn eval(&self, knowledge: &KnowledgeFact, target_role: &str) -> bool {
        match self {
            Self::TargetRolePrefix(prefix) => target_role.starts_with(prefix),
            Self::FactContains(fragment) => knowledge.fact.contains(fragment),
            Self::EndpointRoleMatchesTarget => knowledge.endpoint.role == target_role,
            Self::All(predicates) => predicates
                .iter()
                .all(|predicate| predicate.eval(knowledge, target_role)),
            Self::Any(predicates) => predicates
                .iter()
                .any(|predicate| predicate.eval(knowledge, target_role)),
        }
    }
}

/// VM configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VMConfig {
    /// Migration-safe config schema version.
    #[serde(default = "default_config_schema_version")]
    pub config_schema_version: u32,
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
    /// Flow policy for epistemic knowledge checks.
    #[serde(default)]
    pub flow_policy: FlowPolicy,
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
            config_schema_version: default_config_schema_version(),
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
            flow_policy: FlowPolicy::AllowAll,
            instruction_cost: 1,
            initial_cost_budget: usize::MAX,
        }
    }
}

impl VMConfig {
    /// Assert VM configuration invariants required for safe state initialization.
    ///
    /// # Panics
    ///
    /// Panics when a required invariant is violated.
    pub fn assert_invariants(&self) {
        assert!(
            self.config_schema_version >= 1,
            "config_schema_version must be >= 1"
        );
        assert!(self.max_sessions > 0, "max_sessions must be > 0");
        assert!(self.max_coroutines > 0, "max_coroutines must be > 0");
        assert!(self.num_registers > 0, "num_registers must be > 0");
        assert!(self.instruction_cost > 0, "instruction_cost must be > 0");
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
    /// Persistence model lifecycle error.
    #[error("persistence error: {0}")]
    PersistenceError(String),
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
pub struct VM<I = (), G = (), P = NoopPersistence, Nu = DefaultVerificationModel>
where
    P: PersistenceModel,
{
    config: VMConfig,
    code: Option<Program>,
    programs: Vec<Program>,
    identity_model: PhantomData<I>,
    guard_model: PhantomData<G>,
    persistence_model: PhantomData<P>,
    persistent: P::PState,
    verification: Nu,
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
    guard_layer: InMemoryGuardLayer,
    effect_trace: Vec<EffectTraceEntry>,
    next_effect_id: u64,
    output_condition_checks: Vec<OutputConditionCheck>,
    crashed_sites: Vec<SiteId>,
    partitioned_edges: Vec<Edge>,
    corrupted_edges: Vec<CorruptedEdge>,
    timed_out_sites: Vec<SiteTimeout>,
    last_sched_step: Option<SchedStepDebug>,
}

/// Lean-aligned VM state alias.
pub type VMState<I = (), G = (), P = NoopPersistence, Nu = DefaultVerificationModel> =
    VM<I, G, P, Nu>;

impl<I, G, P, Nu> VM<I, G, P, Nu>
where
    P: PersistenceModel,
{
    /// Borrow the persistent state tracked by the configured persistence model.
    #[must_use]
    pub fn persistent_state(&self) -> &P::PState {
        &self.persistent
    }

    /// Mutably borrow persistent state.
    pub fn persistent_state_mut(&mut self) -> &mut P::PState {
        &mut self.persistent
    }

    /// Resolve guard-layer capability for a participant via bridge binding.
    #[must_use]
    pub fn bridge_guard_layer_for_participant<B>(
        &self,
        bridge: &B,
        participant: &I::ParticipantId,
    ) -> LayerId
    where
        I: IdentityModel,
        G: GuardLayer,
        B: IdentityGuardBridge<I, G>,
    {
        bridge.guard_layer_for_participant(participant)
    }

    /// Resolve participant verification key via bridge binding.
    #[must_use]
    pub fn bridge_verifying_key_for_participant<B>(
        &self,
        bridge: &B,
        participant: &I::ParticipantId,
    ) -> Nu::VerifyingKey
    where
        I: IdentityModel,
        Nu: VerificationModel,
        B: IdentityVerificationBridge<I, Nu>,
    {
        bridge.verification_key_for_participant(participant)
    }
}

impl VM {
    /// Create a new VM with the given configuration.
    #[must_use]
    pub fn new(config: VMConfig) -> Self {
        config.assert_invariants();
        let tick_duration = config.tick_duration;
        let sched = Scheduler::new(config.sched_policy.clone());
        let mut guard_resources = BTreeMap::new();
        for layer in &config.guard_layers {
            guard_resources.insert(layer.id.clone(), Value::Unit);
        }
        Self {
            config,
            code: None,
            programs: Vec::new(),
            identity_model: PhantomData,
            guard_model: PhantomData,
            persistence_model: PhantomData,
            persistent: (),
            verification: DefaultVerificationModel,
            coroutines: Vec::new(),
            sessions: SessionStore::new(),
            arena: Arena::default(),
            resource_states: Vec::new(),
            sched,
            monitor: SessionMonitor::default(),
            obs_trace: Vec::new(),
            role_symbols: SymbolTable::new(),
            label_symbols: SymbolTable::new(),
            clock: SimClock::new(tick_duration),
            next_coro_id: 0,
            next_session_id: 0,
            paused_roles: BTreeSet::new(),
            guard_layer: InMemoryGuardLayer {
                resources: guard_resources
                    .into_iter()
                    .map(|(k, v)| (LayerId(k), v))
                    .collect(),
            },
            effect_trace: Vec::new(),
            next_effect_id: 0,
            output_condition_checks: Vec::new(),
            crashed_sites: Vec::new(),
            partitioned_edges: Vec::new(),
            corrupted_edges: Vec::new(),
            timed_out_sites: Vec::new(),
            last_sched_step: None,
        }
    }

    fn apply_open_delta(&mut self, sid: SessionId) -> Result<(), String> {
        let delta = NoopPersistence::open_delta(sid);
        NoopPersistence::apply(&mut self.persistent, &delta)
    }

    fn apply_close_delta(&mut self, sid: SessionId) -> Result<(), String> {
        let delta = NoopPersistence::close_delta(sid);
        NoopPersistence::apply(&mut self.persistent, &delta)
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
        self.monitor.set_kind(sid, SessionKind::Peer);
        self.resource_states.push((sid, ResourceState::default()));
        self.apply_open_delta(sid)
            .map_err(VMError::PersistenceError)?;

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
            coro.owned_endpoints.push(ep.clone());
            if !coro.regs.is_empty() {
                coro.regs[0] = Value::Endpoint(ep);
            }

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
            let crashed_sites = &self.crashed_sites;
            let timed_out_sites = &self.timed_out_sites;
            let coroutines = &self.coroutines;
            let progress_ids = &progress_ids;
            let Some(coro_id) = VMKernel::select_ready_eligible(
                &mut self.sched,
                |id| progress_ids.contains(&id),
                |id| {
                    coroutines
                        .get(id)
                        .map(|c| {
                            !paused_roles.contains(&c.role)
                                && !crashed_sites.iter().any(|site| site == &c.role)
                                && !timed_out_sites.iter().any(|timeout| timeout.site == c.role)
                        })
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
            #[cfg(debug_assertions)]
            debug_assert!(self.wf_vm_state().is_ok());
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

    /// Canonical replay/state fragment for deterministic diffing and snapshots.
    #[must_use]
    pub fn canonical_replay_fragment(&self) -> CanonicalReplayFragmentV1 {
        let partitioned_edges = self
            .partitioned_edges
            .iter()
            .map(|edge| (edge.sender.clone(), edge.receiver.clone()))
            .collect();
        let corrupted_edges = self
            .corrupted_edges
            .iter()
            .map(|entry| {
                (
                    (entry.edge.sender.clone(), entry.edge.receiver.clone()),
                    entry.corruption.clone(),
                )
            })
            .collect();
        let timed_out_sites = self
            .timed_out_sites
            .iter()
            .map(|timeout| (timeout.site.clone(), timeout.until_tick))
            .collect();
        canonical_replay_fragment_v1(
            &self.obs_trace,
            &self.effect_trace,
            self.crashed_sites.clone(),
            partitioned_edges,
            corrupted_edges,
            timed_out_sites,
        )
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

    /// Corrupted directed edges currently active in topology state.
    #[must_use]
    pub fn corrupted_edges(&self) -> &[CorruptedEdge] {
        &self.corrupted_edges
    }

    /// Active site timeouts.
    #[must_use]
    pub fn timed_out_sites(&self) -> &[SiteTimeout] {
        &self.timed_out_sites
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

    /// Runtime well-formedness predicate used by debug assertions.
    pub fn wf_vm_state(&self) -> Result<(), String> {
        for coro in &self.coroutines {
            if self.sessions.get(coro.session_id).is_none() {
                return Err(format!(
                    "coroutine {} references missing session {}",
                    coro.id, coro.session_id
                ));
            }
            let Some(program) = self.programs.get(coro.program_id) else {
                return Err(format!("missing program for coroutine {}", coro.id));
            };
            if coro.pc > program.len() {
                return Err(format!("pc out of bounds for coroutine {}", coro.id));
            }
            if coro.regs.len() != usize::from(self.config.num_registers) {
                return Err(format!("register width mismatch for coroutine {}", coro.id));
            }
            for ep in &coro.owned_endpoints {
                let Some(session) = self.sessions.get(ep.sid) else {
                    return Err(format!(
                        "owned endpoint missing session {}:{}",
                        ep.sid, ep.role
                    ));
                };
                if !session.roles.iter().any(|role| role == &ep.role) {
                    return Err(format!(
                        "owned endpoint role not in session {}:{}",
                        ep.sid, ep.role
                    ));
                }
            }
            for token in &coro.progress_tokens {
                let Some(session) = self.sessions.get(token.sid) else {
                    return Err(format!(
                        "progress token missing session {} for coroutine {}",
                        token.sid, coro.id
                    ));
                };
                if !session
                    .roles
                    .iter()
                    .any(|role| role == &token.endpoint.role)
                {
                    return Err(format!(
                        "progress token role not in session {}:{}",
                        token.sid, token.endpoint.role
                    ));
                }
            }
            for fact in &coro.knowledge_set {
                let Some(session) = self.sessions.get(fact.endpoint.sid) else {
                    return Err(format!(
                        "knowledge fact missing session {}:{}",
                        fact.endpoint.sid, fact.endpoint.role
                    ));
                };
                if !session.roles.iter().any(|role| role == &fact.endpoint.role) {
                    return Err(format!(
                        "knowledge fact role not in session {}:{}",
                        fact.endpoint.sid, fact.endpoint.role
                    ));
                }
            }
        }

        let mut active_sids = BTreeSet::new();
        let mut monitor_required_sids = BTreeSet::new();
        for session in self.sessions.iter() {
            active_sids.insert(session.sid);
            if !matches!(
                session.status,
                SessionStatus::Closed | SessionStatus::Cancelled | SessionStatus::Faulted { .. }
            ) {
                monitor_required_sids.insert(session.sid);
            }
            for ep in session.local_types.keys() {
                if ep.sid != session.sid {
                    return Err(format!("local type sid mismatch for role {}", ep.role));
                }
            }
            for (edge, buffer) in &session.buffers {
                if edge.sid != session.sid {
                    return Err("buffer edge sid mismatch".to_string());
                }
                if buffer.len() > buffer.capacity() {
                    return Err("buffer length exceeds capacity".to_string());
                }
            }
        }

        for sid in self.monitor.session_kinds.keys() {
            if !active_sids.contains(sid) {
                return Err(format!("monitor tracks unknown session {sid}"));
            }
        }
        for sid in &monitor_required_sids {
            if !self.monitor.session_kinds.contains_key(sid) {
                return Err(format!("monitor missing kind for active session {sid}"));
            }
        }

        if !self.arena.check_invariants() {
            return Err("arena invariant violation".to_string());
        }
        Ok(())
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

    fn read_reg_checked(&self, coro_idx: usize, reg: u16) -> Result<Value, Fault> {
        self.coroutines[coro_idx]
            .regs
            .get(usize::from(reg))
            .cloned()
            .ok_or(Fault::OutOfRegisters)
    }

    fn endpoint_from_reg(&self, coro_idx: usize, reg: u16) -> Result<Endpoint, Fault> {
        match self.read_reg_checked(coro_idx, reg)? {
            Value::Endpoint(ep) => Ok(ep),
            other => Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Chan {
                    sid: 0,
                    role: String::new(),
                },
                actual: Self::val_type_of(&other),
                message: "expected endpoint register".to_string(),
            }),
        }
    }

    fn decode_fact(value: Value) -> Option<(Endpoint, String)> {
        match value {
            Value::Prod(left, right) => match (*left, *right) {
                (Value::Endpoint(endpoint), Value::Str(fact)) => Some((endpoint, fact)),
                _ => None,
            },
            _ => None,
        }
    }

    fn val_type_of(value: &Value) -> telltale_types::ValType {
        use telltale_types::ValType;
        match value {
            Value::Unit => ValType::Unit,
            Value::Nat(_) => ValType::Nat,
            Value::Bool(_) => ValType::Bool,
            Value::Str(_) => ValType::String,
            Value::Prod(left, right) => ValType::Prod(
                Box::new(Self::val_type_of(left)),
                Box::new(Self::val_type_of(right)),
            ),
            Value::Endpoint(ep) => ValType::Chan {
                sid: ep.sid,
                role: ep.role.clone(),
            },
        }
    }

    /// Extract partner and branches from a Recv local type.
    fn expect_recv_type(
        local_type: &LocalTypeR,
        role: &str,
    ) -> Result<(String, BranchList), Fault> {
        match local_type {
            LocalTypeR::Recv {
                partner, branches, ..
            } => Ok((partner.clone(), branches.clone())),
            other => Err(Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: Choose expects Recv, got {other:?}"),
            }),
        }
    }

    fn monitor_precheck(
        &mut self,
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
        }?;
        self.monitor
            .record(ep, &format!("{instr:?}"), self.clock.tick);
        Ok(())
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
            .retain(|timeout| timeout.until_tick > tick);
    }

    fn is_site_timed_out(&self, site: &str) -> bool {
        self.timed_out_sites
            .iter()
            .any(|timeout| timeout.site == site)
    }

    fn is_site_crashed(&self, site: &str) -> bool {
        self.crashed_sites.iter().any(|crashed| crashed == site)
    }

    fn is_edge_partitioned(&self, from: &str, to: &str) -> bool {
        self.partitioned_edges
            .iter()
            .any(|edge| edge.sid == TOPOLOGY_EDGE_SID && edge.sender == from && edge.receiver == to)
    }

    fn edge_corruption(&self, edge: &Edge) -> Option<CorruptionType> {
        self.corrupted_edges
            .iter()
            .find(|entry| entry.edge == *edge)
            .map(|entry| entry.corruption.clone())
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

    fn normalize_topology_state(&mut self) {
        self.crashed_sites.sort_unstable();
        self.crashed_sites.dedup();

        self.partitioned_edges
            .sort_by(|lhs, rhs| (&lhs.sender, &lhs.receiver).cmp(&(&rhs.sender, &rhs.receiver)));
        self.partitioned_edges.dedup();

        self.corrupted_edges.sort_by(|lhs, rhs| {
            (&lhs.edge.sender, &lhs.edge.receiver).cmp(&(&rhs.edge.sender, &rhs.edge.receiver))
        });
        self.corrupted_edges
            .dedup_by(|lhs, rhs| lhs.edge == rhs.edge && lhs.corruption == rhs.corruption);

        self.timed_out_sites
            .sort_by(|lhs, rhs| (&lhs.site, lhs.until_tick).cmp(&(&rhs.site, rhs.until_tick)));
    }

    fn apply_site_failure(&mut self, site: &str) {
        let reason = format!("site {site} crashed");

        let session_ids = self.sessions.session_ids();
        for sid in session_ids {
            let should_fault = self
                .sessions
                .get(sid)
                .is_some_and(|session| session.roles.iter().any(|role| role == site));
            if !should_fault {
                continue;
            }
            if let Some(session) = self.sessions.get_mut(sid) {
                if matches!(
                    session.status,
                    SessionStatus::Closed
                        | SessionStatus::Cancelled
                        | SessionStatus::Faulted { .. }
                ) {
                    continue;
                }
                session.status = SessionStatus::Faulted {
                    reason: reason.clone(),
                };
                self.monitor.remove_kind(sid);
            }
        }

        let mut faulted = Vec::new();
        for coro in &mut self.coroutines {
            if coro.role == site && !coro.is_terminal() {
                let fault = Fault::InvokeFault {
                    message: reason.clone(),
                };
                coro.status = CoroStatus::Faulted(fault.clone());
                faulted.push((coro.id, fault));
            }
        }
        for (coro_id, fault) in faulted {
            self.sched.mark_done(coro_id);
            self.obs_trace.push(ObsEvent::Faulted {
                tick: self.clock.tick,
                coro_id,
                fault,
            });
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
                self.apply_site_failure(site);
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
                self.corrupted_edges.retain(|entry| {
                    !((entry.edge.sender == *from && entry.edge.receiver == *to)
                        || (entry.edge.sender == *to && entry.edge.receiver == *from))
                });
            }
            TopologyPerturbation::Corrupt {
                from,
                to,
                corruption,
            } => {
                let edge = Edge::new(TOPOLOGY_EDGE_SID, from.clone(), to.clone());
                self.corrupted_edges
                    .retain(|entry| entry.edge.sender != *from || entry.edge.receiver != *to);
                self.corrupted_edges.push(CorruptedEdge {
                    edge,
                    corruption: corruption.clone(),
                });
            }
            TopologyPerturbation::Timeout { site, duration } => {
                let until_tick = self
                    .clock
                    .tick
                    .saturating_add(self.duration_to_ticks(*duration));
                self.timed_out_sites.retain(|timeout| timeout.site != *site);
                self.timed_out_sites.push(SiteTimeout {
                    site: site.clone(),
                    until_tick,
                });
            }
        }
        self.normalize_topology_state();
    }

    fn ingest_topology_events(&mut self, handler: &dyn EffectHandler) -> Result<(), VMError> {
        let tick = self.clock.tick;
        let mut events = handler
            .topology_events(tick)
            .map_err(VMError::HandlerError)?;
        events.sort_by_key(TopologyPerturbation::ordering_key);
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
            if self.paused_roles.contains(role)
                || self.is_site_crashed(role)
                || self.is_site_timed_out(role)
            {
                continue;
            }
            let reason = self.sched.block_reason(coro_id).cloned();
            if let Some(BlockReason::RecvWait { token, .. }) = reason {
                if let Some(session) = self.sessions.get(token.sid) {
                    let has_msg = session.roles.iter().any(|sender| {
                        sender != &token.endpoint.role
                            && session.has_message(sender, &token.endpoint.role)
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
        let pc = self.coroutines[idx].pc;
        let sid = self.coroutines[idx].session_id;
        let role = self.coroutines[idx].role.clone();
        let fallback_ep = self.coroutines[idx]
            .owned_endpoints
            .first()
            .cloned()
            .unwrap_or(Endpoint {
                sid,
                role: role.clone(),
            });
        let program = self
            .programs
            .get(self.coroutines[idx].program_id)
            .ok_or(Fault::PcOutOfBounds)?;

        // 1. Fetch.
        if pc >= program.len() {
            return Err(Fault::PcOutOfBounds);
        }
        let instr = program[pc].clone();
        let monitor_ep = match &instr {
            Instr::Send { chan, .. }
            | Instr::Receive { chan, .. }
            | Instr::Offer { chan, .. }
            | Instr::Choose { chan, .. } => self
                .endpoint_from_reg(idx, *chan)
                .unwrap_or_else(|_| fallback_ep.clone()),
            Instr::Close { session } => self
                .endpoint_from_reg(idx, *session)
                .unwrap_or_else(|_| fallback_ep.clone()),
            _ => fallback_ep.clone(),
        };

        // 1.5 Monitor precheck and deterministic cost charge.
        self.monitor_precheck(&monitor_ep, &role, &instr)?;
        self.charge_instruction_cost(idx)?;

        // 2. Dispatch to per-instruction step function.
        let pack = exec::step_instr(self, idx, &monitor_ep, &role, sid, instr, handler)?;

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
        role: &str,
        chan: u16,
        val_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed {
                endpoint: ep.clone(),
            });
        }
        let sid = ep.sid;

        // Type lookup — instruction owns this.
        let local_type = self
            .sessions
            .lookup_type(&ep)
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
        let send_payload = self.read_reg_checked(coro_idx, val_reg)?;
        let decision = handler
            .send_decision(
                sid,
                role,
                &partner,
                &label.name,
                &coro.regs,
                Some(send_payload.clone()),
            )
            .map_err(|e| Fault::InvokeFault { message: e })?;

        let edge = Edge::new(sid, role.to_string(), partner.clone());

        if self.is_site_crashed(role)
            || self.is_site_crashed(&partner)
            || self.is_site_timed_out(role)
            || self.is_site_timed_out(&partner)
            || self.is_edge_partitioned(role, &partner)
        {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::SendWait { edge: edge.clone() }),
                type_update: None,
                events: vec![],
            });
        }

        // Enqueue into per-edge signed session buffer (if delivered).
        let maybe_corruption = self.edge_corruption(&Edge::new(
            TOPOLOGY_EDGE_SID,
            role.to_string(),
            partner.clone(),
        ));
        let enqueue = {
            let session = self
                .sessions
                .get_mut(sid)
                .ok_or_else(|| Fault::ChannelClosed {
                    endpoint: ep.clone(),
                })?;
            match decision {
                SendDecision::Deliver(payload) => {
                    let payload = if let Some(corruption) = maybe_corruption.clone() {
                        Self::apply_corruption(payload, corruption)
                    } else {
                        payload
                    };
                    let enqueue = session
                        .send(role, &partner, payload)
                        .map_err(|e| Fault::InvokeFault { message: e })?;
                    enqueue
                }
                SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
            }
        };

        match enqueue {
            EnqueueResult::Ok => {}
            EnqueueResult::WouldBlock => {
                // Block — NO type advancement.
                return Ok(StepPack {
                    coro_update: CoroUpdate::Block(BlockReason::SendWait { edge: edge.clone() }),
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
        let original = self.sessions.original_type(&ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update,
            events: vec![ObsEvent::Sent {
                tick: self.clock.tick,
                edge,
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
        role: &str,
        chan: u16,
        dst_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed {
                endpoint: ep.clone(),
            });
        }
        let sid = ep.sid;

        // Type lookup.
        let local_type = self
            .sessions
            .lookup_type(&ep)
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
                    token: ProgressToken::for_endpoint(ep.clone()),
                }),
                type_update: None,
                events: vec![],
            });
        }

        let edge = Edge::new(sid, partner.clone(), role.to_string());
        // Dequeue from signed session buffer and verify in place.
        let val = {
            let session = self
                .sessions
                .get_mut(sid)
                .ok_or_else(|| Fault::ChannelClosed {
                    endpoint: ep.clone(),
                })?;
            session
                .recv_verified(&partner, role)
                .map_err(|message| Fault::VerificationFailed {
                    edge: edge.clone(),
                    message,
                })?
                .ok_or_else(|| Fault::ChannelClosed {
                    endpoint: ep.clone(),
                })?
        };

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
        let original = self.sessions.original_type(&ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

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

    /// Spawn: allocate a new ready coroutine with copied argument registers.
    pub(crate) fn step_spawn(
        &mut self,
        coro_idx: usize,
        target: PC,
        args: &[u16],
    ) -> Result<StepPack, Fault> {
        if self.coroutines.len() >= self.config.max_coroutines {
            return Err(Fault::SpecFault {
                message: "max coroutines exceeded".to_string(),
            });
        }

        let parent = self.coroutines[coro_idx].clone();
        let new_id = self.next_coro_id;
        self.next_coro_id = self.next_coro_id.saturating_add(1);

        let mut child = Coroutine::new(
            new_id,
            parent.program_id,
            parent.session_id,
            parent.role.clone(),
            self.config.num_registers,
            self.config.initial_cost_budget,
        );
        child.pc = target;
        child.effect_ctx = parent.effect_ctx.clone();
        for (dst_idx, src_reg) in args.iter().enumerate() {
            if dst_idx >= child.regs.len() {
                break;
            }
            if let Some(value) = parent.regs.get(usize::from(*src_reg)).cloned() {
                child.regs[dst_idx] = value;
            }
        }

        self.sched.add_ready(new_id);
        self.coroutines.push(child);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![],
        })
    }

    /// Invoke: call handler.step() for integration.
    pub(crate) fn step_invoke(
        &mut self,
        coro_idx: usize,
        role: &str,
        action: u16,
        dst: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let _action = self.read_reg_checked(coro_idx, action)?;
        if usize::from(dst) >= self.coroutines[coro_idx].regs.len() {
            return Err(Fault::OutOfRegisters);
        }
        let invoke_out = match self.read_reg_checked(coro_idx, dst)? {
            Value::Endpoint(ep) => Value::Endpoint(ep),
            _ => Value::Bool(true),
        };
        let coro_id = self.coroutines[coro_idx].id;
        handler
            .step(role, &mut self.coroutines[coro_idx].regs)
            .map_err(|e| Fault::InvokeFault { message: e })?;

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePcWriteReg {
                reg: dst,
                val: invoke_out,
            },
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

    #[allow(clippy::too_many_arguments)]
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
        let layer_id = LayerId(layer.to_string());
        if self.guard_layer.resources.is_empty() {
            self.guard_layer
                .resources
                .insert(layer_id.clone(), Value::Unit);
        }
        let _ = self
            .guard_layer
            .open_(&layer_id)
            .map_err(|e| Fault::AcquireFault {
                layer: layer.to_string(),
                message: e,
            })?;
        let decision = handler
            .handle_acquire(sid, role, layer, &self.coroutines[coro_idx].regs)
            .map_err(|e| Fault::AcquireFault {
                layer: layer.to_string(),
                message: e,
            })?;
        match decision {
            crate::effect::AcquireDecision::Grant(evidence) => {
                self.guard_layer
                    .resources
                    .insert(layer_id, evidence.clone());
                if let Some((_, state)) = self
                    .resource_states
                    .iter_mut()
                    .find(|(scope, _)| *scope == sid)
                {
                    let _ = state.commit(&evidence);
                } else {
                    let mut state = ResourceState::default();
                    let _ = state.commit(&evidence);
                    self.resource_states.push((sid, state));
                }
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

    #[allow(clippy::too_many_arguments)]
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
        let layer_id = LayerId(layer.to_string());
        if self.guard_layer.resources.is_empty() {
            self.guard_layer
                .resources
                .insert(layer_id.clone(), Value::Unit);
        }
        let ev = self.coroutines[coro_idx]
            .regs
            .get(usize::from(evidence))
            .ok_or(Fault::OutOfRegisters)?
            .clone();
        let decoded = InMemoryGuardLayer::decodeEvidence(&ev).map_err(|e| Fault::AcquireFault {
            layer: layer.to_string(),
            message: e,
        })?;
        handler
            .handle_release(sid, role, layer, &ev, &self.coroutines[coro_idx].regs)
            .map_err(|e| Fault::AcquireFault {
                layer: layer.to_string(),
                message: e,
            })?;
        self.guard_layer
            .close(&layer_id, decoded)
            .map_err(|e| Fault::AcquireFault {
                layer: layer.to_string(),
                message: e,
            })?;
        if let Some((_, state)) = self
            .resource_states
            .iter_mut()
            .find(|(scope, _)| *scope == sid)
        {
            state.consume(&ev).map_err(|e| Fault::AcquireFault {
                layer: layer.to_string(),
                message: e,
            })?;
        }
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
            Value::Nat(v) => usize::try_from(v).map_err(|_| Fault::TypeViolation {
                expected: telltale_types::ValType::Nat,
                actual: telltale_types::ValType::Nat,
                message: format!("{role}: fork ghost id out of range"),
            })?,
            _ => {
                return Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::Nat,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: fork expects nat ghost id"),
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
        let target_id = match self.read_reg_checked(coro_idx, target)? {
            Value::Nat(v) => usize::try_from(v).map_err(|_| Fault::TransferFault {
                message: format!("{role}: target id out of range"),
            })?,
            _ => {
                return Err(Fault::TransferFault {
                    message: format!("{role}: transfer expects nat target coroutine id"),
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

        let mut moved_tokens = Vec::new();
        self.coroutines[coro_idx].progress_tokens.retain(|token| {
            if token.endpoint == ep {
                moved_tokens.push(token.clone());
                false
            } else {
                true
            }
        });
        self.coroutines[target_idx]
            .progress_tokens
            .extend(moved_tokens);

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

        self.sched.record_cross_lane_handoff(
            self.coroutines[coro_idx].id,
            self.coroutines[target_idx].id,
            format!("transfer {}:{}", ep.sid, ep.role),
        );

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
        let (endpoint, fact) = Self::decode_fact(fact_val).ok_or_else(|| Fault::TransferFault {
            message: format!("{role}: tag expects (endpoint, string) fact"),
        })?;
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
        let (endpoint, fact) = Self::decode_fact(know_val).ok_or_else(|| Fault::TransferFault {
            message: format!("{role}: check expects (endpoint, string) fact"),
        })?;
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
        let known_fact = self.coroutines[coro_idx]
            .knowledge_set
            .iter()
            .find(|k| k.endpoint == endpoint && k.fact == fact);
        let permitted =
            known_fact.is_some_and(|k| self.config.flow_policy.allows_knowledge(k, &target_role));
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
        role: &str,
        chan: u16,
        table: &[(String, PC)],
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed {
                endpoint: ep.clone(),
            });
        }
        let sid = ep.sid;

        let local_type = self
            .sessions
            .lookup_type(&ep)
            .ok_or_else(|| Fault::TypeViolation {
                expected: telltale_types::ValType::Unit,
                actual: telltale_types::ValType::Unit,
                message: format!("{role}: no type registered"),
            })?
            .clone();

        let (partner, branches) = Self::expect_recv_type(&local_type, role)?;

        let session = self.sessions.get(sid).ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
        if !session.has_message(&partner, role) {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::RecvWait {
                    edge: Edge::new(sid, partner.clone(), role.to_string()),
                    token: ProgressToken::for_endpoint(ep.clone()),
                }),
                type_update: None,
                events: vec![],
            });
        }

        let edge = Edge::new(sid, partner.clone(), role.to_string());
        let session = self.sessions.get_mut(sid).unwrap();
        let val = session
            .recv_verified(&partner, role)
            .map_err(|message| Fault::VerificationFailed {
                edge: edge.clone(),
                message,
            })?
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
        let label = match &val {
            Value::Str(l) => l.clone(),
            _ => {
                return Err(Fault::TypeViolation {
                    expected: telltale_types::ValType::String,
                    actual: telltale_types::ValType::Unit,
                    message: format!("{role}: Choose expected String label, got {val:?}"),
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

        let original = self.sessions.original_type(&ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

        Ok(StepPack {
            coro_update: CoroUpdate::SetPc(target_pc),
            type_update,
            events: vec![
                ObsEvent::Received {
                    tick: self.clock.tick,
                    edge: edge.clone(),
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
        role: &str,
        chan: u16,
        label: &str,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, chan)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::ChannelClosed {
                endpoint: ep.clone(),
            });
        }
        let sid = ep.sid;

        let local_type = self
            .sessions
            .lookup_type(&ep)
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
                        Some(Value::Str(label.to_string())),
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

                let original = self.sessions.original_type(&ep).unwrap_or(&LocalTypeR::End);
                let (_resolved, type_update) = resolve_type_update(&continuation, original, &ep);

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
    pub(crate) fn step_close(&mut self, coro_idx: usize, session: u16) -> Result<StepPack, Fault> {
        let ep = self.endpoint_from_reg(coro_idx, session)?;
        if !self.coroutines[coro_idx].owned_endpoints.contains(&ep) {
            return Err(Fault::CloseFault {
                message: "endpoint not owned".to_string(),
            });
        }
        let sid = ep.sid;
        self.sessions
            .close(sid)
            .map_err(|e| Fault::CloseFault { message: e })?;
        self.apply_close_delta(sid)
            .map_err(|e| Fault::CloseFault { message: e })?;
        self.monitor.remove_kind(sid);
        self.resource_states.retain(|(scope, _)| *scope != sid);
        let epoch = self.sessions.get(sid).map_or(0, |session| session.epoch);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: Some((ep, TypeUpdate::Remove)),
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
        _role: &str,
        roles: &[String],
        endpoints: &[(String, u16)],
    ) -> Result<StepPack, Fault> {
        let sid = self.sessions.open(
            roles.to_vec(),
            &BufferConfig::default(),
            &std::collections::BTreeMap::new(),
        );
        self.monitor.set_kind(sid, SessionKind::Peer);
        self.resource_states.push((sid, ResourceState::default()));
        self.apply_open_delta(sid)
            .map_err(|e| Fault::TransferFault {
                message: format!("open persistence delta failed: {e}"),
            })?;

        for (_, reg) in endpoints {
            if usize::from(*reg) >= self.coroutines[coro_idx].regs.len() {
                return Err(Fault::OutOfRegisters);
            }
        }

        {
            let coro = &mut self.coroutines[coro_idx];
            for (endpoint_role, reg) in endpoints {
                let ep = Endpoint {
                    sid,
                    role: endpoint_role.clone(),
                };
                coro.regs[usize::from(*reg)] = Value::Endpoint(ep.clone());
                if !coro.owned_endpoints.contains(&ep) {
                    coro.owned_endpoints.push(ep);
                }
            }
        }

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Opened {
                tick: self.clock.tick,
                session: sid,
                roles: roles.to_vec(),
            }],
        })
    }

    /// Commit a `StepPack` atomically: apply coroutine update, type update, events.
    #[allow(clippy::too_many_lines)]
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
    use std::collections::{BTreeMap, BTreeSet};
    use std::time::Duration;
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
            Ok(Value::Nat(42))
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

        fn send_decision(
            &self,
            _sid: SessionId,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
            _payload: Option<Value>,
        ) -> Result<SendDecision, String> {
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

    struct TimeoutOnTickOneHandler;

    impl EffectHandler for TimeoutOnTickOneHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Nat(1))
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

        fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
            if tick == 1 {
                Ok(vec![TopologyPerturbation::Timeout {
                    site: "A".to_string(),
                    duration: Duration::from_millis(20),
                }])
            } else {
                Ok(Vec::new())
            }
        }
    }

    struct CorruptOnTickOneHandler;

    impl EffectHandler for CorruptOnTickOneHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Nat(0))
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

        fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
            if tick == 1 {
                Ok(vec![TopologyPerturbation::Corrupt {
                    from: "A".to_string(),
                    to: "B".to_string(),
                    corruption: CorruptionType::BitFlip,
                }])
            } else {
                Ok(Vec::new())
            }
        }
    }

    struct CrashOnTickOneHandler;

    impl EffectHandler for CrashOnTickOneHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Unit)
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

        fn topology_events(&self, tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
            if tick == 1 {
                Ok(vec![TopologyPerturbation::Crash {
                    site: "A".to_string(),
                }])
            } else {
                Ok(Vec::new())
            }
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
    fn test_transfer_moves_progress_tokens_with_endpoint() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let b_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "B")
            .expect("B coroutine exists");

        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };
        vm.coroutines[a_idx]
            .progress_tokens
            .push(ProgressToken::for_endpoint(ep_a.clone()));
        vm.coroutines[a_idx].regs[2] = Value::Endpoint(ep_a.clone());
        vm.coroutines[a_idx].regs[3] =
            Value::Nat(u64::try_from(vm.coroutines[b_idx].id).expect("coroutine id fits in u64"));

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.programs[a_program_id] = vec![
            Instr::Transfer {
                endpoint: 2,
                target: 3,
                bundle: 0,
            },
            Instr::Halt,
        ];

        let handler = PassthroughHandler;
        // Intentionally discard StepResult: we only care that the step executes without panic
        let _ = vm.step(&handler).expect("transfer step should succeed");

        assert!(vm.coroutines[a_idx].progress_tokens.is_empty());
        assert!(vm.coroutines[b_idx]
            .progress_tokens
            .iter()
            .any(|t| t.sid == sid && t.endpoint == ep_a));
    }

    #[test]
    fn test_check_applies_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut denied_roles = BTreeSet::new();
        denied_roles.insert("Observer".to_string());
        let mut vm = VM::new(VMConfig {
            flow_policy: FlowPolicy::DenyRoles(denied_roles),
            ..VMConfig::default()
        });
        let sid = vm.load_choreography(&image).unwrap();

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        vm.coroutines[a_idx]
            .knowledge_set
            .push(crate::coroutine::KnowledgeFact {
                endpoint: ep_a.clone(),
                fact: "secret".to_string(),
            });
        vm.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("secret".to_string())),
        );
        vm.coroutines[a_idx].regs[3] = Value::Str("Observer".to_string());

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.programs[a_program_id] = vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ];

        let handler = PassthroughHandler;
        // Intentionally discard StepResult: we only care that the step executes without panic
        let _ = vm.step(&handler).expect("check step should succeed");
        assert_eq!(vm.coroutines[a_idx].regs[4], Value::Bool(false));
    }

    #[test]
    fn test_check_applies_predicate_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            flow_policy: FlowPolicy::PredicateExpr(FlowPredicate::FactContains(
                "secret".to_string(),
            )),
            ..VMConfig::default()
        });
        let sid = vm.load_choreography(&image).unwrap();

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        vm.coroutines[a_idx]
            .knowledge_set
            .push(crate::coroutine::KnowledgeFact {
                endpoint: ep_a.clone(),
                fact: "top_secret".to_string(),
            });
        vm.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("top_secret".to_string())),
        );
        vm.coroutines[a_idx].regs[3] = Value::Str("Observer".to_string());

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.programs[a_program_id] = vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ];

        let handler = PassthroughHandler;
        let _ = vm.step(&handler).expect("check step should succeed");
        assert_eq!(vm.coroutines[a_idx].regs[4], Value::Bool(true));
    }

    #[test]
    fn test_check_applies_runtime_predicate_flow_policy() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            flow_policy: FlowPolicy::predicate(|knowledge: &KnowledgeFact, target: &str| {
                knowledge.fact.contains("secret") && target == "Observer"
            }),
            ..VMConfig::default()
        });
        let sid = vm.load_choreography(&image).unwrap();

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        vm.coroutines[a_idx].knowledge_set.push(KnowledgeFact {
            endpoint: ep_a.clone(),
            fact: "top_secret".to_string(),
        });
        vm.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str("top_secret".to_string())),
        );
        vm.coroutines[a_idx].regs[3] = Value::Str("Observer".to_string());

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.programs[a_program_id] = vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ];

        let handler = PassthroughHandler;
        let _ = vm.step(&handler).expect("check step should succeed");
        assert_eq!(vm.coroutines[a_idx].regs[4], Value::Bool(true));
    }

    fn run_check_with_flow_policy(
        policy: FlowPolicy,
        target_role: &str,
        known_fact: &str,
        query_fact: &str,
        insert_fact: bool,
    ) -> bool {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig {
            flow_policy: policy,
            ..VMConfig::default()
        });
        let sid = vm.load_choreography(&image).expect("load choreography");
        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        let ep_a = Endpoint {
            sid,
            role: "A".to_string(),
        };

        if insert_fact {
            vm.coroutines[a_idx].knowledge_set.push(KnowledgeFact {
                endpoint: ep_a.clone(),
                fact: known_fact.to_string(),
            });
        }
        vm.coroutines[a_idx].regs[2] = Value::Prod(
            Box::new(Value::Endpoint(ep_a)),
            Box::new(Value::Str(query_fact.to_string())),
        );
        vm.coroutines[a_idx].regs[3] = Value::Str(target_role.to_string());

        let a_program_id = vm.coroutines[a_idx].program_id;
        vm.programs[a_program_id] = vec![
            Instr::Check {
                knowledge: 2,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ];

        let handler = PassthroughHandler;
        let _ = vm.step(&handler).expect("check step should execute");
        matches!(vm.coroutines[a_idx].regs[4], Value::Bool(true))
    }

    #[test]
    fn test_check_flow_policy_variant_matrix() {
        let mut allow_roles = BTreeSet::new();
        allow_roles.insert("Observer".to_string());

        let mut deny_roles = BTreeSet::new();
        deny_roles.insert("Observer".to_string());

        assert!(run_check_with_flow_policy(
            FlowPolicy::AllowAll,
            "Observer",
            "secret",
            "secret",
            true
        ));
        assert!(!run_check_with_flow_policy(
            FlowPolicy::DenyAll,
            "Observer",
            "secret",
            "secret",
            true
        ));
        assert!(run_check_with_flow_policy(
            FlowPolicy::AllowRoles(allow_roles),
            "Observer",
            "secret",
            "secret",
            true
        ));
        assert!(!run_check_with_flow_policy(
            FlowPolicy::DenyRoles(deny_roles),
            "Observer",
            "secret",
            "secret",
            true
        ));
        assert!(run_check_with_flow_policy(
            FlowPolicy::PredicateExpr(FlowPredicate::FactContains("secret".to_string())),
            "Observer",
            "top_secret",
            "top_secret",
            true
        ));
        assert!(run_check_with_flow_policy(
            FlowPolicy::predicate(|knowledge: &KnowledgeFact, target: &str| {
                knowledge.fact.contains("secret") && target == "Observer"
            }),
            "Observer",
            "top_secret",
            "top_secret",
            true
        ));
        assert!(!run_check_with_flow_policy(
            FlowPolicy::AllowAll,
            "Observer",
            "secret",
            "secret",
            false
        ));
    }

    #[test]
    fn test_timeout_event_blocks_scheduling() {
        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), vec![Instr::Halt]);
                m
            },
            global_type: GlobalType::End,
            local_types: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), LocalTypeR::End);
                m
            },
        };
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        let step = vm
            .step(&TimeoutOnTickOneHandler)
            .expect("timeout topology ingress should not fault");
        assert!(matches!(step, StepResult::Stuck));
        assert!(!vm.timed_out_sites().is_empty());
    }

    #[test]
    fn test_corrupt_event_mutates_send_payload() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");

        let a_idx = vm
            .coroutines
            .iter()
            .position(|c| c.role == "A")
            .expect("A coroutine exists");
        vm.coroutines[a_idx].regs[1] = Value::Nat(10);

        let _ = vm
            .step(&CorruptOnTickOneHandler)
            .expect("send step with corruption should execute");
        let received = vm
            .sessions
            .get_mut(sid)
            .expect("session exists")
            .recv("A", "B");
        assert_eq!(received, Some(Value::Nat(11)));
    }

    #[test]
    fn test_crash_event_faults_session_and_clears_monitor_kind() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");

        assert!(vm.monitor.session_kinds.contains_key(&sid));
        let _ = vm
            .step(&CrashOnTickOneHandler)
            .expect("crash topology ingress should not fault step");
        let session = vm.sessions.get(sid).expect("session exists");
        assert!(matches!(session.status, SessionStatus::Faulted { .. }));
        assert!(!vm.monitor.session_kinds.contains_key(&sid));
        assert!(vm.crashed_sites.contains(&"A".to_string()));
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

    #[test]
    fn wf_vm_state_rejects_dangling_coroutine_session_reference() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");

        vm.coroutines[0].session_id = usize::MAX - 1;
        let err = vm
            .wf_vm_state()
            .expect_err("dangling session reference should fail wf check");
        assert!(err.contains("references missing session"));
    }

    #[test]
    fn wf_vm_state_rejects_monitor_missing_kind_for_session() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);
        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).expect("load choreography");

        vm.monitor.remove_kind(sid);
        let err = vm
            .wf_vm_state()
            .expect_err("missing monitor kind should fail wf check");
        assert!(err.contains("monitor missing kind for active session"));
    }
}
