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
    /// Advance PC by 1 and set blocked status.
    AdvancePcBlock(BlockReason),
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

#[derive(Clone, Copy)]
pub(crate) struct GuardAcquireInput<'a> {
    pub coro_idx: usize,
    pub endpoint: &'a Endpoint,
    pub role: &'a str,
    pub sid: SessionId,
    pub layer: &'a str,
    pub dst: u16,
}

#[derive(Clone, Copy)]
pub(crate) struct GuardReleaseInput<'a> {
    pub coro_idx: usize,
    pub endpoint: &'a Endpoint,
    pub role: &'a str,
    pub sid: SessionId,
    pub layer: &'a str,
    pub evidence: u16,
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
    resource_states: BTreeMap<ScopeId, ResourceState>,
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
    crashed_sites: BTreeSet<SiteId>,
    partitioned_edges: BTreeSet<(SiteId, SiteId)>,
    corrupted_edges: BTreeMap<(SiteId, SiteId), CorruptionType>,
    timed_out_sites: BTreeMap<SiteId, u64>,
    last_sched_step: Option<SchedStepDebug>,
    handler_identity_anchor: Option<String>,
}

/// Lean-aligned VM state alias.
pub type VMState<I = (), G = (), P = NoopPersistence, Nu = DefaultVerificationModel> =
    VM<I, G, P, Nu>;

impl<I, G, P, Nu> VM<I, G, P, Nu>
where
    P: PersistenceModel,
{
    /// Create a VM for arbitrary persistence/verification model parameters.
    #[must_use]
    pub fn new_with_models(config: VMConfig) -> Self
    where
        P::PState: Default,
        Nu: VerificationModel + Default,
    {
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
            persistent: P::PState::default(),
            verification: Nu::default(),
            coroutines: Vec::new(),
            sessions: SessionStore::new(),
            arena: Arena::default(),
            resource_states: BTreeMap::new(),
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
            crashed_sites: BTreeSet::new(),
            partitioned_edges: BTreeSet::new(),
            corrupted_edges: BTreeMap::new(),
            timed_out_sites: BTreeMap::new(),
            last_sched_step: None,
            handler_identity_anchor: None,
        }
    }

    /// Borrow the persistent state tracked by the configured persistence model.
    #[must_use]
    pub fn persistent_state(&self) -> &P::PState {
        &self.persistent
    }

    /// Mutably borrow persistent state.
    pub fn persistent_state_mut(&mut self) -> &mut P::PState {
        &mut self.persistent
    }

    fn apply_open_delta(&mut self, sid: SessionId) -> Result<(), String> {
        let delta = P::open_delta(sid);
        P::apply(&mut self.persistent, &delta)
    }

    fn apply_close_delta(&mut self, sid: SessionId) -> Result<(), String> {
        let delta = P::close_delta(sid);
        P::apply(&mut self.persistent, &delta)
    }

    fn apply_invoke_delta(&mut self, sid: SessionId, action: &str) -> Result<(), String> {
        if let Some(delta) = P::invoke_delta(sid, action) {
            P::apply(&mut self.persistent, &delta)?;
        }
        Ok(())
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

