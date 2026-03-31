/// Errors from ProtocolMachine operations.
#[derive(Debug, thiserror::Error)]
pub enum ProtocolMachineError {
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
    HandlerError(EffectFailure),
    /// Persistence model lifecycle error.
    #[error("persistence error: {0}")]
    PersistenceError(String),
    /// Invalid concurrency parameter.
    #[error("invalid concurrency level: {n}")]
    InvalidConcurrency {
        /// Requested concurrency.
        n: usize,
    },
    /// ProtocolMachine configuration violates required runtime invariants.
    #[error("invalid ProtocolMachine config: {reason}")]
    InvalidConfig {
        /// Validation failure details.
        reason: String,
    },
    /// Thread-pool initialization failed.
    #[error("thread pool build failed: {message}")]
    ThreadPoolBuild {
        /// Build error details.
        message: String,
    },
    /// Code image failed runtime validation checks.
    #[error("invalid code image: {reason}")]
    InvalidCodeImage {
        /// Validation failure details.
        reason: String,
    },
    /// Ownership contract violation surfaced by a preferred host integration path.
    #[error("ownership contract error: {0}")]
    OwnershipContract(String),
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

// ---- The ProtocolMachine ----

/// Retained observability artifacts with optional bounded storage.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(transparent)]
pub(crate) struct RetainedLog<T>(Vec<T>);

fn default_true() -> bool {
    true
}

impl<T> Default for RetainedLog<T> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<T> RetainedLog<T> {
    fn push(&mut self, item: T, config: &ObservabilityRetentionConfig) {
        match config.mode {
            ObservabilityRetentionMode::Disabled => {}
            ObservabilityRetentionMode::Full => self.0.push(item),
            ObservabilityRetentionMode::Capped => {
                self.0.push(item);
                self.trim_to_capacity(config.capacity);
            }
        }
    }

    fn extend<I>(&mut self, iter: I, config: &ObservabilityRetentionConfig)
    where
        I: IntoIterator<Item = T>,
    {
        match config.mode {
            ObservabilityRetentionMode::Disabled => {}
            ObservabilityRetentionMode::Full => self.0.extend(iter),
            ObservabilityRetentionMode::Capped => {
                self.0.extend(iter);
                self.trim_to_capacity(config.capacity);
            }
        }
    }

    fn as_slice(&self) -> &[T] {
        &self.0
    }

    fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.0
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn drain(&mut self) -> Vec<T> {
        self.0.drain(..).collect()
    }

    fn trim_to_capacity(&mut self, capacity: usize) {
        if self.0.len() > capacity {
            let overflow = self.0.len() - capacity;
            self.0.drain(0..overflow);
        }
    }
}

impl<T> std::ops::Deref for RetainedLog<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

/// The choreographic ProtocolMachine.
///
/// Manages coroutines, sessions (which own type state), and a scheduler.
/// Multiple choreographies can be loaded into a single ProtocolMachine, each in its
/// own session namespace — justified by separation logic.
#[derive(Debug, Serialize, Deserialize)]
pub struct ProtocolMachine<I = (), G = (), P = NoopPersistence, Nu = DefaultVerificationModel>
where
    P: PersistenceModel,
{
    config: ProtocolMachineConfig,
    code: Option<Program>,
    programs: ProgramStore,
    identity_model: PhantomData<I>,
    guard_model: PhantomData<G>,
    persistence_model: PhantomData<P>,
    persistent: P::PState,
    verification: Nu,
    #[serde(default)]
    communication_consumption: DefaultCommunicationConsumption,
    #[serde(default)]
    communication_consumption_artifacts: RetainedLog<CommunicationConsumptionArtifact>,
    coroutines: Vec<Coroutine>,
    sessions: SessionStore,
    arena: Arena,
    resource_states: BTreeMap<ScopeId, ResourceState>,
    sched: Scheduler,
    monitor: SessionMonitor,
    obs_trace: RetainedLog<ObsEvent>,
    role_symbols: SymbolTable,
    label_symbols: SymbolTable,
    handler_symbols: SymbolTable,
    edge_symbols: EdgeSymbolTable,
    clock: SimClock,
    next_coro_id: usize,
    next_session_id: SessionId,
    paused_roles: BTreeSet<String>,
    #[serde(skip, default)]
    coro_slots: BTreeMap<usize, usize>,
    #[serde(skip, default)]
    role_coroutines: BTreeMap<String, Vec<usize>>,
    #[serde(skip, default)]
    paused_coro_ids: BTreeSet<usize>,
    #[serde(skip, default)]
    timed_out_coro_ids: BTreeSet<usize>,
    #[serde(skip, default)]
    session_open_plans: BTreeMap<String, crate::session::SessionOpenPlan>,
    #[serde(skip, default)]
    eligible_ready: BTreeSet<usize>,
    #[serde(skip, default = "default_true")]
    eligibility_dirty: bool,
    guard_layer: InMemoryGuardLayer,
    effect_trace: RetainedLog<EffectTraceEntry>,
    effect_exchanges: RetainedLog<EffectExchangeRecord>,
    operation_instances: RetainedLog<OperationInstance>,
    outstanding_effects: RetainedLog<OutstandingEffect>,
    progress_contracts: RetainedLog<ProgressContract>,
    progress_transitions: RetainedLog<ProgressTransition>,
    next_effect_id: u64,
    output_condition_checks: RetainedLog<OutputConditionCheck>,
    delegation_audit_log: RetainedLog<DelegationAuditRecord>,
    next_delegation_receipt_id: u64,
    authority_audit_log: RetainedLog<AuthorityAuditRecord>,
    next_authority_witness_id: u64,
    crashed_sites: BTreeSet<SiteId>,
    partitioned_edges: BTreeSet<(SiteId, SiteId)>,
    corrupted_edges: BTreeMap<(SiteId, SiteId), CorruptionType>,
    timed_out_sites: BTreeMap<SiteId, TimeoutWitness>,
    last_sched_step: Option<SchedStepDebug>,
    #[serde(skip, default)]
    last_pre_dispatch_state: Option<crate::refinement::ProtocolMachineRefinementSlice>,
    handler_identity_anchor: Option<String>,
}

/// Lean-aligned ProtocolMachine state alias.
pub type ProtocolMachineState<I = (), G = (), P = NoopPersistence, Nu = DefaultVerificationModel> =
    ProtocolMachine<I, G, P, Nu>;

impl<I, G, P, Nu> ProtocolMachine<I, G, P, Nu>
where
    P: PersistenceModel,
{
    /// Create a ProtocolMachine for arbitrary persistence/verification model parameters.
    #[must_use]
    pub fn new_with_models(config: ProtocolMachineConfig) -> Self
    where
        P::PState: Default,
        Nu: VerificationModel + Default,
    {
        config.assert_invariants();
        let tick_duration = config.tick_duration;
        let communication_replay_mode = config.communication_replay_mode;
        let sched = Scheduler::new(config.sched_policy.clone());
        let mut guard_resources = BTreeMap::new();
        for layer in &config.guard_layers {
            guard_resources.insert(layer.id.clone(), Value::Unit);
        }
        Self {
            config,
            code: None,
            programs: ProgramStore::new(),
            identity_model: PhantomData,
            guard_model: PhantomData,
            persistence_model: PhantomData,
            persistent: P::PState::default(),
            verification: Nu::default(),
            communication_consumption: DefaultCommunicationConsumption::new(
                communication_replay_mode,
            ),
            communication_consumption_artifacts: RetainedLog::default(),
            coroutines: Vec::new(),
            sessions: SessionStore::new(),
            arena: Arena::default(),
            resource_states: BTreeMap::new(),
            sched,
            monitor: SessionMonitor::default(),
            obs_trace: RetainedLog::default(),
            role_symbols: SymbolTable::new(),
            label_symbols: SymbolTable::new(),
            handler_symbols: SymbolTable::new(),
            edge_symbols: EdgeSymbolTable::new(),
            clock: SimClock::new(tick_duration),
            next_coro_id: 0,
            next_session_id: 0,
            paused_roles: BTreeSet::new(),
            coro_slots: BTreeMap::new(),
            role_coroutines: BTreeMap::new(),
            paused_coro_ids: BTreeSet::new(),
            timed_out_coro_ids: BTreeSet::new(),
            session_open_plans: BTreeMap::new(),
            eligible_ready: BTreeSet::new(),
            eligibility_dirty: true,
            guard_layer: InMemoryGuardLayer {
                resources: guard_resources
                    .into_iter()
                    .map(|(k, v)| (LayerId(k), v))
                    .collect(),
            },
            effect_trace: RetainedLog::default(),
            effect_exchanges: RetainedLog::default(),
            operation_instances: RetainedLog::default(),
            outstanding_effects: RetainedLog::default(),
            progress_contracts: RetainedLog::default(),
            progress_transitions: RetainedLog::default(),
            next_effect_id: 0,
            output_condition_checks: RetainedLog::default(),
            delegation_audit_log: RetainedLog::default(),
            next_delegation_receipt_id: 0,
            authority_audit_log: RetainedLog::default(),
            next_authority_witness_id: 0,
            crashed_sites: BTreeSet::new(),
            partitioned_edges: BTreeSet::new(),
            corrupted_edges: BTreeMap::new(),
            timed_out_sites: BTreeMap::new(),
            last_sched_step: None,
            last_pre_dispatch_state: None,
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
