fn default_instruction_cost() -> usize {
    1
}

fn default_initial_cost_budget() -> usize {
    usize::MAX
}

fn default_config_schema_version() -> u32 {
    1
}

fn default_max_payload_bytes() -> usize {
    64 * 1024
}

/// Scope identifier type, aligned with Lean's scope representation.
pub type ScopeId = usize;

/// Lean-aligned immutable program representation.
pub type Program = Box<[Instr]>;

/// Immutable program storage with deterministic interning.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ProgramStore {
    programs: Vec<Program>,
    #[serde(default)]
    cache: BTreeMap<Vec<u8>, usize>,
}

impl ProgramStore {
    /// Create an empty immutable program store.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn ensure_cache_initialized(&mut self) {
        if self.cache.len() == self.programs.len() {
            return;
        }
        self.cache.clear();
        for (idx, program) in self.programs.iter().enumerate() {
            self.cache.insert(Self::cache_key(program), idx);
        }
    }

    fn cache_key(program: &[Instr]) -> Vec<u8> {
        bincode::serialize(program).expect("program serialization for cache key should succeed")
    }

    /// Reserve space for additional unique programs.
    pub fn reserve(&mut self, additional: usize) {
        self.programs.reserve(additional);
    }

    /// Intern a program and return its stable index.
    pub fn intern(&mut self, program: Vec<Instr>) -> usize {
        self.ensure_cache_initialized();
        let key = Self::cache_key(&program);
        if let Some(existing) = self.cache.get(&key) {
            return *existing;
        }
        let program_id = self.programs.len();
        self.programs.push(program.into_boxed_slice());
        self.cache.insert(key, program_id);
        program_id
    }

    /// Fetch an immutable program by id.
    #[must_use]
    pub fn get(&self, program_id: usize) -> Option<&Program> {
        self.programs.get(program_id)
    }

    /// Number of unique programs retained by the store.
    #[must_use]
    pub fn len(&self) -> usize {
        self.programs.len()
    }

    /// Whether the program store is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.programs.is_empty()
    }

    /// Total instruction count across all unique programs.
    #[must_use]
    pub fn instruction_count(&self) -> usize {
        self.programs.iter().map(|program| program.len()).sum()
    }

    #[cfg(test)]
    fn replace_for_test(&mut self, program_id: usize, program: Vec<Instr>) {
        self.ensure_cache_initialized();
        if let Some(existing) = self.programs.get(program_id) {
            let key = Self::cache_key(existing);
            self.cache.remove(&key);
        }
        self.programs[program_id] = program.into_boxed_slice();
        let new_key = Self::cache_key(&self.programs[program_id]);
        self.cache.insert(new_key, program_id);
    }
}

/// Branch list type used in local types.
type BranchList = Vec<(
    telltale_types::Label,
    Option<telltale_types::ValType>,
    LocalTypeR,
)>;

// RECURSION_SAFE: structural recursion over a finite runtime value tree.
pub(crate) fn runtime_value_val_type(value: &Value) -> ValType {
    match value {
        Value::Unit => ValType::Unit,
        Value::Nat(_) => ValType::Nat,
        Value::Bool(_) => ValType::Bool,
        Value::Str(_) => ValType::String,
        Value::Prod(left, right) => ValType::Prod(
            Box::new(runtime_value_val_type(left)),
            Box::new(runtime_value_val_type(right)),
        ),
        Value::Endpoint(endpoint) => ValType::Chan {
            sid: endpoint.sid,
            role: endpoint.role.clone(),
        },
    }
}

// RECURSION_SAFE: structural recursion over a finite runtime value tree.
pub(crate) fn runtime_value_wire_size_bytes(value: &Value) -> usize {
    match value {
        Value::Unit => 1,
        Value::Nat(_) => 8,
        Value::Bool(_) => 1,
        Value::Str(text) => 8_usize.saturating_add(text.len()),
        Value::Prod(left, right) => 1_usize
            .saturating_add(runtime_value_wire_size_bytes(left))
            .saturating_add(runtime_value_wire_size_bytes(right)),
        Value::Endpoint(endpoint) => 8_usize
            .saturating_add(8_usize)
            .saturating_add(endpoint.role.len()),
    }
}

// RECURSION_SAFE: structural recursion over finite value/type trees.
pub(crate) fn runtime_value_matches_val_type(value: &Value, expected: &ValType) -> bool {
    match (value, expected) {
        (Value::Unit, ValType::Unit) => true,
        (Value::Nat(_), ValType::Nat) => true,
        (Value::Bool(_), ValType::Bool) => true,
        (Value::Str(_), ValType::String) => true,
        (Value::Prod(left, right), ValType::Prod(expected_left, expected_right)) => {
            runtime_value_matches_val_type(left, expected_left)
                && runtime_value_matches_val_type(right, expected_right)
        }
        (Value::Endpoint(endpoint), ValType::Chan { sid, role }) => {
            endpoint.sid == *sid && endpoint.role == *role
        }
        _ => false,
    }
}

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

#[allow(clippy::derivable_impls)]
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
                // Dynamic closure policies cannot be value-compared.
                // Equality is identity-based: true only when both variants
                // point to the exact same trait object instance.
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

/// Typed runtime tuning profile for benchmark/runtime configuration harmonization.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum RuntimeTuningProfile {
    /// Default production-like tuning.
    #[default]
    Standard,
    /// Reference profile approximating early M1 stress behavior.
    M1StressReference,
}

/// Threaded scheduler round semantics mode.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum ThreadedRoundSemantics {
    /// Canonical one-step semantics aligned with Lean runner rounds.
    #[default]
    CanonicalOneStep,
    /// Performance extension: multi-pick waves within one round.
    WaveParallelExtension,
}

/// Effect-trace capture mode for runtime overhead control.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum EffectTraceCaptureMode {
    /// Record all canonical effect kinds.
    #[default]
    Full,
    /// Record only topology ingress events.
    TopologyOnly,
    /// Disable effect-trace recording.
    Disabled,
}

/// Retention policy for stored observability artifacts.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum ObservabilityRetentionMode {
    /// Retain all recorded artifacts.
    #[default]
    Full,
    /// Retain only the most recent `capacity` artifacts per stream.
    Capped,
    /// Disable retention entirely while preserving runtime behavior.
    Disabled,
}

/// Retention configuration for observability artifacts.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct ObservabilityRetentionConfig {
    /// Retention policy for observability artifacts.
    #[serde(default)]
    pub mode: ObservabilityRetentionMode,
    /// Maximum retained items per stream when `mode = capped`.
    #[serde(default = "default_observability_retention_capacity")]
    pub capacity: usize,
}

const fn default_observability_retention_capacity() -> usize {
    4_096
}

impl Default for ObservabilityRetentionConfig {
    fn default() -> Self {
        Self {
            mode: ObservabilityRetentionMode::Full,
            capacity: default_observability_retention_capacity(),
        }
    }
}

/// Payload validation mode for runtime message hardening.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum PayloadValidationMode {
    /// Disable VM-side payload validation checks.
    Off,
    /// Validate payload size and annotated `ValType` compatibility.
    #[default]
    Structural,
    /// Structural checks plus strict annotation requirement for `Send` and `Receive`.
    StrictSchema,
}
