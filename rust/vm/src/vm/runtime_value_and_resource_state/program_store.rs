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
