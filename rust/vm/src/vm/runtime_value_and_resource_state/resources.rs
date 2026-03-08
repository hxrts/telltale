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
