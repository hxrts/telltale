/// State of a single session.
///
/// Stores per-endpoint local types (the type truth), message buffers,
/// and lifecycle status. Matches Lean `SessionState`.
#[derive(Debug, Serialize)]
pub struct SessionState {
    /// Session identifier.
    pub sid: SessionId,
    /// Role names in this session.
    pub roles: Vec<String>,
    /// Deterministic internal ids for participant roles.
    #[serde(skip)]
    role_ids: BTreeMap<String, u16>,
    /// Per-endpoint local type state. This IS the type truth.
    ///
    /// Matches Lean `localTypes : List (Endpoint × LocalType)`.
    pub local_types: BTreeMap<Endpoint, TypeEntry>,
    /// Message buffers keyed by directed edge.
    pub buffers: BTreeMap<Edge, SignedBuffer<Signature>>,
    /// Deterministic internal edge lookup keyed by interned role ids.
    #[serde(skip)]
    edge_lookup: BTreeMap<(u16, u16), Edge>,
    /// Deterministic internal ids for bound handlers.
    #[serde(skip)]
    handler_ids: BTreeMap<HandlerId, HandlerNumericId>,
    /// Reverse lookup for internal handler ids.
    #[serde(skip)]
    handlers_by_id: Vec<HandlerId>,
    /// Deterministic handler binding keyed by internal edge ids.
    #[serde(skip)]
    edge_handler_lookup: BTreeMap<(u16, u16), HandlerNumericId>,
    /// Session-wide fallback handler id.
    #[serde(skip)]
    default_handler_id: Option<HandlerNumericId>,
    /// Deterministic internal ids for branch labels reachable from current local types.
    #[serde(skip)]
    label_ids: BTreeMap<String, LabelNumericId>,
    /// Reverse lookup for internal label ids.
    #[serde(skip)]
    labels_by_id: Vec<String>,
    /// Cached branch resolution keyed by endpoint then label id.
    #[serde(skip)]
    branch_lookup: BTreeMap<Endpoint, BTreeMap<LabelNumericId, CachedBranch>>,
    /// Per-edge authenticated leaves for Merkle-auth tracking.
    pub auth_leaves: BTreeMap<Edge, Vec<Hash>>,
    /// Per-edge Merkle trees for incremental authenticated updates.
    #[serde(default)]
    pub auth_trees: BTreeMap<Edge, AuthTree>,
    /// Per-edge Merkle roots for signed-buffer history.
    pub auth_roots: BTreeMap<Edge, Hash>,
    /// Optional handler binding per edge.
    pub edge_handlers: BTreeMap<Edge, HandlerId>,
    /// Session-wide fallback handler id.
    #[serde(default = "default_handler_id")]
    pub default_handler: HandlerId,
    /// Coherence trace by edge.
    pub edge_traces: BTreeMap<Edge, Vec<ValType>>,
    /// Current status.
    pub status: SessionStatus,
    /// Epoch counter for draining.
    pub epoch: usize,
}

impl SessionState {
    pub(crate) fn from_open_plan(
        sid: SessionId,
        plan: &SessionOpenPlan,
        buffer_config: &BufferConfig,
    ) -> Self {
        let mut local_type_entries = Vec::with_capacity(plan.initial_types.len());
        for (role, current, original) in &plan.initial_types {
            local_type_entries.push((
                Endpoint {
                    sid,
                    role: role.clone(),
                },
                TypeEntry {
                    current: current.clone(),
                    original: original.clone(),
                },
            ));
        }
        let local_types = local_type_entries.into_iter().collect();

        let mut edge_entries = Vec::with_capacity(plan.edge_blueprint().len());
        let mut buffer_entries = Vec::with_capacity(plan.edge_blueprint().len());
        for (key, from, to) in plan.edge_blueprint() {
            let edge = Edge::new(sid, from.clone(), to.clone());
            edge_entries.push((*key, edge.clone()));
            buffer_entries.push((edge, BoundedBuffer::new(buffer_config)));
        }
        let edge_lookup = edge_entries.into_iter().collect();
        let buffers = buffer_entries.into_iter().collect();

        let default_handler = default_handler_id();
        let (handler_ids, handlers_by_id, edge_handler_lookup, default_handler_id) =
            Self::build_handler_indexes(&plan.role_ids, &default_handler, &BTreeMap::new());

        let mut state = Self {
            sid,
            roles: plan.roles.clone(),
            role_ids: plan.role_ids.clone(),
            local_types,
            buffers,
            edge_lookup,
            handler_ids,
            handlers_by_id,
            edge_handler_lookup,
            default_handler_id,
            label_ids: BTreeMap::new(),
            labels_by_id: Vec::new(),
            branch_lookup: BTreeMap::new(),
            auth_leaves: BTreeMap::new(),
            auth_trees: BTreeMap::new(),
            auth_roots: BTreeMap::new(),
            edge_handlers: BTreeMap::new(),
            default_handler,
            edge_traces: BTreeMap::new(),
            status: SessionStatus::Active,
            epoch: 0,
        };
        for role in &plan.active_branch_roles {
            state.refresh_endpoint_branch_lookup(&Endpoint {
                sid,
                role: role.clone(),
            });
        }
        state
    }

    fn retained_session_core_bytes(&self) -> usize {
        std::mem::size_of::<Self>()
            .saturating_add(serialized_bytes(&self.sid))
            .saturating_add(serialized_bytes(&self.roles))
            .saturating_add(serialized_bytes(&self.role_ids))
            .saturating_add(serialized_bytes(&self.edge_lookup))
            .saturating_add(serialized_bytes(&self.handler_ids))
            .saturating_add(serialized_bytes(&self.handlers_by_id))
            .saturating_add(serialized_bytes(&self.edge_handler_lookup))
            .saturating_add(serialized_bytes(&self.default_handler_id))
            .saturating_add(serialized_bytes(&self.label_ids))
            .saturating_add(serialized_bytes(&self.labels_by_id))
            .saturating_add(serialized_bytes(&self.branch_lookup))
            .saturating_add(serialized_bytes(&self.status))
            .saturating_add(serialized_bytes(&self.epoch))
    }

    fn retained_local_type_bytes(&self) -> usize {
        serialized_bytes(&self.local_types)
    }

    fn retained_buffer_bytes(&self) -> usize {
        serialized_bytes(&self.buffers)
    }

    fn retained_trace_bytes(&self) -> usize {
        serialized_bytes(&self.edge_traces)
    }

    fn retained_auth_bytes(&self) -> usize {
        serialized_bytes(&self.auth_leaves)
            .saturating_add(serialized_bytes(&self.auth_trees))
            .saturating_add(serialized_bytes(&self.auth_roots))
    }

    fn retained_handler_bytes(&self) -> usize {
        serialized_bytes(&self.edge_handlers)
            .saturating_add(serialized_bytes(&self.default_handler))
    }

    fn rebuild_derived_indexes(&mut self) {
        self.role_ids = Self::build_role_ids(&self.roles);
        self.edge_lookup = Self::build_edge_lookup_from_buffers(&self.role_ids, &self.buffers);
        self.refresh_handler_indexes();
        self.label_ids = BTreeMap::new();
        self.labels_by_id = Vec::new();
        self.branch_lookup = BTreeMap::new();
        let endpoints: Vec<Endpoint> = self.local_types.keys().cloned().collect();
        for endpoint in endpoints {
            self.refresh_endpoint_branch_lookup(&endpoint);
        }
    }

    pub(crate) fn refresh_handler_indexes(&mut self) {
        let (handler_ids, handlers_by_id, edge_handler_lookup, default_handler_id) =
            Self::build_handler_indexes(&self.role_ids, &self.default_handler, &self.edge_handlers);
        self.handler_ids = handler_ids;
        self.handlers_by_id = handlers_by_id;
        self.edge_handler_lookup = edge_handler_lookup;
        self.default_handler_id = default_handler_id;
    }

    pub(crate) fn build_role_ids(roles: &[String]) -> BTreeMap<String, u16> {
        roles
            .iter()
            .enumerate()
            .map(|(idx, role)| {
                (
                    role.clone(),
                    u16::try_from(idx).expect("role count should fit in u16"),
                )
            })
            .collect()
    }

    pub(crate) fn build_edge_lookup_from_buffers(
        role_ids: &BTreeMap<String, u16>,
        buffers: &BTreeMap<Edge, SignedBuffer<Signature>>,
    ) -> BTreeMap<EdgeKey, Edge> {
        let mut lookup = BTreeMap::new();
        for edge in buffers.keys() {
            let Some(from_id) = role_ids.get(&edge.sender) else {
                continue;
            };
            let Some(to_id) = role_ids.get(&edge.receiver) else {
                continue;
            };
            lookup.insert((*from_id, *to_id), edge.clone());
        }
        lookup
    }

    pub(crate) fn build_handler_indexes(
        role_ids: &BTreeMap<String, u16>,
        default_handler: &str,
        edge_handlers: &BTreeMap<Edge, HandlerId>,
    ) -> HandlerIndexBuild {
        let mut handler_ids = BTreeMap::new();
        let mut handlers_by_id = Vec::new();
        let intern_handler = |handler: &str,
                              handler_ids: &mut BTreeMap<HandlerId, HandlerNumericId>,
                              handlers_by_id: &mut Vec<HandlerId>|
         -> HandlerNumericId {
            if let Some(id) = handler_ids.get(handler) {
                return *id;
            }
            let id = u16::try_from(handlers_by_id.len()).expect("handler count should fit in u16");
            let owned = handler.to_string();
            handler_ids.insert(owned.clone(), id);
            handlers_by_id.push(owned);
            id
        };

        let default_handler_id = (!default_handler.is_empty())
            .then(|| intern_handler(default_handler, &mut handler_ids, &mut handlers_by_id));

        let mut edge_handler_lookup = BTreeMap::new();
        for (edge, handler) in edge_handlers {
            let Some(from_id) = role_ids.get(&edge.sender) else {
                continue;
            };
            let Some(to_id) = role_ids.get(&edge.receiver) else {
                continue;
            };
            let handler_id = intern_handler(handler, &mut handler_ids, &mut handlers_by_id);
            edge_handler_lookup.insert((*from_id, *to_id), handler_id);
        }

        (
            handler_ids,
            handlers_by_id,
            edge_handler_lookup,
            default_handler_id,
        )
    }

    fn edge_for_roles(&self, from: &str, to: &str) -> Option<&Edge> {
        let from_id = self.role_ids.get(from)?;
        let to_id = self.role_ids.get(to)?;
        self.edge_lookup.get(&(*from_id, *to_id))
    }

    fn edge_key_for_roles(&self, from: &str, to: &str) -> Option<(u16, u16)> {
        let from_id = self.role_ids.get(from)?;
        let to_id = self.role_ids.get(to)?;
        Some((*from_id, *to_id))
    }

    fn intern_label(&mut self, label: &str) -> LabelNumericId {
        if let Some(id) = self.label_ids.get(label) {
            return *id;
        }
        let id = u16::try_from(self.labels_by_id.len()).expect("label count should fit in u16");
        let owned = label.to_string();
        self.label_ids.insert(owned.clone(), id);
        self.labels_by_id.push(owned);
        id
    }

    fn intern_handler_binding(&mut self, handler: &str) -> HandlerNumericId {
        if let Some(id) = self.handler_ids.get(handler) {
            return *id;
        }
        let id = u16::try_from(self.handlers_by_id.len()).expect("handler count should fit in u16");
        let owned = handler.to_string();
        self.handler_ids.insert(owned.clone(), id);
        self.handlers_by_id.push(owned);
        id
    }

    fn handler_by_id(&self, handler_id: HandlerNumericId) -> Option<&HandlerId> {
        self.handlers_by_id.get(usize::from(handler_id))
    }

    fn branch_shape(local_type: &LocalTypeR) -> Option<(BranchDirection, &str, LocalBranches<'_>)> {
        match local_type {
            LocalTypeR::Send { partner, branches } => {
                Some((BranchDirection::Send, partner.as_str(), branches.as_slice()))
            }
            LocalTypeR::Recv { partner, branches } => {
                Some((BranchDirection::Recv, partner.as_str(), branches.as_slice()))
            }
            _ => None,
        }
    }

    pub(crate) fn refresh_endpoint_branch_lookup(&mut self, ep: &Endpoint) {
        self.branch_lookup.remove(ep);
        let Some(entry) = self.local_types.get(ep) else {
            return;
        };
        let Some((direction, partner, branches)) = Self::branch_shape(&entry.current) else {
            return;
        };
        let partner = partner.to_string();
        let branches: Vec<(String, Option<ValType>, LocalTypeR)> = branches
            .iter()
            .map(|(label, expected_type, continuation)| {
                (
                    label.name.clone(),
                    expected_type.clone(),
                    continuation.clone(),
                )
            })
            .collect();

        let mut endpoint_lookup = BTreeMap::new();
        for (label, expected_type, continuation) in branches {
            let label_id = self.intern_label(&label);
            endpoint_lookup.insert(
                label_id,
                CachedBranch {
                    direction,
                    partner: partner.clone(),
                    expected_type,
                    continuation,
                },
            );
        }
        if !endpoint_lookup.is_empty() {
            self.branch_lookup.insert(ep.clone(), endpoint_lookup);
        }
    }

    /// Lookup a cached branch resolution for an endpoint and label.
    #[must_use]
    pub(crate) fn lookup_branch_resolution(
        &self,
        ep: &Endpoint,
        label: &str,
    ) -> Option<&CachedBranch> {
        let label_id = self.label_ids.get(label)?;
        self.branch_lookup.get(ep)?.get(label_id)
    }

    fn update_auth_tree(&mut self, edge: &Edge, signed: &SignedValue<Signature>) {
        let bytes = bincode::serialize(signed).unwrap_or_default();
        let leaf = DefaultVerificationModel::hash(HashTag::MerkleLeaf, &bytes);
        self.auth_leaves.entry(edge.clone()).or_default().push(leaf);
        let tree = self
            .auth_trees
            .entry(edge.clone())
            .or_insert_with(|| AuthTree::new(Vec::new()));
        tree.append_leaf(leaf);
        self.auth_roots.insert(edge.clone(), tree.root());
    }

    /// Send a signed value from one role to another.
    ///
    /// # Errors
    ///
    /// Returns an error if no buffer exists for the given edge.
    pub fn send_signed(
        &mut self,
        from: &str,
        to: &str,
        signed: &SignedValue<Signature>,
    ) -> Result<crate::buffer::EnqueueResult, String> {
        let edge = self
            .edge_for_roles(from, to)
            .cloned()
            .ok_or_else(|| format!("no buffer for edge {from} → {to}"))?;
        let buf = self
            .buffers
            .get_mut(&edge)
            .ok_or_else(|| format!("no buffer for edge {from} → {to}"))?;
        let result = buf.enqueue(signed.clone());
        if matches!(result, crate::buffer::EnqueueResult::Ok) {
            self.update_auth_tree(&edge, signed);
        }
        Ok(result)
    }

    /// Send a value from one role to another.
    ///
    /// Returns the enqueue result from the buffer.
    ///
    /// # Errors
    ///
    /// Returns an error if no buffer exists for the given edge.
    pub fn send(
        &mut self,
        from: &str,
        to: &str,
        val: Value,
    ) -> Result<crate::buffer::EnqueueResult, String> {
        let signer = signing_key_for_endpoint(&Endpoint {
            sid: self.sid,
            role: from.to_string(),
        });
        let signature = signValue(&val, &signer);
        self.send_signed(
            from,
            to,
            &SignedValue {
                payload: val,
                signature,
                sequence_no: 0,
            },
        )
    }

    /// Send a value from one role to another with explicit sequence number.
    ///
    /// # Errors
    ///
    /// Returns an error if no buffer exists for the given edge.
    pub fn send_with_sequence(
        &mut self,
        from: &str,
        to: &str,
        val: Value,
        sequence_no: u64,
    ) -> Result<crate::buffer::EnqueueResult, String> {
        let signer = signing_key_for_endpoint(&Endpoint {
            sid: self.sid,
            role: from.to_string(),
        });
        let signature = signValue(&val, &signer);
        self.send_signed(
            from,
            to,
            &SignedValue {
                payload: val,
                signature,
                sequence_no,
            },
        )
    }

    /// Receive a signed value destined for a role from a specific sender.
    pub fn recv_signed(&mut self, from: &str, to: &str) -> Option<SignedValue<Signature>> {
        let edge = self.edge_for_roles(from, to)?.clone();
        self.buffers.get_mut(&edge).and_then(|buf| buf.dequeue())
    }

    /// Receive and verify a value destined for a role from a specific sender.
    ///
    /// # Errors
    ///
    /// Returns an error if signature verification fails.
    pub fn recv_verified_signed(
        &mut self,
        from: &str,
        to: &str,
    ) -> Result<Option<SignedValue<Signature>>, String> {
        let sender = Endpoint {
            sid: self.sid,
            role: from.to_string(),
        };
        let verifying = verifying_key_for_endpoint(&sender);
        let signed = self.recv_signed(from, to);
        let Some(signed) = signed else {
            return Ok(None);
        };
        if !verifySignedValue(&signed.payload, &signed.signature, &verifying) {
            return Err(format!(
                "signature verification failed on edge {from} -> {to}"
            ));
        }
        Ok(Some(signed))
    }

    /// Receive and verify a value destined for a role from a specific sender.
    ///
    /// # Errors
    ///
    /// Returns an error if signature verification fails.
    pub fn recv_verified(&mut self, from: &str, to: &str) -> Result<Option<Value>, String> {
        Ok(self
            .recv_verified_signed(from, to)?
            .map(|signed| signed.payload))
    }

    /// Receive a value destined for a role from a specific sender.
    pub fn recv(&mut self, from: &str, to: &str) -> Option<Value> {
        self.recv_verified(from, to).ok().flatten()
    }

    /// Check if there is a message available on an edge.
    #[must_use]
    pub fn has_message(&self, from: &str, to: &str) -> bool {
        let Some(edge) = self.edge_for_roles(from, to) else {
            return false;
        };
        self.buffers.get(edge).is_some_and(|buf| !buf.is_empty())
    }

    /// Lookup an edge-bound handler by role pair using the internal numeric path.
    #[must_use]
    pub fn lookup_handler_for_roles(&self, from: &str, to: &str) -> Option<&HandlerId> {
        if self.edge_handlers.is_empty() {
            return None;
        }
        let edge_key = self.edge_key_for_roles(from, to)?;
        let handler_id = self.edge_handler_lookup.get(&edge_key)?;
        self.handler_by_id(*handler_id)
    }

    /// Lookup the session-wide fallback handler using the internal numeric path.
    #[must_use]
    pub fn default_handler_binding(&self) -> Option<&HandlerId> {
        if self.default_handler.is_empty() {
            return None;
        }
        let handler_id = self.default_handler_id?;
        self.handler_by_id(handler_id)
    }

    /// Whether the session currently has any handler binding configured.
    #[must_use]
    pub fn has_bound_handler(&self) -> bool {
        !self.default_handler.is_empty() || !self.edge_handlers.is_empty()
    }
}

#[derive(Debug, Deserialize)]
struct SessionStateSerde {
    sid: SessionId,
    roles: Vec<String>,
    local_types: BTreeMap<Endpoint, TypeEntry>,
    buffers: BTreeMap<Edge, SignedBuffer<Signature>>,
    auth_leaves: BTreeMap<Edge, Vec<Hash>>,
    #[serde(default)]
    auth_trees: BTreeMap<Edge, AuthTree>,
    auth_roots: BTreeMap<Edge, Hash>,
    edge_handlers: BTreeMap<Edge, HandlerId>,
    #[serde(default = "default_handler_id")]
    default_handler: HandlerId,
    edge_traces: BTreeMap<Edge, Vec<ValType>>,
    status: SessionStatus,
    epoch: usize,
}
