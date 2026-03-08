impl<'de> Deserialize<'de> for SessionState {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let raw = SessionStateSerde::deserialize(deserializer)?;
        let mut session = Self {
            sid: raw.sid,
            roles: raw.roles,
            role_ids: BTreeMap::new(),
            local_types: raw.local_types,
            buffers: raw.buffers,
            edge_lookup: BTreeMap::new(),
            handler_ids: BTreeMap::new(),
            handlers_by_id: Vec::new(),
            edge_handler_lookup: BTreeMap::new(),
            default_handler_id: None,
            label_ids: BTreeMap::new(),
            labels_by_id: Vec::new(),
            branch_lookup: BTreeMap::new(),
            auth_leaves: raw.auth_leaves,
            auth_trees: raw.auth_trees,
            auth_roots: raw.auth_roots,
            edge_handlers: raw.edge_handlers,
            default_handler: raw.default_handler,
            edge_traces: raw.edge_traces,
            status: raw.status,
            epoch: raw.epoch,
        };
        session.rebuild_derived_indexes();
        Ok(session)
    }
}

/// Store of all sessions managed by the VM.
///
/// Provides type lookup/update methods that match the Lean
/// `SessionStore.lookupType` / `SessionStore.updateType` pattern.
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct SessionStore {
    sessions: BTreeMap<SessionId, SessionState>,
    #[serde(default)]
    archived_closed: Vec<ClosedSessionSummary>,
    next_id: SessionId,
}

impl SessionStore {
    /// Create an empty session store.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Open a new session with an externally supplied session id.
    ///
    /// Callers should source ids from `SessionStore::next_session_id()`.
    #[allow(clippy::needless_pass_by_value)]
    pub fn open_with_sid(
        &mut self,
        sid: SessionId,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> SessionId {
        let plan = SessionOpenPlan::new(&roles, initial_types);
        self.open_with_sid_from_plan(sid, &plan, buffer_config)
    }

    /// Open a new session from a reusable precomputed open plan.
    pub fn open_with_sid_from_plan(
        &mut self,
        sid: SessionId,
        plan: &SessionOpenPlan,
        buffer_config: &BufferConfig,
    ) -> SessionId {
        let state = SessionState::from_open_plan(sid, plan, buffer_config);
        self.sessions.insert(sid, state);
        self.next_id = self.next_id.max(sid.saturating_add(1));
        sid
    }

    /// Open a new session with the given roles, buffer config, and initial local types.
    ///
    /// Returns the session ID. Endpoints are constructed as `Endpoint { sid, role }`.
    #[allow(clippy::needless_pass_by_value)]
    pub fn open(
        &mut self,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> SessionId {
        let sid = self.next_id;
        self.open_with_sid(sid, roles, buffer_config, initial_types)
    }

    /// Next session identifier that will be allocated by `open`.
    #[must_use]
    pub fn next_session_id(&self) -> SessionId {
        self.next_id
    }

    // ---- Type state methods (match Lean SessionStore.lookupType / updateType) ----

    /// Lookup the current local type for an endpoint.
    ///
    /// Matches Lean `SessionStore.lookupType`.
    #[must_use]
    pub fn lookup_type(&self, ep: &Endpoint) -> Option<&LocalTypeR> {
        self.sessions
            .get(&ep.sid)?
            .local_types
            .get(ep)
            .map(|e| &e.current)
    }

    /// Update the local type for an endpoint (type advancement on commit).
    ///
    /// Matches Lean `SessionStore.updateType`.
    pub fn update_type(&mut self, ep: &Endpoint, new_type: LocalTypeR) {
        if let Some(session) = self.sessions.get_mut(&ep.sid) {
            if let Some(entry) = session.local_types.get_mut(ep) {
                entry.current = new_type;
            }
            session.refresh_endpoint_branch_lookup(ep);
        }
    }

    /// Update the original type (when entering a new Mu scope).
    pub fn update_original(&mut self, ep: &Endpoint, new_original: LocalTypeR) {
        if let Some(session) = self.sessions.get_mut(&ep.sid) {
            if let Some(entry) = session.local_types.get_mut(ep) {
                entry.original = new_original;
            }
        }
    }

    /// Get the original type for recursive unfolding.
    #[must_use]
    pub fn original_type(&self, ep: &Endpoint) -> Option<&LocalTypeR> {
        self.sessions
            .get(&ep.sid)?
            .local_types
            .get(ep)
            .map(|e| &e.original)
    }

    /// Remove type entry (on Halt/End — session endpoint completed).
    pub fn remove_type(&mut self, ep: &Endpoint) {
        if let Some(session) = self.sessions.get_mut(&ep.sid) {
            session.local_types.remove(ep);
            session.branch_lookup.remove(ep);
        }
    }

    // ---- Session access methods ----

    /// Get a reference to a session.
    #[must_use]
    pub fn get(&self, sid: SessionId) -> Option<&SessionState> {
        self.sessions.get(&sid)
    }

    /// Get a mutable reference to a session.
    pub fn get_mut(&mut self, sid: SessionId) -> Option<&mut SessionState> {
        self.sessions.get_mut(&sid)
    }

    /// Iterate over all sessions.
    pub fn iter(&self) -> impl Iterator<Item = &SessionState> {
        self.sessions.values()
    }

    /// Close a session.
    ///
    /// # Errors
    ///
    /// Returns an error if the session is not found.
    pub fn close(&mut self, sid: SessionId) -> Result<(), String> {
        let session = self
            .sessions
            .get_mut(&sid)
            .ok_or_else(|| format!("session {sid} not found"))?;

        session.status = SessionStatus::Closed;
        session.buffers.clear();
        session.edge_traces.clear();
        session.epoch = session.epoch.saturating_add(1);
        Ok(())
    }

    /// Closed/cancelled/faulted session identifiers still resident in the store.
    #[must_use]
    pub fn closed_session_ids(&self) -> Vec<SessionId> {
        self.sessions
            .iter()
            .filter_map(|(sid, session)| {
                matches!(
                    session.status,
                    SessionStatus::Closed
                        | SessionStatus::Cancelled
                        | SessionStatus::Faulted { .. }
                )
                .then_some(*sid)
            })
            .collect()
    }

    /// Reap specific session ids from live storage and archive compact summaries.
    ///
    /// # Panics
    ///
    /// Panics if a session disappears between the initial residency/status check
    /// and the subsequent removal from the store.
    pub fn reap_sessions(&mut self, session_ids: &[SessionId]) -> Vec<ClosedSessionSummary> {
        let mut reaped = Vec::new();
        for sid in session_ids {
            let Some(session) = self.sessions.get(sid) else {
                continue;
            };
            if !matches!(
                session.status,
                SessionStatus::Closed | SessionStatus::Cancelled | SessionStatus::Faulted { .. }
            ) {
                continue;
            }

            let session = self
                .sessions
                .remove(sid)
                .expect("session existence checked before removal");
            let summary = ClosedSessionSummary::from_session(&session);
            self.archived_closed.push(summary.clone());
            reaped.push(summary);
        }
        reaped
    }

    /// Reap all closed/cancelled/faulted sessions from live storage.
    pub fn reap_closed(&mut self) -> Vec<ClosedSessionSummary> {
        let sids = self.closed_session_ids();
        self.reap_sessions(&sids)
    }

    /// Number of active sessions.
    #[must_use]
    pub fn active_count(&self) -> usize {
        self.sessions
            .values()
            .filter(|s| s.status == SessionStatus::Active)
            .count()
    }

    /// Number of sessions still resident in the store.
    #[must_use]
    pub fn live_count(&self) -> usize {
        self.sessions.len()
    }

    /// All session IDs.
    #[must_use]
    pub fn session_ids(&self) -> Vec<SessionId> {
        self.sessions.keys().copied().collect()
    }

    /// Archived closed-session summaries retained after reaping.
    #[must_use]
    pub fn archived_closed(&self) -> &[ClosedSessionSummary] {
        &self.archived_closed
    }

    /// Approximate retained state for the session store.
    #[must_use]
    pub fn memory_usage(&self) -> SessionStoreMemoryUsage {
        let mut usage = SessionStoreMemoryUsage {
            live_sessions: self.sessions.len(),
            archived_closed_sessions: self.archived_closed.len(),
            ..SessionStoreMemoryUsage::default()
        };
        usage.retained_bytes.archived_closed = self
            .archived_closed
            .iter()
            .map(ClosedSessionSummary::retained_bytes_estimate)
            .sum();

        for session in self.sessions.values() {
            if matches!(
                session.status,
                SessionStatus::Closed | SessionStatus::Cancelled | SessionStatus::Faulted { .. }
            ) {
                usage.live_closed_sessions += 1;
            }
            usage.live_local_type_entries += session.local_types.len();
            usage.live_buffer_count += session.buffers.len();
            usage.live_buffered_messages += session
                .buffers
                .values()
                .map(BoundedBuffer::len)
                .sum::<usize>();
            usage.live_edge_handler_count += session.edge_handlers.len();
            usage.live_auth_leaf_count += session.auth_leaves.values().map(Vec::len).sum::<usize>();
            usage.live_auth_tree_count += session.auth_trees.len();
            usage.live_auth_root_count += session.auth_roots.len();
            usage.retained_bytes.live_sessions += session.retained_session_core_bytes();
            usage.retained_bytes.local_types += session.retained_local_type_bytes();
            usage.retained_bytes.buffers += session.retained_buffer_bytes();
            usage.retained_bytes.traces += session.retained_trace_bytes();
            usage.retained_bytes.auth += session.retained_auth_bytes();
            usage.retained_bytes.handlers += session.retained_handler_bytes();
        }
        usage.retained_bytes.total = usage
            .retained_bytes
            .live_sessions
            .saturating_add(usage.retained_bytes.archived_closed)
            .saturating_add(usage.retained_bytes.local_types)
            .saturating_add(usage.retained_bytes.buffers)
            .saturating_add(usage.retained_bytes.traces)
            .saturating_add(usage.retained_bytes.auth)
            .saturating_add(usage.retained_bytes.handlers);

        usage
    }

    /// Lookup edge-bound handler id.
    #[must_use]
    pub fn lookup_handler(&self, edge: &Edge) -> Option<&HandlerId> {
        self.sessions
            .get(&edge.sid)?
            .lookup_handler_for_roles(&edge.sender, &edge.receiver)
    }

    /// Lookup a default handler id for a session.
    #[must_use]
    pub fn default_handler_for_session(&self, sid: SessionId) -> Option<&HandlerId> {
        self.sessions.get(&sid)?.default_handler_binding()
    }

    /// Set the default handler id for a session.
    pub fn set_default_handler_for_session(&mut self, sid: SessionId, handler: HandlerId) {
        if let Some(session) = self.sessions.get_mut(&sid) {
            let handler_id = session.intern_handler_binding(&handler);
            session.default_handler = handler;
            session.default_handler_id = Some(handler_id);
        }
    }

    /// Update edge-bound handler id.
    pub fn update_handler(&mut self, edge: &Edge, handler: HandlerId) {
        if let Some(session) = self.sessions.get_mut(&edge.sid) {
            let handler_id = session.intern_handler_binding(&handler);
            if let Some(edge_key) = session.edge_key_for_roles(&edge.sender, &edge.receiver) {
                session.edge_handler_lookup.insert(edge_key, handler_id);
            }
            session.edge_handlers.insert(edge.clone(), handler);
        }
    }

    /// Lookup coherence trace for an edge.
    #[must_use]
    pub fn lookup_trace(&self, edge: &Edge) -> Option<&[ValType]> {
        self.sessions
            .get(&edge.sid)?
            .edge_traces
            .get(edge)
            .map(Vec::as_slice)
    }

    /// Update coherence trace for an edge.
    pub fn update_trace(&mut self, edge: &Edge, trace: Vec<ValType>) {
        if let Some(session) = self.sessions.get_mut(&edge.sid) {
            session.edge_traces.insert(edge.clone(), trace);
        }
    }
}

// ---- Type unfolding utilities ----

/// Unfold top-level `Mu` to its body.
///
/// Recursively strips `Mu` constructors to reach the first action.
#[must_use]
// RECURSION_SAFE: each step unwraps one Mu node from a finite local type tree.
pub fn unfold_mu(lt: &LocalTypeR) -> LocalTypeR {
    match lt {
        LocalTypeR::Mu { body, .. } => unfold_mu(body),
        other => other.clone(),
    }
}

/// Resolve a continuation that may be a `Var` (recursive reference).
///
/// If `cont` is `Var`, unfolds back to the original type's mu body.
/// If `cont` is `Mu`, unfolds it. Otherwise returns as-is.
#[must_use]
pub fn unfold_if_var(cont: &LocalTypeR, original: &LocalTypeR) -> LocalTypeR {
    match cont {
        LocalTypeR::Var(_) => unfold_mu(original),
        LocalTypeR::Mu { .. } => unfold_mu(cont),
        other => other.clone(),
    }
}

/// Like `unfold_if_var`, but also returns the new Mu scope (original) if one was entered.
///
/// When the continuation is a `Mu`, the Mu itself becomes the new original
/// for subsequent `Var` resolution. Returns `(resolved_type, Some(mu))` when
/// entering a new Mu scope, `(resolved_type, None)` otherwise.
#[must_use]
pub fn unfold_if_var_with_scope(
    cont: &LocalTypeR,
    original: &LocalTypeR,
) -> (LocalTypeR, Option<LocalTypeR>) {
    match cont {
        LocalTypeR::Var(_) => (unfold_mu(original), None),
        LocalTypeR::Mu { .. } => (unfold_mu(cont), Some(cont.clone())),
        other => (other.clone(), None),
    }
}
