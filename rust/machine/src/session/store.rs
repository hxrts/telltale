// Session store serialization and index rebuilding.
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
            ownership: raw.ownership,
        };
        session.rebuild_derived_indexes();
        Ok(session)
    }
}

/// Store of all sessions managed by the ProtocolMachine.
///
/// Provides type lookup/update methods that match the Lean
/// `SessionStore.lookupType` / `SessionStore.updateType` pattern.
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct SessionStore {
    sessions: BTreeMap<SessionId, SessionState>,
    #[serde(default)]
    archived_closed: Vec<ClosedSessionSummary>,
    #[serde(default)]
    ownership_audit_log: Option<Vec<AuthorityAuditRecord>>,
    next_id: SessionId,
}

impl SessionStore {
    /// Apply one host transition and retain its actual producer order, including
    /// rejection records emitted before an error. Locks/adapters call this only
    /// between machine steps; the supplied tick is the machine's current tick.
    pub(crate) fn with_owned_session_at<T>(
        &mut self,
        sid: SessionId,
        tick: Option<u64>,
        operation: impl FnOnce(&mut SessionState) -> Result<T, OwnershipError>,
    ) -> Result<T, OwnershipError> {
        if !self.sessions.contains_key(&sid) {
            return Err(OwnershipError::SessionNotFound { session_id: sid });
        }
        self.ensure_ownership_audit_history();
        let session = self
            .sessions
            .get_mut(&sid)
            .ok_or(OwnershipError::SessionNotFound { session_id: sid })?;
        let start = session.ownership.audit_log.len();
        let result = operation(session);
        let records = session.authority_records_since(start);
        if let Some(tick) = tick {
            for record in records.iter_mut() {
                record.tick = Some(tick);
            }
        }
        self.ownership_audit_log
            .as_mut()
            .expect("audit journal initialized")
            .extend_from_slice(records);
        result
    }

    fn ensure_ownership_audit_history(&mut self) {
        if self.ownership_audit_log.is_none() {
            // Preserve legacy observations without inventing their emission times.
            self.ownership_audit_log = Some(self.ownership_audit_history());
        }
    }

    pub(crate) fn ownership_audit_history(&self) -> Vec<AuthorityAuditRecord> {
        self.ownership_audit_log.clone().unwrap_or_else(|| {
            self.sessions
                .values()
                .flat_map(|session| session.ownership.audit_log.iter().cloned())
                .collect()
        })
    }

    /// Create an empty session store.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Open a new session with an externally supplied session id.
    ///
    /// This is fresh allocation, not restore/resume. Older ids cannot be reissued.
    ///
    /// # Errors
    /// Rejects resident/previous ids or exhaustion before mutation.
    #[allow(clippy::needless_pass_by_value)]
    pub fn open_with_sid(
        &mut self,
        sid: SessionId,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> Result<SessionId, SessionAllocationError> {
        let plan = SessionOpenPlan::new(&roles, initial_types);
        self.open_with_sid_from_plan(sid, &plan, buffer_config)
    }

    /// Open a new session from a reusable precomputed open plan.
    ///
    /// # Errors
    /// Rejects resident/previous ids or exhaustion before mutation.
    pub fn open_with_sid_from_plan(
        &mut self,
        sid: SessionId,
        plan: &SessionOpenPlan,
        buffer_config: &BufferConfig,
    ) -> Result<SessionId, SessionAllocationError> {
        let next = admit_session_id(sid, self.next_id, self.sessions.contains_key(&sid))?;
        let state = SessionState::from_open_plan(sid, plan, buffer_config);
        self.sessions.insert(sid, state);
        self.next_id = next;
        Ok(sid)
    }

    /// Open a new session with the given roles, buffer config, and initial local types.
    ///
    /// Returns the session ID. Endpoints are constructed as `Endpoint { sid, role }`.
    ///
    /// # Errors
    /// Rejects a non-fresh next id or exhaustion before mutation.
    #[allow(clippy::needless_pass_by_value)]
    pub fn open(
        &mut self,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> Result<SessionId, SessionAllocationError> {
        let sid = self.next_id;
        self.open_with_sid(sid, roles, buffer_config, initial_types)
    }

    /// Next session high-water mark. `usize::MAX` denotes exhausted allocation.
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

    /// Get the current live ownership capability for a session, if any.
    #[must_use]
    pub fn current_ownership(&self, sid: SessionId) -> Option<&OwnershipCapability> {
        self.sessions.get(&sid)?.ownership.current.as_ref()
    }

    /// Validate that a capability still matches the live owner state.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the session is missing, terminal, or stale.
    pub fn validate_ownership_capability(
        &self,
        capability: &OwnershipCapability,
    ) -> Result<(), OwnershipError> {
        let session =
            self.sessions
                .get(&capability.session_id)
                .ok_or(OwnershipError::SessionNotFound {
                    session_id: capability.session_id,
                })?;
        SessionState::validate_current_owner(session, capability)
    }

    /// Read deterministic authority audit records for one session.
    #[must_use]
    pub fn authority_audit_log(&self, sid: SessionId) -> Option<&[AuthorityAuditRecord]> {
        Some(self.sessions.get(&sid)?.ownership.audit_log.as_slice())
    }

    /// Claim ownership for an unclaimed session.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the session is missing, terminal, or already claimed.
    pub fn claim_ownership(
        &mut self,
        sid: SessionId,
        owner_id: impl Into<FragmentOwnerId>,
        scope: OwnershipScope,
    ) -> Result<OwnershipCapability, OwnershipError> {
        self.with_owned_session_at(sid, None, |session| {
            session.claim_ownership(sid, owner_id, scope)
        })
    }

    /// Release the current owner capability for a session.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or a transfer is still pending.
    pub fn release_ownership(
        &mut self,
        capability: &OwnershipCapability,
    ) -> Result<(), OwnershipError> {
        self.with_owned_session_at(capability.session_id, None, |session| {
            session.release_ownership(capability)
        })
    }

    /// Begin an explicit ownership transfer and return a typed receipt.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or another transfer is pending.
    pub fn begin_ownership_transfer(
        &mut self,
        capability: &OwnershipCapability,
        new_owner_id: impl Into<FragmentOwnerId>,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipReceipt, OwnershipError> {
        self.with_owned_session_at(capability.session_id, None, |session| {
            session.begin_ownership_transfer(capability, new_owner_id, new_scope)
        })
    }

    /// Commit a previously staged ownership transfer.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the receipt is stale or mismatched.
    pub fn commit_ownership_transfer(
        &mut self,
        receipt: &OwnershipReceipt,
    ) -> Result<OwnershipCapability, OwnershipError> {
        self.with_owned_session_at(receipt.session_id, None, |session| {
            session.commit_ownership_transfer(receipt)
        })
    }

    /// Roll back only the staged transfer identified by this receipt.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the receipt does not match the current staged transfer.
    pub fn rollback_ownership_transfer(
        &mut self,
        receipt: &OwnershipReceipt,
    ) -> Result<(), OwnershipError> {
        self.with_owned_session_at(receipt.session_id, None, |session| {
            session.rollback_ownership_transfer(receipt)
        })
    }

    /// Preserve or reduce scope for the same owner without adding authority.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or a transfer is pending.
    pub fn attenuate_ownership_scope(
        &mut self,
        capability: &OwnershipCapability,
        new_scope: OwnershipScope,
    ) -> Result<OwnershipCapability, OwnershipError> {
        self.with_owned_session_at(capability.session_id, None, |session| {
            session.attenuate_ownership_scope(capability, new_scope)
        })
    }

    /// Apply session-local host mutation through the ownership gate.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or lacks full-session scope.
    pub fn apply_owned_session_mutation(
        &mut self,
        capability: &OwnershipCapability,
        mutation: SessionHostMutation,
    ) -> Result<(), OwnershipError> {
        self.with_owned_session_at(capability.session_id, None, |session| {
            session.apply_owned_session_mutation(capability, mutation)
        })
    }

    /// Issue a single-use readiness witness under the current owner capability.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the capability is stale or lacks full-session scope.
    pub fn issue_readiness_witness(
        &mut self,
        capability: &OwnershipCapability,
        predicate_ref: impl Into<String>,
    ) -> Result<ReadinessWitness, OwnershipError> {
        self.with_owned_session_at(capability.session_id, None, |session| {
            session.issue_readiness_witness(capability, predicate_ref)
        })
    }

    /// Consume a readiness witness exactly once under the same live owner capability.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the witness is stale, forged, mismatched, or already used.
    pub fn consume_readiness_witness(
        &mut self,
        capability: &OwnershipCapability,
        witness: &ReadinessWitness,
    ) -> Result<(), OwnershipError> {
        self.with_owned_session_at(capability.session_id, None, |session| {
            session.consume_readiness_witness(capability, witness)
        })
    }

    /// Mark the current owner as dead and fault the session.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the session is missing or owner mismatch occurs.
    pub fn mark_owner_died(
        &mut self,
        sid: SessionId,
        owner_id: &str,
    ) -> Result<CancellationWitness, OwnershipError> {
        self.with_owned_session_at(sid, None, |session| session.mark_owner_died(sid, owner_id))
    }

    /// Cancel a session because a staged transfer was abandoned.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the receipt does not match the staged transfer.
    pub fn cancel_abandoned_transfer(
        &mut self,
        receipt: &OwnershipReceipt,
    ) -> Result<CancellationWitness, OwnershipError> {
        self.with_owned_session_at(receipt.session_id, None, |session| {
            session.cancel_abandoned_transfer(receipt)
        })
    }

    /// Fault a session because a staged transfer could not commit.
    ///
    /// # Errors
    ///
    /// Returns an `OwnershipError` if the receipt does not match the staged transfer.
    pub fn fault_failed_transfer_commit(
        &mut self,
        receipt: &OwnershipReceipt,
        reason: impl Into<String>,
    ) -> Result<(), OwnershipError> {
        self.with_owned_session_at(receipt.session_id, None, |session| {
            session.fault_failed_transfer_commit(receipt, reason)
        })
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

    /// Remove exactly the selected session, preserving a compact terminal
    /// summary under the store's existing explicit archival policy.
    pub(crate) fn close_and_reap_required(
        &mut self,
        sid: SessionId,
    ) -> Result<ClosedSessionSummary, SessionDisposalError> {
        if let Some(summary) = self
            .archived_closed
            .iter()
            .find(|summary| summary.sid == sid)
        {
            return Ok(summary.clone());
        }
        let target = self
            .sessions
            .get(&sid)
            .ok_or(SessionDisposalError::MissingSession { session: sid })?;
        let already_terminal = matches!(
            target.status,
            SessionStatus::Closed | SessionStatus::Cancelled | SessionStatus::Faulted { .. }
        );
        let next_epoch = if already_terminal {
            target.epoch
        } else {
            target
                .epoch
                .checked_add(1)
                .ok_or(SessionDisposalError::EpochExhausted { session: sid })?
        };
        self.ensure_ownership_audit_history();
        let mut session = self
            .sessions
            .remove(&sid)
            .ok_or(SessionDisposalError::MissingSession { session: sid })?;
        if !already_terminal {
            session.status = SessionStatus::Closed;
        }
        session.epoch = next_epoch;
        let summary = ClosedSessionSummary::from_session(&session);
        self.archived_closed.push(summary.clone());
        Ok(summary)
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

            self.ensure_ownership_audit_history();
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
            .sum::<usize>()
            .saturating_add(
                self.ownership_audit_log
                    .iter()
                    .flatten()
                    .map(serialized_bytes)
                    .sum(),
            );

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
    pub(crate) fn set_default_handler_for_session(&mut self, sid: SessionId, handler: HandlerId) {
        if let Some(session) = self.sessions.get_mut(&sid) {
            let handler_id = session.intern_handler_binding(&handler);
            session.default_handler = handler;
            session.default_handler_id = Some(handler_id);
        }
    }

    /// Update edge-bound handler id.
    pub(crate) fn update_handler(&mut self, edge: &Edge, handler: HandlerId) {
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
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn update_trace(&mut self, edge: &Edge, trace: Vec<ValType>) {
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
pub(crate) fn unfold_if_var_with_scope(
    cont: &LocalTypeR,
    original: &LocalTypeR,
) -> (LocalTypeR, Option<LocalTypeR>) {
    match cont {
        LocalTypeR::Var(_) => (unfold_mu(original), None),
        LocalTypeR::Mu { .. } => (unfold_mu(cont), Some(cont.clone())),
        other => (other.clone(), None),
    }
}
