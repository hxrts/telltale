//! Session lifecycle and store.
//!
//! Matches the Lean `SessionState`, `SessionStore` from `lean/Runtime/VM/Model/State.lean`.
//! Local type state lives here — the session store is the single source
//! of truth for per-endpoint type advancement.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value as JsonValue;
use telltale_types::{LocalTypeR, ValType};

use crate::buffer::{BoundedBuffer, BufferConfig, SignedBuffer, SignedValue};
use crate::coroutine::Value;
use crate::instr::Endpoint;
use crate::verification::{
    signValue, signing_key_for_endpoint, verifySignedValue, verifying_key_for_endpoint, AuthTree,
    DefaultVerificationModel, Hash, HashTag, Signature, VerificationModel,
};

/// Archival summary for a closed session that has been reaped from live state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClosedSessionSummary {
    /// Session identifier.
    pub sid: SessionId,
    /// Terminal session status at reap time.
    pub status: SessionStatus,
    /// Number of participant roles.
    pub role_count: usize,
    /// Number of retained endpoint type entries at reap time.
    pub local_type_entries: usize,
    /// Number of directed edges tracked by the session.
    pub edge_count: usize,
    /// Number of edge-bound handlers.
    pub edge_handler_count: usize,
    /// Number of accumulated auth leaves across all edges.
    pub auth_leaf_count: usize,
    /// Number of auth trees retained by the session.
    pub auth_tree_count: usize,
    /// Number of auth roots retained by the session.
    pub auth_root_count: usize,
    /// Final epoch value.
    pub epoch: usize,
}

impl ClosedSessionSummary {
    fn from_session(session: &SessionState) -> Self {
        Self {
            sid: session.sid,
            status: session.status.clone(),
            role_count: session.roles.len(),
            local_type_entries: session.local_types.len(),
            edge_count: session.buffers.len(),
            edge_handler_count: session.edge_handlers.len(),
            auth_leaf_count: session.auth_leaves.values().map(Vec::len).sum(),
            auth_tree_count: session.auth_trees.len(),
            auth_root_count: session.auth_roots.len(),
            epoch: session.epoch,
        }
    }
}

/// Approximate retained state for the session store.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SessionStoreMemoryUsage {
    /// Number of live sessions still resident in the store.
    pub live_sessions: usize,
    /// Number of closed/cancelled/faulted sessions still resident in the store.
    pub live_closed_sessions: usize,
    /// Number of archived closed-session summaries retained after reaping.
    pub archived_closed_sessions: usize,
    /// Number of live endpoint type entries.
    pub live_local_type_entries: usize,
    /// Number of live directed buffers.
    pub live_buffer_count: usize,
    /// Number of live buffered messages.
    pub live_buffered_messages: usize,
    /// Number of live edge-bound handlers.
    pub live_edge_handler_count: usize,
    /// Number of live auth leaves across sessions.
    pub live_auth_leaf_count: usize,
    /// Number of live auth trees.
    pub live_auth_tree_count: usize,
    /// Number of live auth roots.
    pub live_auth_root_count: usize,
}

/// Session identifier. Each session gets a unique ID within the VM.
pub type SessionId = usize;

/// Handler identifier for edge-bound runtime dispatch.
pub type HandlerId = String;

/// Built-in fallback handler id used when no edge-specific binding exists.
pub const DEFAULT_HANDLER_ID: &str = "default_handler";

fn default_handler_id() -> HandlerId {
    DEFAULT_HANDLER_ID.to_string()
}

/// Edge between two roles in a session (directed: sender → receiver).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Edge {
    /// Session scope for this edge.
    pub sid: SessionId,
    /// Sender role name.
    pub sender: String,
    /// Receiver role name.
    pub receiver: String,
}

impl Edge {
    /// Construct a sid-qualified edge.
    #[must_use]
    pub fn new(sid: SessionId, sender: impl Into<String>, receiver: impl Into<String>) -> Self {
        Self {
            sid,
            sender: sender.into(),
            receiver: receiver.into(),
        }
    }
}

#[derive(Debug, Deserialize)]
struct EdgeJson {
    sid: Option<SessionId>,
    sender: String,
    receiver: String,
}

/// Decode an edge from JSON.
///
/// # Errors
///
/// Returns an error when fields are missing.
pub fn decode_edge_json(
    value: &JsonValue,
    session_hint: Option<SessionId>,
) -> Result<Edge, String> {
    let raw: EdgeJson =
        serde_json::from_value(value.clone()).map_err(|e| format!("invalid edge json: {e}"))?;

    let sid = raw
        .sid
        .or(session_hint)
        .ok_or_else(|| "missing sid in edge json".to_string())?;
    Ok(Edge::new(sid, raw.sender, raw.receiver))
}

/// Session status.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SessionStatus {
    /// Session is active and processing messages.
    Active,
    /// Session is draining buffered messages before close.
    Draining,
    /// Session is closed normally.
    Closed,
    /// Session was cancelled.
    Cancelled,
    /// Session faulted.
    Faulted {
        /// Reason for the fault.
        reason: String,
    },
}

/// Per-endpoint type tracking: current state + original for unfolding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeEntry {
    /// Current local type (advances with each completed instruction).
    pub current: LocalTypeR,
    /// Original local type (for unfolding recursive variables).
    pub original: LocalTypeR,
}

/// State of a single session.
///
/// Stores per-endpoint local types (the type truth), message buffers,
/// and lifecycle status. Matches Lean `SessionState`.
#[derive(Debug, Serialize, Deserialize)]
pub struct SessionState {
    /// Session identifier.
    pub sid: SessionId,
    /// Role names in this session.
    pub roles: Vec<String>,
    /// Deterministic internal ids for participant roles.
    #[serde(default)]
    role_ids: BTreeMap<String, u16>,
    /// Per-endpoint local type state. This IS the type truth.
    ///
    /// Matches Lean `localTypes : List (Endpoint × LocalType)`.
    pub local_types: BTreeMap<Endpoint, TypeEntry>,
    /// Message buffers keyed by directed edge.
    pub buffers: BTreeMap<Edge, SignedBuffer<Signature>>,
    /// Deterministic internal edge lookup keyed by interned role ids.
    #[serde(default)]
    edge_lookup: BTreeMap<(u16, u16), Edge>,
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

    pub(crate) fn build_edge_lookup(
        sid: SessionId,
        roles: &[String],
        role_ids: &BTreeMap<String, u16>,
    ) -> BTreeMap<(u16, u16), Edge> {
        let edge_capacity = roles.len().saturating_mul(roles.len().saturating_sub(1));
        let mut edges = Vec::with_capacity(edge_capacity);
        for from in roles {
            for to in roles {
                if from == to {
                    continue;
                }
                let from_id = *role_ids
                    .get(from)
                    .expect("sender role id must exist for edge table");
                let to_id = *role_ids
                    .get(to)
                    .expect("receiver role id must exist for edge table");
                edges.push(((from_id, to_id), Edge::new(sid, from.clone(), to.clone())));
            }
        }
        edges.into_iter().collect()
    }

    fn edge_for_roles(&self, from: &str, to: &str) -> Option<&Edge> {
        let from_id = self.role_ids.get(from)?;
        let to_id = self.role_ids.get(to)?;
        self.edge_lookup.get(&(*from_id, *to_id))
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
        self.buffers.get(&edge).is_some_and(|buf| !buf.is_empty())
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
    pub fn open_with_sid(
        &mut self,
        sid: SessionId,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> SessionId {
        let role_count = roles.len();
        let role_ids = SessionState::build_role_ids(&roles);
        // Build per-endpoint local types with initial unfolding.
        let mut local_type_entries = Vec::with_capacity(role_count);
        for role in &roles {
            if let Some(lt) = initial_types.get(role) {
                let ep = Endpoint {
                    sid,
                    role: role.clone(),
                };
                local_type_entries.push((
                    ep,
                    TypeEntry {
                        current: unfold_mu(lt),
                        original: lt.clone(),
                    },
                ));
            }
        }
        let local_types = local_type_entries.into_iter().collect();

        // Create buffers for each directed edge.
        let edge_lookup = SessionState::build_edge_lookup(sid, &roles, &role_ids);
        let edge_capacity = role_count.saturating_mul(role_count.saturating_sub(1));
        let mut buffer_entries = Vec::with_capacity(edge_capacity);
        for edge in edge_lookup.values() {
            buffer_entries.push((edge.clone(), BoundedBuffer::new(buffer_config)));
        }
        let buffers = buffer_entries.into_iter().collect();

        let state = SessionState {
            sid,
            roles,
            role_ids,
            local_types,
            buffers,
            edge_lookup,
            auth_leaves: BTreeMap::new(),
            auth_trees: BTreeMap::new(),
            auth_roots: BTreeMap::new(),
            edge_handlers: BTreeMap::new(),
            default_handler: default_handler_id(),
            edge_traces: BTreeMap::new(),
            status: SessionStatus::Active,
            epoch: 0,
        };

        self.sessions.insert(sid, state);
        self.next_id = self.next_id.max(sid.saturating_add(1));
        sid
    }

    /// Open a new session with the given roles, buffer config, and initial local types.
    ///
    /// Returns the session ID. Endpoints are constructed as `Endpoint { sid, role }`.
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
        }

        usage
    }

    /// Lookup edge-bound handler id.
    #[must_use]
    pub fn lookup_handler(&self, edge: &Edge) -> Option<&HandlerId> {
        self.sessions.get(&edge.sid)?.edge_handlers.get(edge)
    }

    /// Lookup a default handler id for a session.
    #[must_use]
    pub fn default_handler_for_session(&self, sid: SessionId) -> Option<&HandlerId> {
        Some(&self.sessions.get(&sid)?.default_handler)
    }

    /// Set the default handler id for a session.
    pub fn set_default_handler_for_session(&mut self, sid: SessionId, handler: HandlerId) {
        if let Some(session) = self.sessions.get_mut(&sid) {
            session.default_handler = handler;
        }
    }

    /// Update edge-bound handler id.
    pub fn update_handler(&mut self, edge: &Edge, handler: HandlerId) {
        if let Some(session) = self.sessions.get_mut(&edge.sid) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use telltale_types::Label;

    fn default_types() -> BTreeMap<String, LocalTypeR> {
        let mut m = BTreeMap::new();
        m.insert(
            "A".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Send {
                    partner: "B".into(),
                    branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                },
            ),
        );
        m.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Recv {
                    partner: "A".into(),
                    branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                },
            ),
        );
        m
    }

    #[test]
    fn test_session_open_with_types() {
        let mut store = SessionStore::new();
        let types = default_types();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &types,
        );

        let ep_a = Endpoint {
            sid,
            role: "A".into(),
        };
        let ep_b = Endpoint {
            sid,
            role: "B".into(),
        };

        // Types should be unfolded (mu stripped).
        assert!(matches!(
            store.lookup_type(&ep_a),
            Some(LocalTypeR::Send { .. })
        ));
        assert!(matches!(
            store.lookup_type(&ep_b),
            Some(LocalTypeR::Recv { .. })
        ));
    }

    #[test]
    fn test_type_advance_and_unfold() {
        let mut store = SessionStore::new();
        let types = default_types();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &types,
        );

        let ep_a = Endpoint {
            sid,
            role: "A".into(),
        };

        // Get current type: Send { ... Var("step") }
        let lt = store.lookup_type(&ep_a).unwrap().clone();
        let (_, _vt, continuation) = match &lt {
            LocalTypeR::Send { branches, .. } => branches.first().unwrap().clone(),
            _ => panic!("expected Send"),
        };

        // Continuation is Var("step") — resolve it.
        let original = store.original_type(&ep_a).unwrap();
        let resolved = unfold_if_var(&continuation, original);
        assert!(matches!(resolved, LocalTypeR::Send { .. }));

        // Advance type.
        store.update_type(&ep_a, resolved);
        assert!(matches!(
            store.lookup_type(&ep_a),
            Some(LocalTypeR::Send { .. })
        ));
    }

    #[test]
    fn test_session_send_recv() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );

        let session = store.get_mut(sid).unwrap();
        session.send("A", "B", Value::Nat(42)).unwrap();
        assert!(session.has_message("A", "B"));
        assert!(!session.has_message("B", "A"));

        let val = session.recv("A", "B");
        assert_eq!(val, Some(Value::Nat(42)));
    }

    #[test]
    fn test_close_clears_buffers_and_traces_even_when_messages_pending() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );
        let edge = Edge::new(sid, "A", "B");
        store
            .get_mut(sid)
            .expect("session exists")
            .send("A", "B", Value::Nat(7))
            .expect("enqueue pending message");
        store.update_trace(&edge, vec![ValType::Nat]);

        store.close(sid).expect("close session");
        let session = store.get(sid).expect("session exists after close");
        assert_eq!(session.status, SessionStatus::Closed);
        assert!(session.buffers.is_empty());
        assert!(session.edge_traces.is_empty());
    }

    #[test]
    fn test_reap_closed_archives_and_removes_session() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );

        store.close(sid).expect("close session");
        let summaries = store.reap_closed();

        assert_eq!(summaries.len(), 1);
        assert_eq!(summaries[0].sid, sid);
        assert!(store.get(sid).is_none());
        assert_eq!(store.archived_closed().len(), 1);
    }

    #[test]
    fn test_memory_usage_tracks_live_and_archived_closed_sessions() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );

        let before_close = store.memory_usage();
        assert_eq!(before_close.live_sessions, 1);
        assert_eq!(before_close.live_closed_sessions, 0);

        store.close(sid).expect("close session");
        let after_close = store.memory_usage();
        assert_eq!(after_close.live_sessions, 1);
        assert_eq!(after_close.live_closed_sessions, 1);

        store.reap_closed();
        let after_reap = store.memory_usage();
        assert_eq!(after_reap.live_sessions, 0);
        assert_eq!(after_reap.live_closed_sessions, 0);
        assert_eq!(after_reap.archived_closed_sessions, 1);
    }

    #[test]
    fn test_session_state_roundtrip_preserves_internal_role_edge_indexes() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into(), "C".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );

        let session = store.get_mut(sid).expect("session exists");
        session
            .send("A", "B", Value::Nat(7))
            .expect("send should succeed");

        let encoded = serde_json::to_string(session).expect("serialize session");
        let mut decoded: SessionState = serde_json::from_str(&encoded).expect("deserialize");

        assert!(decoded.has_message("A", "B"));
        assert_eq!(decoded.recv("A", "B"), Some(Value::Nat(7)));
        assert!(!decoded.has_message("A", "B"));
    }

    #[test]
    fn test_namespace_isolation() {
        let mut store = SessionStore::new();
        let sid1 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );
        let sid2 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );

        assert_ne!(sid1, sid2);

        store
            .get_mut(sid1)
            .unwrap()
            .send("A", "B", Value::Nat(1))
            .unwrap();
        assert!(!store.get(sid2).unwrap().has_message("A", "B"));
    }

    #[test]
    fn test_remove_type() {
        let mut store = SessionStore::new();
        let types = default_types();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &types,
        );

        let ep_a = Endpoint {
            sid,
            role: "A".into(),
        };
        assert!(store.lookup_type(&ep_a).is_some());

        store.remove_type(&ep_a);
        assert!(store.lookup_type(&ep_a).is_none());
    }

    #[test]
    fn test_cross_session_role_name_edge_collision_regression() {
        let mut store = SessionStore::new();
        let sid1 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );
        let sid2 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );

        let e1 = Edge::new(sid1, "A", "B");
        let e2 = Edge::new(sid2, "A", "B");
        assert_ne!(e1, e2, "edges from distinct sessions must not collide");
        assert!(store
            .get(sid1)
            .expect("sid1 exists")
            .buffers
            .contains_key(&e1));
        assert!(store
            .get(sid2)
            .expect("sid2 exists")
            .buffers
            .contains_key(&e2));
    }

    #[test]
    fn test_edge_handler_and_trace_bindings() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &BTreeMap::new(),
        );
        let edge = Edge::new(sid, "A", "B");

        assert!(store.lookup_handler(&edge).is_none());
        store.update_handler(&edge, "handler/send".to_string());
        assert_eq!(
            store.lookup_handler(&edge).map(String::as_str),
            Some("handler/send")
        );

        assert!(store.lookup_trace(&edge).is_none());
        store.update_trace(&edge, vec![ValType::Nat]);
        assert_eq!(store.lookup_trace(&edge), Some([ValType::Nat].as_slice()));
    }

    #[test]
    fn test_decode_edge_json_requires_sid_sender_receiver() {
        let sid_qualified = json!({
            "sid": 7,
            "sender": "A",
            "receiver": "B"
        });
        let e = decode_edge_json(&sid_qualified, None).expect("decode sid-qualified edge");
        assert_eq!(e, Edge::new(7, "A", "B"));

        let no_sid = json!({
            "sender": "A",
            "receiver": "B"
        });
        let e2 = decode_edge_json(&no_sid, Some(11)).expect("decode edge with sid hint");
        assert_eq!(e2, Edge::new(11, "A", "B"));

        let legacy = json!({
            "from": "A",
            "to": "B",
            "sid": 11
        });
        let err = decode_edge_json(&legacy, None).expect_err("legacy edge shape must be rejected");
        assert!(err.contains("invalid edge json"), "unexpected error: {err}");
    }
}
