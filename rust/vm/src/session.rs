//! Session lifecycle and store.
//!
//! Matches the Lean `SessionState`, `SessionStore` from `runtime.md §7`.
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

/// Session identifier. Each session gets a unique ID within the VM.
pub type SessionId = usize;

/// Handler identifier for edge-bound runtime dispatch.
pub type HandlerId = String;

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
    /// Per-endpoint local type state. This IS the type truth.
    ///
    /// Matches Lean `localTypes : List (Endpoint × LocalType)`.
    pub local_types: BTreeMap<Endpoint, TypeEntry>,
    /// Message buffers keyed by directed edge.
    pub buffers: BTreeMap<Edge, SignedBuffer<Signature>>,
    /// Per-edge authenticated leaves for Merkle-auth tracking.
    pub auth_leaves: BTreeMap<Edge, Vec<Hash>>,
    /// Per-edge Merkle roots for signed-buffer history.
    pub auth_roots: BTreeMap<Edge, Hash>,
    /// Optional handler binding per edge.
    pub edge_handlers: BTreeMap<Edge, HandlerId>,
    /// Coherence trace by edge.
    pub edge_traces: BTreeMap<Edge, Vec<ValType>>,
    /// Current status.
    pub status: SessionStatus,
    /// Epoch counter for draining.
    pub epoch: usize,
}

impl SessionState {
    fn update_auth_tree(&mut self, edge: &Edge, signed: &SignedValue<Signature>) {
        let bytes = serde_json::to_vec(signed).unwrap_or_default();
        let leaf = DefaultVerificationModel::hash(HashTag::MerkleLeaf, &bytes);
        let leaves = self.auth_leaves.entry(edge.clone()).or_default();
        leaves.push(leaf);
        let tree = AuthTree::new(leaves.clone());
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
        signed: SignedValue<Signature>,
    ) -> Result<crate::buffer::EnqueueResult, String> {
        let edge = Edge::new(self.sid, from, to);
        let buf = self
            .buffers
            .get_mut(&edge)
            .ok_or_else(|| format!("no buffer for edge {from} → {to}"))?;
        let result = buf.enqueue(signed.clone());
        if matches!(result, crate::buffer::EnqueueResult::Ok) {
            self.update_auth_tree(&edge, &signed);
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
            SignedValue {
                payload: val,
                signature,
            },
        )
    }

    /// Receive a signed value destined for a role from a specific sender.
    pub fn recv_signed(&mut self, from: &str, to: &str) -> Option<SignedValue<Signature>> {
        let edge = Edge::new(self.sid, from, to);
        self.buffers.get_mut(&edge).and_then(|buf| buf.dequeue())
    }

    /// Receive and verify a value destined for a role from a specific sender.
    ///
    /// # Errors
    ///
    /// Returns an error if signature verification fails.
    pub fn recv_verified(&mut self, from: &str, to: &str) -> Result<Option<Value>, String> {
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
        Ok(Some(signed.payload))
    }

    /// Receive a value destined for a role from a specific sender.
    pub fn recv(&mut self, from: &str, to: &str) -> Option<Value> {
        self.recv_verified(from, to).ok().flatten()
    }

    /// Check if there is a message available on an edge.
    #[must_use]
    pub fn has_message(&self, from: &str, to: &str) -> bool {
        let edge = Edge::new(self.sid, from, to);
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
    /// This is used by VM state machines that own `next_session_id`.
    pub fn open_with_sid(
        &mut self,
        sid: SessionId,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> SessionId {
        // Build per-endpoint local types with initial unfolding.
        let mut local_types = BTreeMap::new();
        for role in &roles {
            if let Some(lt) = initial_types.get(role) {
                let ep = Endpoint {
                    sid,
                    role: role.clone(),
                };
                local_types.insert(
                    ep,
                    TypeEntry {
                        current: unfold_mu(lt),
                        original: lt.clone(),
                    },
                );
            }
        }

        // Create buffers for each directed edge.
        let mut buffers = BTreeMap::new();
        for from in &roles {
            for to in &roles {
                if from != to {
                    let edge = Edge::new(sid, from.clone(), to.clone());
                    buffers.insert(edge, BoundedBuffer::new(buffer_config));
                }
            }
        }

        let state = SessionState {
            sid,
            roles,
            local_types,
            buffers,
            auth_leaves: BTreeMap::new(),
            auth_roots: BTreeMap::new(),
            edge_handlers: BTreeMap::new(),
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

    /// Number of active sessions.
    #[must_use]
    pub fn active_count(&self) -> usize {
        self.sessions
            .values()
            .filter(|s| s.status == SessionStatus::Active)
            .count()
    }

    /// All session IDs.
    #[must_use]
    pub fn session_ids(&self) -> Vec<SessionId> {
        self.sessions.keys().copied().collect()
    }

    /// Lookup edge-bound handler id.
    #[must_use]
    pub fn lookup_handler(&self, edge: &Edge) -> Option<&HandlerId> {
        self.sessions.get(&edge.sid)?.edge_handlers.get(edge)
    }

    /// Lookup a default handler id for a session, if any edge binding exists.
    #[must_use]
    pub fn default_handler_for_session(&self, sid: SessionId) -> Option<&HandlerId> {
        self.sessions.get(&sid)?.edge_handlers.values().next()
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
