//! Session lifecycle and store.
//!
//! Matches the Lean `SessionState`, `SessionStore` from `lean/Runtime/VM/Model/State.lean`.
//! Local type state lives here — the session store is the single source
//! of truth for per-endpoint type advancement.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use serde_json::Value as JsonValue;
use telltale_types::{Label, LocalTypeR, ValType};

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

    fn retained_bytes_estimate(&self) -> usize {
        std::mem::size_of::<Self>().saturating_add(serialized_bytes(self))
    }
}

/// Reusable session-open layout derived from a fixed role topology and local types.
#[derive(Debug, Clone)]
pub struct SessionOpenPlan {
    pub(crate) roles: Vec<String>,
    pub(crate) role_ids: BTreeMap<String, u16>,
    pub(crate) initial_types: Vec<(String, LocalTypeR, LocalTypeR)>,
    pub(crate) edge_blueprint: Vec<((u16, u16), String, String)>,
    pub(crate) active_branch_roles: Vec<String>,
}

impl SessionOpenPlan {
    fn collect_protocol_edges(
        role: &str,
        local_type: &LocalTypeR,
        role_ids: &BTreeMap<String, u16>,
        edges: &mut BTreeSet<(u16, u16)>,
    ) {
        match local_type {
            LocalTypeR::End | LocalTypeR::Var(_) => {}
            LocalTypeR::Mu { body, .. } => {
                Self::collect_protocol_edges(role, body, role_ids, edges);
            }
            LocalTypeR::Send { partner, branches } => {
                if let (Some(from_id), Some(to_id)) = (role_ids.get(role), role_ids.get(partner)) {
                    if from_id != to_id {
                        edges.insert((*from_id, *to_id));
                    }
                }
                for (_, _, continuation) in branches {
                    Self::collect_protocol_edges(role, continuation, role_ids, edges);
                }
            }
            LocalTypeR::Recv { partner, branches } => {
                if let (Some(from_id), Some(to_id)) = (role_ids.get(partner), role_ids.get(role)) {
                    if from_id != to_id {
                        edges.insert((*from_id, *to_id));
                    }
                }
                for (_, _, continuation) in branches {
                    Self::collect_protocol_edges(role, continuation, role_ids, edges);
                }
            }
        }
    }

    /// Build a reusable open plan from a role list and initial local types.
    #[must_use]
    pub fn new(roles: &[String], initial_types: &BTreeMap<String, LocalTypeR>) -> Self {
        let role_ids = SessionState::build_role_ids(roles);
        let mut planned_types = Vec::with_capacity(roles.len());
        let mut active_branch_roles = Vec::new();
        for role in roles {
            if let Some(original) = initial_types.get(role) {
                let current = unfold_mu(original);
                if SessionState::branch_shape(&current).is_some() {
                    active_branch_roles.push(role.clone());
                }
                planned_types.push((role.clone(), current, original.clone()));
            }
        }

        let mut protocol_edges = BTreeSet::new();
        for role in roles {
            if let Some(original) = initial_types.get(role) {
                Self::collect_protocol_edges(role, original, &role_ids, &mut protocol_edges);
            }
        }
        let mut edge_blueprint = Vec::with_capacity(protocol_edges.len());
        for (from_id, to_id) in protocol_edges {
            let from = roles
                .get(usize::from(from_id))
                .expect("sender role id must index the session-open role set")
                .clone();
            let to = roles
                .get(usize::from(to_id))
                .expect("receiver role id must index the session-open role set")
                .clone();
            edge_blueprint.push(((from_id, to_id), from, to));
        }

        Self {
            roles: roles.to_vec(),
            role_ids,
            initial_types: planned_types,
            edge_blueprint,
            active_branch_roles,
        }
    }

    /// Canonical role ordering for this plan.
    #[must_use]
    pub fn roles(&self) -> &[String] {
        &self.roles
    }

    /// Directed protocol edges needed by this session.
    #[must_use]
    pub fn edge_blueprint(&self) -> &[((u16, u16), String, String)] {
        &self.edge_blueprint
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
    /// Estimated retained bytes by session-store subsystem.
    pub retained_bytes: SessionStoreRetainedBytes,
}

/// Estimated retained bytes for session-store subsystems.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SessionStoreRetainedBytes {
    /// Live session metadata excluding dedicated subsystems below.
    pub live_sessions: usize,
    /// Archived closed-session summaries.
    pub archived_closed: usize,
    /// Local type storage and endpoint bindings.
    pub local_types: usize,
    /// Buffer storage and buffered payloads.
    pub buffers: usize,
    /// Edge-trace storage.
    pub traces: usize,
    /// Auth leaves, trees, and roots.
    pub auth: usize,
    /// Handler bindings and defaults.
    pub handlers: usize,
    /// Aggregate retained bytes across all session-store subsystems.
    pub total: usize,
}

/// Session identifier. Each session gets a unique ID within the VM.
pub type SessionId = usize;

/// Handler identifier for edge-bound runtime dispatch.
pub type HandlerId = String;
type HandlerNumericId = u16;
type LabelNumericId = u16;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum BranchDirection {
    Send,
    Recv,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CachedBranch {
    pub(crate) direction: BranchDirection,
    pub(crate) partner: String,
    pub(crate) expected_type: Option<ValType>,
    pub(crate) continuation: LocalTypeR,
}

/// Built-in fallback handler id used when no edge-specific binding exists.
pub const DEFAULT_HANDLER_ID: &str = "default_handler";

fn default_handler_id() -> HandlerId {
    DEFAULT_HANDLER_ID.to_string()
}

fn serialized_bytes<T: Serialize>(value: &T) -> usize {
    bincode::serialized_size(value)
        .ok()
        .and_then(|bytes| usize::try_from(bytes).ok())
        .unwrap_or(0)
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
        let (handler_ids, handlers_by_id, edge_handler_lookup, default_handler_id) =
            Self::build_handler_indexes(&self.role_ids, &self.default_handler, &self.edge_handlers);
        self.handler_ids = handler_ids;
        self.handlers_by_id = handlers_by_id;
        self.edge_handler_lookup = edge_handler_lookup;
        self.default_handler_id = default_handler_id;
        self.label_ids = BTreeMap::new();
        self.labels_by_id = Vec::new();
        self.branch_lookup = BTreeMap::new();
        let endpoints: Vec<Endpoint> = self.local_types.keys().cloned().collect();
        for endpoint in endpoints {
            self.refresh_endpoint_branch_lookup(&endpoint);
        }
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
    ) -> BTreeMap<(u16, u16), Edge> {
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
    ) -> (
        BTreeMap<HandlerId, HandlerNumericId>,
        Vec<HandlerId>,
        BTreeMap<(u16, u16), HandlerNumericId>,
        Option<HandlerNumericId>,
    ) {
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

    fn branch_shape(
        local_type: &LocalTypeR,
    ) -> Option<(
        BranchDirection,
        &str,
        &[(Label, Option<ValType>, LocalTypeR)],
    )> {
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
        self.buffers.get(&edge).is_some_and(|buf| !buf.is_empty())
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
            SessionState::build_handler_indexes(&plan.role_ids, &default_handler, &BTreeMap::new());

        let mut state = SessionState {
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

    fn single_send_recv_types() -> BTreeMap<String, LocalTypeR> {
        let mut types = BTreeMap::new();
        types.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
        );
        types.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End),
        );
        types
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
    fn test_branch_lookup_tracks_type_updates_and_removals() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &default_types(),
        );
        let ep_a = Endpoint {
            sid,
            role: "A".into(),
        };

        let initial = store
            .get(sid)
            .expect("session exists")
            .lookup_branch_resolution(&ep_a, "msg")
            .expect("initial branch must be cached");
        assert_eq!(initial.direction, BranchDirection::Send);
        assert_eq!(initial.partner, "B");
        assert_eq!(initial.expected_type, None);

        store.update_type(
            &ep_a,
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("alt"), Some(ValType::Nat), LocalTypeR::End)],
            },
        );

        let updated_session = store.get(sid).expect("session exists after type update");
        assert!(updated_session
            .lookup_branch_resolution(&ep_a, "msg")
            .is_none());
        let updated = updated_session
            .lookup_branch_resolution(&ep_a, "alt")
            .expect("updated branch must be cached");
        assert_eq!(updated.direction, BranchDirection::Send);
        assert_eq!(updated.partner, "B");
        assert_eq!(updated.expected_type, Some(ValType::Nat));

        store.remove_type(&ep_a);
        assert!(store
            .get(sid)
            .expect("session exists after remove")
            .lookup_branch_resolution(&ep_a, "alt")
            .is_none());
    }

    #[test]
    fn test_session_send_recv() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
        );

        let session = store.get_mut(sid).unwrap();
        session.send("A", "B", Value::Nat(42)).unwrap();
        assert!(session.has_message("A", "B"));
        assert!(!session.has_message("B", "A"));

        let val = session.recv("A", "B");
        assert_eq!(val, Some(Value::Nat(42)));
    }

    #[test]
    fn test_open_allocates_only_protocol_reachable_edges() {
        let mut types = BTreeMap::new();
        types.insert(
            "A".to_string(),
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
        );
        types.insert(
            "B".to_string(),
            LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End),
        );
        types.insert("C".to_string(), LocalTypeR::End);

        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into(), "C".into()],
            &BufferConfig::default(),
            &types,
        );

        let session = store.get_mut(sid).expect("session exists");
        assert_eq!(session.buffers.len(), 1);
        assert!(session.buffers.contains_key(&Edge::new(sid, "A", "B")));
        assert!(session.send("A", "B", Value::Nat(42)).is_ok());
        assert!(session.has_message("A", "B"));
        assert_eq!(session.recv("A", "B"), Some(Value::Nat(42)));
        assert_eq!(
            session.send("B", "A", Value::Nat(7)).unwrap_err(),
            "no buffer for edge B → A"
        );
        assert_eq!(
            session.send("A", "C", Value::Nat(9)).unwrap_err(),
            "no buffer for edge A → C"
        );
    }

    #[test]
    fn test_close_clears_buffers_and_traces_even_when_messages_pending() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
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
        assert!(before_close.retained_bytes.total > 0);
        assert!(before_close.retained_bytes.live_sessions > 0);
        assert!(before_close.retained_bytes.buffers > 0);

        store.close(sid).expect("close session");
        let after_close = store.memory_usage();
        assert_eq!(after_close.live_sessions, 1);
        assert_eq!(after_close.live_closed_sessions, 1);
        assert!(after_close.retained_bytes.total > 0);

        store.reap_closed();
        let after_reap = store.memory_usage();
        assert_eq!(after_reap.live_sessions, 0);
        assert_eq!(after_reap.live_closed_sessions, 0);
        assert_eq!(after_reap.archived_closed_sessions, 1);
        assert_eq!(after_reap.retained_bytes.live_sessions, 0);
        assert_eq!(after_reap.retained_bytes.local_types, 0);
        assert_eq!(after_reap.retained_bytes.buffers, 0);
        assert!(after_reap.retained_bytes.archived_closed > 0);
    }

    #[test]
    fn test_session_state_roundtrip_preserves_internal_role_edge_indexes() {
        let mut store = SessionStore::new();
        let sid = store.open(
            vec!["A".into(), "B".into(), "C".into()],
            &BufferConfig::default(),
            &{
                let mut types = single_send_recv_types();
                types.insert("C".to_string(), LocalTypeR::End);
                types
            },
        );

        let session = store.get_mut(sid).expect("session exists");
        session.default_handler = "handler/default".to_string();
        session
            .edge_handlers
            .insert(Edge::new(sid, "A", "B"), "handler/ab".to_string());
        session.rebuild_derived_indexes();
        session
            .send("A", "B", Value::Nat(7))
            .expect("send should succeed");

        let encoded = bincode::serialize(session).expect("serialize session");
        let mut decoded: SessionState = bincode::deserialize(&encoded).expect("deserialize");

        assert_eq!(
            decoded.default_handler_binding().map(String::as_str),
            Some("handler/default")
        );
        assert_eq!(
            decoded
                .lookup_handler_for_roles("A", "B")
                .map(String::as_str),
            Some("handler/ab")
        );
        assert!(decoded.has_bound_handler());
        assert!(decoded
            .lookup_branch_resolution(
                &Endpoint {
                    sid,
                    role: "A".into()
                },
                "msg"
            )
            .is_some());
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
            &single_send_recv_types(),
        );
        let sid2 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
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
            &single_send_recv_types(),
        );
        let sid2 = store.open(
            vec!["A".into(), "B".into()],
            &BufferConfig::default(),
            &single_send_recv_types(),
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
        assert_eq!(
            store.default_handler_for_session(sid).map(String::as_str),
            Some(DEFAULT_HANDLER_ID)
        );
        store.update_handler(&edge, "handler/send".to_string());
        assert_eq!(
            store.lookup_handler(&edge).map(String::as_str),
            Some("handler/send")
        );
        store.set_default_handler_for_session(sid, "handler/default".to_string());
        assert_eq!(
            store.default_handler_for_session(sid).map(String::as_str),
            Some("handler/default")
        );
        assert!(
            store.get(sid).expect("session exists").has_bound_handler(),
            "internal handler ids must remain populated after updates"
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
