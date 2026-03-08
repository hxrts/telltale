// Session lifecycle and store.
//
// Matches the Lean `SessionState`, `SessionStore` from `lean/Runtime/VM/Model/State.lean`.
// Local type state lives here — the session store is the single source
// of truth for per-endpoint type advancement.

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
    ///
    /// # Panics
    ///
    /// Panics if an internally assigned role id does not map back into the
    /// canonical `roles` slice while constructing the edge blueprint.
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
type EdgeKey = (u16, u16);
type LocalBranches<'a> = &'a [(Label, Option<ValType>, LocalTypeR)];
type HandlerIndexBuild = (
    BTreeMap<HandlerId, HandlerNumericId>,
    Vec<HandlerId>,
    BTreeMap<EdgeKey, HandlerNumericId>,
    Option<HandlerNumericId>,
);

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
