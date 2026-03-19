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

/// Stable host/runtime owner identifier for one session capability.
pub type FragmentOwnerId = String;

/// Ownership generation/epoch used to reject stale capabilities.
pub type OwnershipEpoch = u64;

/// Identifier for one staged ownership operation.
pub type OwnershipClaimId = u64;

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
    crate::serialization::binary_size(value)
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

/// Current authority carried by a live ownership capability.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OwnershipScope {
    /// Full-session authority.
    Session,
    /// Fragment/boundary-scoped authority.
    Fragments(BTreeSet<String>),
}

impl OwnershipScope {
    /// Whether this scope authorizes full-session host mutation.
    #[must_use]
    pub fn allows_session_mutation(&self) -> bool {
        matches!(self, Self::Session)
    }
}

/// Capability proving the caller is the current owner for one session.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OwnershipCapability {
    /// Session covered by this capability.
    pub session_id: SessionId,
    /// Stable owner label.
    pub owner_id: FragmentOwnerId,
    /// Current ownership generation.
    pub generation: OwnershipEpoch,
    /// Authorized scope for this capability.
    pub scope: OwnershipScope,
}

/// Receipt for an in-progress ownership transfer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OwnershipReceipt {
    /// Session covered by the transfer.
    pub session_id: SessionId,
    /// Unique staged-claim identifier.
    pub claim_id: OwnershipClaimId,
    /// Previous owner label.
    pub from_owner_id: FragmentOwnerId,
    /// Previous owner generation.
    pub from_generation: OwnershipEpoch,
    /// Target owner label.
    pub to_owner_id: FragmentOwnerId,
    /// Generation that will become current on commit.
    pub to_generation: OwnershipEpoch,
    /// Scope granted if the transfer commits.
    pub scope: OwnershipScope,
}

/// Terminal reason recorded when ownership fails closed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OwnershipTerminalReason {
    /// Current owner died or was abandoned by the host.
    OwnerDied {
        /// Owner that died.
        owner_id: FragmentOwnerId,
    },
    /// Transfer was abandoned before commit.
    TransferAbandoned {
        /// Owner that abandoned the staged transfer.
        owner_id: FragmentOwnerId,
        /// Claim/receipt identifier for the abandoned transfer.
        claim_id: OwnershipClaimId,
    },
    /// Transfer commit failed after staging.
    TransferCommitFailed {
        /// Owner whose staged transfer failed.
        owner_id: FragmentOwnerId,
        /// Claim/receipt identifier for the failed transfer.
        claim_id: OwnershipClaimId,
        /// Human-readable commit failure reason.
        reason: String,
    },
}

/// Errors surfaced by the runtime ownership contract.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OwnershipError {
    /// Session was not found.
    SessionNotFound {
        /// Session that was not found.
        session_id: SessionId,
    },
    /// Session already has a current owner.
    AlreadyClaimed {
        /// Session that was already claimed.
        session_id: SessionId,
        /// Owner that already holds the claim.
        current_owner_id: FragmentOwnerId,
    },
    /// Session does not currently have an owner.
    Unclaimed {
        /// Session that does not currently have an owner.
        session_id: SessionId,
    },
    /// Capability generation or owner no longer matches live state.
    StaleCapability {
        /// Session whose live ownership state rejected the capability.
        session_id: SessionId,
        /// Owner label carried by the stale capability.
        owner_id: FragmentOwnerId,
        /// Generation expected by the caller.
        expected_generation: OwnershipEpoch,
        /// Generation currently live in the session store.
        actual_generation: OwnershipEpoch,
    },
    /// Capability scope is too weak for the attempted operation.
    ScopeViolation {
        /// Session whose scope check failed.
        session_id: SessionId,
        /// Owner label that attempted the operation.
        owner_id: FragmentOwnerId,
        /// Minimum scope required for the operation.
        required: OwnershipScope,
        /// Actual live scope carried by the capability.
        actual: OwnershipScope,
    },
    /// Another staged ownership transfer already exists.
    TransferPending {
        /// Session with an existing staged transfer.
        session_id: SessionId,
        /// Identifier of the staged transfer.
        claim_id: OwnershipClaimId,
    },
    /// No staged ownership transfer exists.
    TransferNotPending {
        /// Session with no staged transfer.
        session_id: SessionId,
    },
    /// Transfer receipt does not match live staged state.
    ReceiptMismatch {
        /// Session whose staged transfer did not match the receipt.
        session_id: SessionId,
        /// Identifier carried by the mismatched receipt.
        claim_id: OwnershipClaimId,
    },
    /// Ownership already terminated for this session.
    Terminal {
        /// Session whose ownership contract is terminal.
        session_id: SessionId,
        /// Recorded terminal ownership reason.
        reason: OwnershipTerminalReason,
    },
}

/// Host-routed session-local mutation guarded by ownership.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SessionHostMutation {
    /// Update the session default handler.
    SetDefaultHandler {
        /// New default handler binding.
        handler: HandlerId,
    },
    /// Update one edge-bound handler.
    UpdateEdgeHandler {
        /// Edge whose handler binding should change.
        edge: Edge,
        /// New handler binding for the edge.
        handler: HandlerId,
    },
    /// Update one edge coherence trace.
    UpdateTrace {
        /// Edge whose coherence trace should change.
        edge: Edge,
        /// New trace payload.
        trace: Vec<ValType>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingOwnershipTransfer {
    pub(crate) receipt: OwnershipReceipt,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SessionOwnershipState {
    pub(crate) current: Option<OwnershipCapability>,
    pub(crate) pending_transfer: Option<PendingOwnershipTransfer>,
    pub(crate) terminal_reason: Option<OwnershipTerminalReason>,
    pub(crate) next_claim_id: OwnershipClaimId,
}

impl Default for SessionOwnershipState {
    fn default() -> Self {
        Self {
            current: None,
            pending_transfer: None,
            terminal_reason: None,
            next_claim_id: 1,
        }
    }
}

/// Per-endpoint type tracking: current state + original for unfolding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeEntry {
    /// Current local type (advances with each completed instruction).
    pub current: LocalTypeR,
    /// Original local type (for unfolding recursive variables).
    pub original: LocalTypeR,
}
