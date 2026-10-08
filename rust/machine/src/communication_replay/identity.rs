// Communication replay-consumption model for send/receive boundaries.
//
// Canonical identity schema fields:
// - `domain_tag`: `telltale.comm.identity.v1`
// - `sid`, `sender`, `receiver`
// - `step_kind`, `label`
// - `payload_digest`
// - `sequence_no`

use telltale_types::ValType;

/// Domain-separation tag for canonical communication identities.
pub const COMM_IDENTITY_DOMAIN_TAG: &str = "telltale.comm.identity.v1";
/// Stable error tag for sequence replay violations.
pub const COMM_REPLAY_SEQUENCE_MISMATCH_TAG: &str = "comm_replay.sequence_mismatch";
/// Stable error tag for duplicate nullifier replay violations.
pub const COMM_REPLAY_DUPLICATE_TAG: &str = "comm_replay.duplicate";

fn default_domain_tag() -> String {
    COMM_IDENTITY_DOMAIN_TAG.to_string()
}

fn replay_binary_encode<T: Serialize>(value: &T) -> Vec<u8> {
    crate::serialization::binary_encode(value).unwrap_or_default()
}

fn zero_hash() -> Hash {
    Hash([0_u8; 32])
}

fn xor_hash(lhs: Hash, rhs: Hash) -> Hash {
    let mut out = [0_u8; 32];
    for (slot, (left, right)) in out.iter_mut().zip(lhs.0.into_iter().zip(rhs.0)) {
        *slot = left ^ right;
    }
    Hash(out)
}

/// Replay-consumption mode for communication events.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum CommunicationReplayMode {
    /// Disable replay-consumption enforcement.
    #[default]
    Off,
    /// Enforce per-edge monotonic sequence consumption at receive.
    Sequence,
    /// Enforce one-time identity consumption via nullifiers.
    Nullifier,
}

/// Which identity fields derive a receive nullifier in
/// [`CommunicationReplayMode::Nullifier`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum CommunicationNullifierIdentity {
    /// Full canonical identity, including the transport `sequence_no`.
    ///
    /// A re-sent message carrying a fresh sequence number derives a fresh
    /// nullifier and is accepted.
    #[default]
    SequenceBound,
    /// Content identity only: domain tag, `sid`, roles, step kind, label, and
    /// payload digest. `sequence_no` is excluded.
    ///
    /// A re-sent message with identical content derives the same nullifier
    /// and is rejected as a duplicate regardless of its sequence number.
    /// Protocols that legitimately deliver identical content twice on the
    /// same edge and label must distinguish those payloads.
    ContentOnly,
}

impl CommunicationNullifierIdentity {
    /// Derive the receive nullifier for `identity` under `model`.
    #[must_use]
    pub fn nullifier(self, identity: &CommunicationIdentity, model: HashModel) -> Nullifier {
        let bytes = match self {
            Self::SequenceBound => replay_binary_encode(identity),
            Self::ContentOnly => replay_binary_encode(&(
                0x31_u8,
                &identity.domain_tag,
                identity.sid,
                &identity.sender,
                &identity.receiver,
                identity.step_kind,
                &identity.label,
                identity.payload_digest,
            )),
        };
        Nullifier(model.hash(HashTag::Nullifier, &bytes))
    }
}

/// Protocol step context used in canonical communication identities.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CommunicationStepKind {
    /// Outbound send payload.
    Send,
    /// Inbound receive payload.
    Receive,
    /// Outbound offer label.
    Offer,
    /// Inbound choose label.
    Choose,
}

/// Canonical communication identity used for replay-consumption decisions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommunicationIdentity {
    /// Domain-separation tag.
    #[serde(default = "default_domain_tag")]
    pub domain_tag: String,
    /// Session id.
    pub sid: SessionId,
    /// Sender role.
    pub sender: String,
    /// Receiver role.
    pub receiver: String,
    /// Protocol step context.
    pub step_kind: CommunicationStepKind,
    /// Session label context.
    pub label: String,
    /// Domain-separated payload digest.
    pub payload_digest: Hash,
    /// Sequence number carried by the transport message.
    #[serde(default)]
    pub sequence_no: u64,
}

/// Precomputed stable identity fields that can be reused across payloads.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommunicationIdentitySeed {
    /// Domain-separation tag.
    #[serde(default = "default_domain_tag")]
    pub domain_tag: String,
    /// Session id.
    pub sid: SessionId,
    /// Sender role.
    pub sender: String,
    /// Receiver role.
    pub receiver: String,
    /// Protocol step context.
    pub step_kind: CommunicationStepKind,
    /// Session label context.
    pub label: String,
}

/// Canonical receive replay label-context.
///
/// Lean uses deterministic typed-context tokens for receive replay identities.
/// Rust aligns with that token when the session type carries an expected payload
/// annotation, and falls back to the runtime label when no annotation exists.
#[must_use]
pub fn canonical_receive_label_context(
    runtime_label: &str,
    expected_type: Option<&ValType>,
) -> String {
    match expected_type {
        Some(expected) => format!("recv:{expected:?}"),
        None => runtime_label.to_string(),
    }
}

impl CommunicationIdentity {
    /// Build a canonical identity from an edge, label, and payload.
    #[must_use]
    pub fn from_payload(
        edge: &Edge,
        step_kind: CommunicationStepKind,
        label: impl Into<String>,
        payload: &Value,
        sequence_no: u64,
    ) -> Self {
        CommunicationIdentitySeed::new(edge, step_kind, label).build(payload, sequence_no)
    }

    /// Return the canonical directed edge for this identity.
    #[must_use]
    pub fn edge(&self) -> Edge {
        Edge::new(self.sid, self.sender.clone(), self.receiver.clone())
    }
}

impl CommunicationIdentitySeed {
    /// Build a reusable identity seed from stable edge and label fields.
    #[must_use]
    pub fn new(edge: &Edge, step_kind: CommunicationStepKind, label: impl Into<String>) -> Self {
        Self {
            domain_tag: default_domain_tag(),
            sid: edge.sid,
            sender: edge.sender.clone(),
            receiver: edge.receiver.clone(),
            step_kind,
            label: label.into(),
        }
    }

    /// Build an identity from a previously hashed payload.
    #[must_use]
    pub fn build_with_digest(
        &self,
        payload_digest: Hash,
        sequence_no: u64,
    ) -> CommunicationIdentity {
        CommunicationIdentity {
            domain_tag: self.domain_tag.clone(),
            sid: self.sid,
            sender: self.sender.clone(),
            receiver: self.receiver.clone(),
            step_kind: self.step_kind,
            label: self.label.clone(),
            payload_digest,
            sequence_no,
        }
    }

    /// Build an identity by hashing the payload with the default [`HashModel`].
    #[must_use]
    pub fn build(&self, payload: &Value, sequence_no: u64) -> CommunicationIdentity {
        self.build_with_model(payload, sequence_no, HashModel::DEFAULT)
    }

    /// Build an identity by hashing the canonical payload encoding with `model`.
    #[must_use]
    pub fn build_with_model(
        &self,
        payload: &Value,
        sequence_no: u64,
        model: HashModel,
    ) -> CommunicationIdentity {
        let payload_bytes = replay_binary_encode(payload);
        let payload_digest = model.hash(HashTag::Value, &payload_bytes);
        self.build_with_digest(payload_digest, sequence_no)
    }
}

/// Deterministic replay-consumption snapshot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct CommunicationReplayState {
    /// Next outbound sequence id per edge.
    #[serde(default)]
    pub next_send_sequence: BTreeMap<Edge, u64>,
    /// Next expected inbound sequence id per edge.
    #[serde(default)]
    pub next_recv_sequence: BTreeMap<Edge, u64>,
    /// Nullifiers consumed at receive boundaries.
    #[serde(default)]
    pub consumed_nullifiers: BTreeSet<Nullifier>,
}

impl CommunicationReplayState {
    /// Deterministic digest of replay-consumption state under the default [`HashModel`].
    #[must_use]
    pub fn root(&self) -> Hash {
        self.root_with(HashModel::DEFAULT)
    }

    /// Deterministic digest of replay-consumption state under `model`.
    #[must_use]
    pub fn root_with(&self, model: HashModel) -> Hash {
        ReplayRootCache::from_state(self, model).root()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReplayRootCache {
    model: HashModel,
    send_sequence_acc: Hash,
    send_sequence_len: usize,
    recv_sequence_acc: Hash,
    recv_sequence_len: usize,
    nullifier_acc: Hash,
    nullifier_len: usize,
}

impl ReplayRootCache {
    fn empty(model: HashModel) -> Self {
        Self {
            model,
            send_sequence_acc: zero_hash(),
            send_sequence_len: 0,
            recv_sequence_acc: zero_hash(),
            recv_sequence_len: 0,
            nullifier_acc: zero_hash(),
            nullifier_len: 0,
        }
    }
}

impl Default for DefaultCommunicationConsumption {
    fn default() -> Self {
        Self::new(CommunicationReplayMode::Off)
    }
}

impl ReplayRootCache {
    fn from_state(state: &CommunicationReplayState, model: HashModel) -> Self {
        let mut cache = Self::empty(model);
        for (edge, sequence_no) in &state.next_send_sequence {
            cache.send_sequence_acc = xor_hash(
                cache.send_sequence_acc,
                hash_send_sequence_entry(model, edge, *sequence_no),
            );
            cache.send_sequence_len = cache.send_sequence_len.saturating_add(1);
        }
        for (edge, sequence_no) in &state.next_recv_sequence {
            cache.recv_sequence_acc = xor_hash(
                cache.recv_sequence_acc,
                hash_recv_sequence_entry(model, edge, *sequence_no),
            );
            cache.recv_sequence_len = cache.recv_sequence_len.saturating_add(1);
        }
        for nullifier in &state.consumed_nullifiers {
            cache.nullifier_acc = xor_hash(cache.nullifier_acc, hash_nullifier_entry(model, *nullifier));
            cache.nullifier_len = cache.nullifier_len.saturating_add(1);
        }
        cache
    }

    fn component_root(&self, prefix: u8, len: usize, acc: Hash) -> Hash {
        self.model.hash(
            HashTag::Nullifier,
            &replay_binary_encode(&(prefix, len, acc)),
        )
    }

    fn root(&self) -> Hash {
        let send_root = self.component_root(0x11, self.send_sequence_len, self.send_sequence_acc);
        let recv_root = self.component_root(0x12, self.recv_sequence_len, self.recv_sequence_acc);
        let nullifier_root = self.component_root(0x13, self.nullifier_len, self.nullifier_acc);
        self.model.hash(
            HashTag::Nullifier,
            &replay_binary_encode(&(send_root, recv_root, nullifier_root)),
        )
    }

    fn update_send_sequence(&mut self, edge: &Edge, old: Option<u64>, new: u64) {
        if let Some(old) = old {
            self.send_sequence_acc =
                xor_hash(self.send_sequence_acc, hash_send_sequence_entry(self.model, edge, old));
        } else {
            self.send_sequence_len = self.send_sequence_len.saturating_add(1);
        }
        self.send_sequence_acc =
            xor_hash(self.send_sequence_acc, hash_send_sequence_entry(self.model, edge, new));
    }

    fn update_recv_sequence(&mut self, edge: &Edge, old: Option<u64>, new: u64) {
        if let Some(old) = old {
            self.recv_sequence_acc =
                xor_hash(self.recv_sequence_acc, hash_recv_sequence_entry(self.model, edge, old));
        } else {
            self.recv_sequence_len = self.recv_sequence_len.saturating_add(1);
        }
        self.recv_sequence_acc =
            xor_hash(self.recv_sequence_acc, hash_recv_sequence_entry(self.model, edge, new));
    }

    fn insert_nullifier(&mut self, nullifier: Nullifier) {
        self.nullifier_acc = xor_hash(self.nullifier_acc, hash_nullifier_entry(self.model, nullifier));
        self.nullifier_len = self.nullifier_len.saturating_add(1);
    }

    fn remove_send_sequence(&mut self, edge: &Edge, sequence_no: u64) {
        self.send_sequence_acc = xor_hash(
            self.send_sequence_acc,
            hash_send_sequence_entry(self.model, edge, sequence_no),
        );
        self.send_sequence_len = self.send_sequence_len.saturating_sub(1);
    }

    fn remove_recv_sequence(&mut self, edge: &Edge, sequence_no: u64) {
        self.recv_sequence_acc = xor_hash(
            self.recv_sequence_acc,
            hash_recv_sequence_entry(self.model, edge, sequence_no),
        );
        self.recv_sequence_len = self.recv_sequence_len.saturating_sub(1);
    }
}

fn hash_send_sequence_entry(model: HashModel, edge: &Edge, sequence_no: u64) -> Hash {
    model.hash(
        HashTag::Nullifier,
        &replay_binary_encode(&(0x21_u8, edge, sequence_no)),
    )
}

fn hash_recv_sequence_entry(model: HashModel, edge: &Edge, sequence_no: u64) -> Hash {
    model.hash(
        HashTag::Nullifier,
        &replay_binary_encode(&(0x22_u8, edge, sequence_no)),
    )
}

fn hash_nullifier_entry(model: HashModel, nullifier: Nullifier) -> Hash {
    model.hash(
        HashTag::Nullifier,
        &replay_binary_encode(&(0x23_u8, nullifier)),
    )
}

// moved to `model.rs`
