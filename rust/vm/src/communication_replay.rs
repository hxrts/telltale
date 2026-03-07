//! Communication replay-consumption model for send/receive boundaries.
//!
//! Canonical identity schema fields:
//! - `domain_tag`: `telltale.comm.identity.v1`
//! - `sid`, `sender`, `receiver`
//! - `step_kind`, `label`
//! - `payload_digest`
//! - `sequence_no`

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use telltale_types::ValType;

use crate::coroutine::Value;
use crate::session::{Edge, SessionId};
use crate::verification::{DefaultVerificationModel, Hash, HashTag, Nullifier, VerificationModel};

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
    bincode::serialize(value).unwrap_or_default()
}

fn zero_hash() -> Hash {
    Hash([0_u8; 32])
}

fn xor_hash(lhs: Hash, rhs: Hash) -> Hash {
    let mut out = [0_u8; 32];
    for (slot, (left, right)) in out.iter_mut().zip(lhs.0.into_iter().zip(rhs.0.into_iter())) {
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

    /// Build an identity by hashing the payload with canonical binary encoding.
    #[must_use]
    pub fn build(&self, payload: &Value, sequence_no: u64) -> CommunicationIdentity {
        let payload_bytes = replay_binary_encode(payload);
        let payload_digest = DefaultVerificationModel::hash(HashTag::Value, &payload_bytes);
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
    /// Deterministic digest of replay-consumption state.
    #[must_use]
    pub fn root(&self) -> Hash {
        ReplayRootCache::from_state(self).root()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
struct ReplayRootCache {
    send_sequence_acc: Hash,
    send_sequence_len: usize,
    recv_sequence_acc: Hash,
    recv_sequence_len: usize,
    nullifier_acc: Hash,
    nullifier_len: usize,
}

impl Default for ReplayRootCache {
    fn default() -> Self {
        Self {
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
    fn from_state(state: &CommunicationReplayState) -> Self {
        let mut cache = Self::default();
        for (edge, sequence_no) in &state.next_send_sequence {
            cache.send_sequence_acc = xor_hash(
                cache.send_sequence_acc,
                hash_send_sequence_entry(edge, *sequence_no),
            );
            cache.send_sequence_len = cache.send_sequence_len.saturating_add(1);
        }
        for (edge, sequence_no) in &state.next_recv_sequence {
            cache.recv_sequence_acc = xor_hash(
                cache.recv_sequence_acc,
                hash_recv_sequence_entry(edge, *sequence_no),
            );
            cache.recv_sequence_len = cache.recv_sequence_len.saturating_add(1);
        }
        for nullifier in &state.consumed_nullifiers {
            cache.nullifier_acc = xor_hash(cache.nullifier_acc, hash_nullifier_entry(*nullifier));
            cache.nullifier_len = cache.nullifier_len.saturating_add(1);
        }
        cache
    }

    fn component_root(prefix: u8, len: usize, acc: Hash) -> Hash {
        DefaultVerificationModel::hash(
            HashTag::Nullifier,
            &replay_binary_encode(&(prefix, len, acc)),
        )
    }

    fn root(&self) -> Hash {
        let send_root = Self::component_root(0x11, self.send_sequence_len, self.send_sequence_acc);
        let recv_root = Self::component_root(0x12, self.recv_sequence_len, self.recv_sequence_acc);
        let nullifier_root = Self::component_root(0x13, self.nullifier_len, self.nullifier_acc);
        DefaultVerificationModel::hash(
            HashTag::Nullifier,
            &replay_binary_encode(&(send_root, recv_root, nullifier_root)),
        )
    }

    fn update_send_sequence(&mut self, edge: &Edge, old: Option<u64>, new: u64) {
        if let Some(old) = old {
            self.send_sequence_acc =
                xor_hash(self.send_sequence_acc, hash_send_sequence_entry(edge, old));
        } else {
            self.send_sequence_len = self.send_sequence_len.saturating_add(1);
        }
        self.send_sequence_acc =
            xor_hash(self.send_sequence_acc, hash_send_sequence_entry(edge, new));
    }

    fn update_recv_sequence(&mut self, edge: &Edge, old: Option<u64>, new: u64) {
        if let Some(old) = old {
            self.recv_sequence_acc =
                xor_hash(self.recv_sequence_acc, hash_recv_sequence_entry(edge, old));
        } else {
            self.recv_sequence_len = self.recv_sequence_len.saturating_add(1);
        }
        self.recv_sequence_acc =
            xor_hash(self.recv_sequence_acc, hash_recv_sequence_entry(edge, new));
    }

    fn insert_nullifier(&mut self, nullifier: Nullifier) {
        self.nullifier_acc = xor_hash(self.nullifier_acc, hash_nullifier_entry(nullifier));
        self.nullifier_len = self.nullifier_len.saturating_add(1);
    }

    fn remove_send_sequence(&mut self, edge: &Edge, sequence_no: u64) {
        self.send_sequence_acc = xor_hash(
            self.send_sequence_acc,
            hash_send_sequence_entry(edge, sequence_no),
        );
        self.send_sequence_len = self.send_sequence_len.saturating_sub(1);
    }

    fn remove_recv_sequence(&mut self, edge: &Edge, sequence_no: u64) {
        self.recv_sequence_acc = xor_hash(
            self.recv_sequence_acc,
            hash_recv_sequence_entry(edge, sequence_no),
        );
        self.recv_sequence_len = self.recv_sequence_len.saturating_sub(1);
    }
}

fn hash_send_sequence_entry(edge: &Edge, sequence_no: u64) -> Hash {
    DefaultVerificationModel::hash(
        HashTag::Nullifier,
        &replay_binary_encode(&(0x21_u8, edge, sequence_no)),
    )
}

fn hash_recv_sequence_entry(edge: &Edge, sequence_no: u64) -> Hash {
    DefaultVerificationModel::hash(
        HashTag::Nullifier,
        &replay_binary_encode(&(0x22_u8, edge, sequence_no)),
    )
}

fn hash_nullifier_entry(nullifier: Nullifier) -> Hash {
    DefaultVerificationModel::hash(
        HashTag::Nullifier,
        &replay_binary_encode(&(0x23_u8, nullifier)),
    )
}

/// Replay-consumption error.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CommunicationReplayError {
    /// Received sequence number does not match expected edge position.
    SequenceMismatch {
        /// Expected sequence number.
        expected: u64,
        /// Received sequence number.
        actual: u64,
    },
    /// Identity nullifier was already consumed.
    DuplicateIdentity {
        /// Duplicate nullifier.
        nullifier: Nullifier,
    },
}

impl CommunicationReplayError {
    /// Stable deterministic error tag.
    #[must_use]
    pub fn tag(&self) -> &'static str {
        match self {
            Self::SequenceMismatch { .. } => COMM_REPLAY_SEQUENCE_MISMATCH_TAG,
            Self::DuplicateIdentity { .. } => COMM_REPLAY_DUPLICATE_TAG,
        }
    }
}

/// Replay-consumption check result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommunicationConsumeResult {
    /// Mode used for the check.
    pub mode: CommunicationReplayMode,
    /// Replay-state root before check.
    pub pre_root: Hash,
    /// Replay-state root after check.
    pub post_root: Hash,
    /// Consumed nullifier when mode is `Nullifier`.
    pub consumed_nullifier: Option<Nullifier>,
}

/// Proof-friendly replay-consumption artifact recorded at receive boundaries.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CommunicationConsumptionArtifact {
    /// Scheduler tick at consumption time.
    pub tick: u64,
    /// Canonical identity consumed at receive.
    pub identity: CommunicationIdentity,
    /// Active replay mode.
    pub mode: CommunicationReplayMode,
    /// Replay-state root before receive consumption.
    pub pre_root: Hash,
    /// Replay-state root after receive consumption.
    pub post_root: Hash,
}

/// Replay-consumption interface for send/receive boundaries.
pub trait CommunicationConsumption {
    /// Active replay mode.
    fn mode(&self) -> CommunicationReplayMode;
    /// Set active replay mode.
    fn set_mode(&mut self, mode: CommunicationReplayMode);
    /// Read replay-consumption state.
    fn state(&self) -> &CommunicationReplayState;
    /// Read the deterministic replay-state root.
    fn root(&self) -> Hash;
    /// Allocate next outbound sequence number for an edge.
    fn allocate_send_sequence(&mut self, edge: &Edge) -> u64;
    /// Consume a receive identity according to the selected mode.
    ///
    /// # Errors
    ///
    /// Returns [`CommunicationReplayError`] when the active mode rejects the
    /// receive identity (for example, sequence mismatch or duplicate identity).
    fn consume_receive(
        &mut self,
        identity: &CommunicationIdentity,
    ) -> Result<CommunicationConsumeResult, CommunicationReplayError>;
    /// Drop replay-tracker state for a closed session.
    fn prune_session(&mut self, sid: SessionId);
}

/// Default replay-consumption implementation used by the VM.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DefaultCommunicationConsumption {
    /// Configured mode.
    #[serde(default)]
    pub mode: CommunicationReplayMode,
    /// Deterministic replay state.
    #[serde(default)]
    pub state: CommunicationReplayState,
    /// Incrementally maintained replay root cache.
    #[serde(skip)]
    root_cache: ReplayRootCache,
}

impl DefaultCommunicationConsumption {
    /// Create a replay-consumption model in `mode`.
    #[must_use]
    pub fn new(mode: CommunicationReplayMode) -> Self {
        let mut model = Self {
            mode,
            state: CommunicationReplayState::default(),
            root_cache: ReplayRootCache::default(),
        };
        model.rebuild_root_cache();
        model
    }

    /// Deterministic replay root using the cached incremental path.
    #[must_use]
    pub fn root(&self) -> Hash {
        self.root_cache.root()
    }

    fn rebuild_root_cache(&mut self) {
        self.root_cache = ReplayRootCache::from_state(&self.state);
    }
}

fn identity_nullifier(identity: &CommunicationIdentity) -> Nullifier {
    let bytes = replay_binary_encode(identity);
    Nullifier(DefaultVerificationModel::hash(HashTag::Nullifier, &bytes))
}

#[derive(Debug, Deserialize)]
struct DefaultCommunicationConsumptionSerde {
    #[serde(default)]
    mode: CommunicationReplayMode,
    #[serde(default)]
    state: CommunicationReplayState,
}

impl<'de> Deserialize<'de> for DefaultCommunicationConsumption {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let raw = DefaultCommunicationConsumptionSerde::deserialize(deserializer)?;
        let mut model = Self {
            mode: raw.mode,
            state: raw.state,
            root_cache: ReplayRootCache::default(),
        };
        model.rebuild_root_cache();
        Ok(model)
    }
}

impl CommunicationConsumption for DefaultCommunicationConsumption {
    fn mode(&self) -> CommunicationReplayMode {
        self.mode
    }

    fn set_mode(&mut self, mode: CommunicationReplayMode) {
        self.mode = mode;
    }

    fn state(&self) -> &CommunicationReplayState {
        &self.state
    }

    fn root(&self) -> Hash {
        DefaultCommunicationConsumption::root(self)
    }

    fn allocate_send_sequence(&mut self, edge: &Edge) -> u64 {
        let previous = self.state.next_send_sequence.get(edge).copied();
        let entry = self
            .state
            .next_send_sequence
            .entry(edge.clone())
            .or_insert(0);
        let sequence_no = *entry;
        *entry = entry.saturating_add(1);
        self.root_cache.update_send_sequence(edge, previous, *entry);
        sequence_no
    }

    fn consume_receive(
        &mut self,
        identity: &CommunicationIdentity,
    ) -> Result<CommunicationConsumeResult, CommunicationReplayError> {
        let pre_root = self.root();
        let consumed_nullifier = match self.mode {
            CommunicationReplayMode::Off => None,
            CommunicationReplayMode::Sequence => {
                let edge = identity.edge();
                let expected = self
                    .state
                    .next_recv_sequence
                    .get(&edge)
                    .copied()
                    .unwrap_or(0);
                if identity.sequence_no != expected {
                    return Err(CommunicationReplayError::SequenceMismatch {
                        expected,
                        actual: identity.sequence_no,
                    });
                }
                let previous = self.state.next_recv_sequence.get(&edge).copied();
                self.state
                    .next_recv_sequence
                    .insert(edge, expected.saturating_add(1));
                self.root_cache.update_recv_sequence(
                    &identity.edge(),
                    previous,
                    expected.saturating_add(1),
                );
                None
            }
            CommunicationReplayMode::Nullifier => {
                let nullifier = identity_nullifier(identity);
                if self.state.consumed_nullifiers.contains(&nullifier) {
                    return Err(CommunicationReplayError::DuplicateIdentity { nullifier });
                }
                self.state.consumed_nullifiers.insert(nullifier);
                self.root_cache.insert_nullifier(nullifier);
                Some(nullifier)
            }
        };
        let post_root = self.root();
        Ok(CommunicationConsumeResult {
            mode: self.mode,
            pre_root,
            post_root,
            consumed_nullifier,
        })
    }

    fn prune_session(&mut self, sid: SessionId) {
        let send_pruned: Vec<_> = self
            .state
            .next_send_sequence
            .iter()
            .filter_map(|(edge, sequence_no)| {
                (edge.sid == sid).then_some((edge.clone(), *sequence_no))
            })
            .collect();
        let recv_pruned: Vec<_> = self
            .state
            .next_recv_sequence
            .iter()
            .filter_map(|(edge, sequence_no)| {
                (edge.sid == sid).then_some((edge.clone(), *sequence_no))
            })
            .collect();
        self.state
            .next_send_sequence
            .retain(|edge, _| edge.sid != sid);
        self.state
            .next_recv_sequence
            .retain(|edge, _| edge.sid != sid);
        for (edge, sequence_no) in send_pruned {
            self.root_cache.remove_send_sequence(&edge, sequence_no);
        }
        for (edge, sequence_no) in recv_pruned {
            self.root_cache.remove_recv_sequence(&edge, sequence_no);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_identity(sequence_no: u64) -> CommunicationIdentity {
        let edge = Edge::new(7, "A", "B");
        CommunicationIdentity::from_payload(
            &edge,
            CommunicationStepKind::Receive,
            "msg",
            &Value::Nat(3),
            sequence_no,
        )
    }

    #[test]
    fn off_mode_accepts_duplicate_identities() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Off);
        let identity = sample_identity(0);
        assert!(model.consume_receive(&identity).is_ok());
        assert!(model.consume_receive(&identity).is_ok());
    }

    #[test]
    fn sequence_mode_accepts_in_order_messages() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Sequence);
        assert!(model.consume_receive(&sample_identity(0)).is_ok());
        assert!(model.consume_receive(&sample_identity(1)).is_ok());
    }

    #[test]
    fn sequence_mode_rejects_out_of_order_messages() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Sequence);
        let first = sample_identity(0);
        let second = sample_identity(2);
        assert!(model.consume_receive(&first).is_ok());
        let err = model
            .consume_receive(&second)
            .expect_err("out-of-order sequence should fail");
        assert_eq!(err.tag(), COMM_REPLAY_SEQUENCE_MISMATCH_TAG);
    }

    #[test]
    fn nullifier_mode_rejects_duplicate_identities() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Nullifier);
        let identity = sample_identity(5);
        assert!(model.consume_receive(&identity).is_ok());
        let err = model
            .consume_receive(&identity)
            .expect_err("duplicate identity should fail");
        assert_eq!(err.tag(), COMM_REPLAY_DUPLICATE_TAG);
    }

    #[test]
    fn canonical_receive_label_uses_typed_context_when_available() {
        let label = canonical_receive_label_context("msg", Some(&ValType::Nat));
        assert_eq!(label, "recv:Nat");
    }

    #[test]
    fn canonical_receive_label_falls_back_to_runtime_label_when_untyped() {
        let label = canonical_receive_label_context("msg", None);
        assert_eq!(label, "msg");
    }

    #[test]
    fn identity_seed_matches_direct_identity_construction() {
        let edge = Edge::new(7, "A", "B");
        let seed = CommunicationIdentitySeed::new(&edge, CommunicationStepKind::Receive, "msg");
        let payload = Value::Prod(Box::new(Value::Nat(3)), Box::new(Value::Bool(true)));
        assert_eq!(
            seed.build(&payload, 5),
            CommunicationIdentity::from_payload(
                &edge,
                CommunicationStepKind::Receive,
                "msg",
                &payload,
                5,
            )
        );
    }

    #[test]
    fn cached_replay_root_matches_state_root_after_updates() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Sequence);
        let edge = Edge::new(7, "A", "B");
        assert_eq!(model.root(), model.state().root());

        let _sequence = model.allocate_send_sequence(&edge);
        assert_eq!(model.root(), model.state().root());

        assert!(model.consume_receive(&sample_identity(0)).is_ok());
        assert_eq!(model.root(), model.state().root());

        model.set_mode(CommunicationReplayMode::Nullifier);
        assert!(model.consume_receive(&sample_identity(9)).is_ok());
        assert_eq!(model.root(), model.state().root());

        model.prune_session(7);
        assert_eq!(model.root(), model.state().root());
    }

    #[test]
    fn cached_replay_root_survives_roundtrip() {
        let mut model = DefaultCommunicationConsumption::new(CommunicationReplayMode::Nullifier);
        let edge = Edge::new(7, "A", "B");
        let _sequence = model.allocate_send_sequence(&edge);
        assert!(model.consume_receive(&sample_identity(5)).is_ok());

        let encoded = bincode::serialize(&model).expect("serialize replay consumption");
        let decoded: DefaultCommunicationConsumption =
            bincode::deserialize(&encoded).expect("deserialize replay consumption");

        assert_eq!(decoded.root(), decoded.state().root());
        assert_eq!(decoded, model);
    }
}
