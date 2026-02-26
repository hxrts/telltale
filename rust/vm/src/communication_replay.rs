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
        let payload_bytes =
            serde_json::to_vec(payload).unwrap_or_else(|_| format!("{payload:?}").into_bytes());
        Self {
            domain_tag: default_domain_tag(),
            sid: edge.sid,
            sender: edge.sender.clone(),
            receiver: edge.receiver.clone(),
            step_kind,
            label: label.into(),
            payload_digest: DefaultVerificationModel::hash(HashTag::Value, &payload_bytes),
            sequence_no,
        }
    }

    /// Return the canonical directed edge for this identity.
    #[must_use]
    pub fn edge(&self) -> Edge {
        Edge::new(self.sid, self.sender.clone(), self.receiver.clone())
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
        let bytes = serde_json::to_vec(self).unwrap_or_else(|_| format!("{self:?}").into_bytes());
        DefaultVerificationModel::hash(HashTag::Nullifier, &bytes)
    }
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
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct DefaultCommunicationConsumption {
    /// Configured mode.
    #[serde(default)]
    pub mode: CommunicationReplayMode,
    /// Deterministic replay state.
    #[serde(default)]
    pub state: CommunicationReplayState,
}

impl DefaultCommunicationConsumption {
    /// Create a replay-consumption model in `mode`.
    #[must_use]
    pub fn new(mode: CommunicationReplayMode) -> Self {
        Self {
            mode,
            state: CommunicationReplayState::default(),
        }
    }
}

fn identity_nullifier(identity: &CommunicationIdentity) -> Nullifier {
    let bytes =
        serde_json::to_vec(identity).unwrap_or_else(|_| format!("{identity:?}").into_bytes());
    Nullifier(DefaultVerificationModel::hash(HashTag::Nullifier, &bytes))
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

    fn allocate_send_sequence(&mut self, edge: &Edge) -> u64 {
        let entry = self
            .state
            .next_send_sequence
            .entry(edge.clone())
            .or_insert(0);
        let sequence_no = *entry;
        *entry = entry.saturating_add(1);
        sequence_no
    }

    fn consume_receive(
        &mut self,
        identity: &CommunicationIdentity,
    ) -> Result<CommunicationConsumeResult, CommunicationReplayError> {
        let pre_root = self.state.root();
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
                self.state
                    .next_recv_sequence
                    .insert(edge, expected.saturating_add(1));
                None
            }
            CommunicationReplayMode::Nullifier => {
                let nullifier = identity_nullifier(identity);
                if self.state.consumed_nullifiers.contains(&nullifier) {
                    return Err(CommunicationReplayError::DuplicateIdentity { nullifier });
                }
                self.state.consumed_nullifiers.insert(nullifier);
                Some(nullifier)
            }
        };
        let post_root = self.state.root();
        Ok(CommunicationConsumeResult {
            mode: self.mode,
            pre_root,
            post_root,
            consumed_nullifier,
        })
    }

    fn prune_session(&mut self, sid: SessionId) {
        self.state
            .next_send_sequence
            .retain(|edge, _| edge.sid != sid);
        self.state
            .next_recv_sequence
            .retain(|edge, _| edge.sid != sid);
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
}
