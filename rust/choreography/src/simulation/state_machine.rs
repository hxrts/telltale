//! Protocol state machine for step-by-step simulation
//!
//! This module provides the core abstraction for simulating protocol execution
//! in a controlled, step-by-step manner.

use serde::{Deserialize, Serialize};

use super::envelope::ProtocolEnvelope;
use crate::effects::{ChoreographyError, LabelId};
use crate::identifiers::RoleName;

/// What a protocol state machine is blocked on.
///
/// This enum describes what input is needed for the state machine
/// to make progress.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockedOn<L: LabelId> {
    /// Waiting to send a message to a role.
    Send {
        /// The destination role.
        to: RoleName,
        /// The message type being sent.
        message_type: String,
    },
    /// Waiting to receive a message from a role.
    Recv {
        /// The source role.
        from: RoleName,
        /// Expected message types (any of these is acceptable).
        expected_types: Vec<String>,
    },
    /// Waiting for an internal choice decision.
    Choice {
        /// Available branch labels.
        branches: Vec<L>,
    },
    /// Waiting for an external choice (offer).
    Offer {
        /// The role making the choice.
        from: RoleName,
        /// Expected branch labels.
        branches: Vec<L>,
    },
    /// Protocol has completed successfully.
    Complete,
    /// Protocol has failed with an error.
    Failed(String),
}

impl<L: LabelId> BlockedOn<L> {
    /// Check if the state machine is complete (successfully or with error).
    #[must_use]
    pub fn is_terminal(&self) -> bool {
        matches!(self, BlockedOn::Complete | BlockedOn::Failed(_))
    }

    /// Check if waiting to send.
    #[must_use]
    pub fn is_send(&self) -> bool {
        matches!(self, BlockedOn::Send { .. })
    }

    /// Check if waiting to receive.
    #[must_use]
    pub fn is_recv(&self) -> bool {
        matches!(self, BlockedOn::Recv { .. })
    }

    /// Check if waiting for a choice.
    #[must_use]
    pub fn is_choice(&self) -> bool {
        matches!(self, BlockedOn::Choice { .. } | BlockedOn::Offer { .. })
    }
}

/// Input to advance the state machine.
#[derive(Debug, Clone)]
pub enum StepInput<L: LabelId> {
    /// Provide a message to send.
    SendMessage(ProtocolEnvelope),
    /// Provide a received message.
    RecvMessage(ProtocolEnvelope),
    /// Make an internal choice.
    MakeChoice(L),
    /// Receive an external choice (offer).
    ReceiveOffer(L),
    /// Signal timeout.
    Timeout,
    /// Signal error.
    Error(String),
}

impl<L: LabelId> StepInput<L> {
    /// Create a send message input.
    pub fn send(envelope: ProtocolEnvelope) -> Self {
        Self::SendMessage(envelope)
    }

    /// Create a receive message input.
    pub fn recv(envelope: ProtocolEnvelope) -> Self {
        Self::RecvMessage(envelope)
    }

    /// Create a choice input.
    pub fn choice(branch: L) -> Self {
        Self::MakeChoice(branch)
    }

    /// Create an offer input.
    pub fn offer(branch: L) -> Self {
        Self::ReceiveOffer(branch)
    }
}

/// Output from a state machine step.
#[derive(Debug, Clone)]
pub enum StepOutput<L: LabelId> {
    /// A message was sent.
    Sent(ProtocolEnvelope),
    /// A message was received and processed.
    Received {
        /// The received envelope.
        envelope: ProtocolEnvelope,
        /// Any response to send (for request-response patterns).
        response: Option<ProtocolEnvelope>,
    },
    /// A choice was made.
    ChoiceMade(L),
    /// An offer was received.
    OfferReceived(L),
    /// The protocol completed.
    Completed,
    /// No progress was made (input didn't match what was needed).
    NoProgress,
}

impl<L: LabelId> StepOutput<L> {
    /// Check if this output indicates completion.
    #[must_use]
    pub fn is_completed(&self) -> bool {
        matches!(self, StepOutput::Completed)
    }

    /// Check if progress was made.
    #[must_use]
    pub fn made_progress(&self) -> bool {
        !matches!(self, StepOutput::NoProgress)
    }
}

/// A checkpoint of protocol state for save/restore.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Checkpoint {
    /// Protocol name.
    pub protocol: String,
    /// Current role.
    pub role: RoleName,
    /// State identifier (implementation-specific).
    pub state_id: String,
    /// Serialized state data.
    pub state_data: Vec<u8>,
    /// Sequence number at checkpoint time.
    pub sequence: u64,
    /// Additional metadata.
    pub metadata: std::collections::HashMap<String, String>,
}

impl Checkpoint {
    /// Create a new checkpoint.
    pub fn new(protocol: impl Into<String>, role: RoleName, state_id: impl Into<String>) -> Self {
        Self {
            protocol: protocol.into(),
            role,
            state_id: state_id.into(),
            state_data: Vec::new(),
            sequence: 0,
            metadata: std::collections::HashMap::new(),
        }
    }

    /// Set the state data.
    #[must_use]
    pub fn with_data(mut self, data: Vec<u8>) -> Self {
        self.state_data = data;
        self
    }

    /// Set the sequence number.
    #[must_use]
    pub fn with_sequence(mut self, seq: u64) -> Self {
        self.sequence = seq;
        self
    }

    /// Add metadata.
    #[must_use]
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Serialize the checkpoint to bytes.
    pub fn to_bytes(&self) -> Result<Vec<u8>, CheckpointError> {
        bincode::serialize(self).map_err(|e| CheckpointError::Serialization(e.to_string()))
    }

    /// Deserialize a checkpoint from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CheckpointError> {
        bincode::deserialize(bytes).map_err(|e| CheckpointError::Deserialization(e.to_string()))
    }
}

/// Errors that can occur with checkpoints.
#[derive(Debug, thiserror::Error)]
pub enum CheckpointError {
    /// Serialization failed.
    #[error("Checkpoint serialization error: {0}")]
    Serialization(String),

    /// Deserialization failed.
    #[error("Checkpoint deserialization error: {0}")]
    Deserialization(String),

    /// Checkpoint is incompatible.
    #[error("Incompatible checkpoint: {0}")]
    Incompatible(String),
}

/// Trait for protocol state machines that can be stepped through.
///
/// This trait is the core abstraction for simulation. It allows
/// external simulators to control protocol execution step-by-step.
pub trait ProtocolStateMachine: Send {
    type Label: LabelId;
    /// Get the protocol name.
    fn protocol_name(&self) -> &str;

    /// Get the current role.
    fn role(&self) -> &RoleName;

    /// Get what the state machine is currently blocked on.
    fn blocked_on(&self) -> BlockedOn<Self::Label>;

    /// Attempt to advance the state machine with the given input.
    ///
    /// Returns `Ok(StepOutput)` if the step succeeded, or an error
    /// if the input was invalid for the current state.
    fn step(
        &mut self,
        input: StepInput<Self::Label>,
    ) -> Result<StepOutput<Self::Label>, ChoreographyError>;

    /// Create a checkpoint of the current state.
    fn checkpoint(&self) -> Result<Checkpoint, CheckpointError>;

    /// Restore state from a checkpoint.
    fn restore(&mut self, checkpoint: &Checkpoint) -> Result<(), CheckpointError>;

    /// Get the current sequence number.
    fn sequence(&self) -> u64;

    /// Check if the protocol has completed.
    fn is_complete(&self) -> bool {
        self.blocked_on().is_terminal()
    }
}

/// A simple state machine implementation for testing.
///
/// This implementation uses a linear sequence of expected operations.
#[derive(Debug)]
pub struct LinearStateMachine<L: LabelId> {
    protocol: String,
    role: RoleName,
    states: Vec<BlockedOn<L>>,
    current_state: usize,
    sequence: u64,
}

impl<L: LabelId> LinearStateMachine<L> {
    /// Create a new linear state machine.
    pub fn new(protocol: impl Into<String>, role: RoleName, states: Vec<BlockedOn<L>>) -> Self {
        Self {
            protocol: protocol.into(),
            role,
            states,
            current_state: 0,
            sequence: 0,
        }
    }

    /// Advance to the next state.
    fn advance(&mut self) {
        if self.current_state < self.states.len() {
            self.current_state += 1;
            self.sequence += 1;
        }
    }
}

impl<L: LabelId> ProtocolStateMachine for LinearStateMachine<L> {
    type Label = L;

    fn protocol_name(&self) -> &str {
        &self.protocol
    }

    fn role(&self) -> &RoleName {
        &self.role
    }

    fn blocked_on(&self) -> BlockedOn<Self::Label> {
        self.states
            .get(self.current_state)
            .cloned()
            .unwrap_or(BlockedOn::Complete)
    }

    fn step(
        &mut self,
        input: StepInput<Self::Label>,
    ) -> Result<StepOutput<Self::Label>, ChoreographyError> {
        let current = self.blocked_on();

        match (&current, &input) {
            (BlockedOn::Send { .. }, StepInput::SendMessage(env)) => {
                self.advance();
                Ok(StepOutput::Sent(env.clone()))
            }
            (BlockedOn::Recv { .. }, StepInput::RecvMessage(env)) => {
                self.advance();
                Ok(StepOutput::Received {
                    envelope: env.clone(),
                    response: None,
                })
            }
            (BlockedOn::Choice { branches }, StepInput::MakeChoice(branch)) => {
                if branches.contains(branch) {
                    self.advance();
                    Ok(StepOutput::ChoiceMade(*branch))
                } else {
                    Err(ChoreographyError::InvalidChoice {
                        expected: branches
                            .iter()
                            .map(|label| label.as_str().to_string())
                            .collect(),
                        actual: branch.as_str().to_string(),
                    })
                }
            }
            (BlockedOn::Offer { branches, .. }, StepInput::ReceiveOffer(branch)) => {
                if branches.contains(branch) {
                    self.advance();
                    Ok(StepOutput::OfferReceived(*branch))
                } else {
                    Err(ChoreographyError::InvalidChoice {
                        expected: branches
                            .iter()
                            .map(|label| label.as_str().to_string())
                            .collect(),
                        actual: branch.as_str().to_string(),
                    })
                }
            }
            (BlockedOn::Complete, _) => Ok(StepOutput::Completed),
            (BlockedOn::Failed(msg), _) => Err(ChoreographyError::ExecutionError(msg.clone())),
            _ => Ok(StepOutput::NoProgress),
        }
    }

    fn checkpoint(&self) -> Result<Checkpoint, CheckpointError> {
        let state_data = bincode::serialize(&self.current_state)
            .map_err(|e| CheckpointError::Serialization(e.to_string()))?;

        Ok(Checkpoint::new(
            &self.protocol,
            self.role.clone(),
            format!("state_{}", self.current_state),
        )
        .with_data(state_data)
        .with_sequence(self.sequence))
    }

    fn restore(&mut self, checkpoint: &Checkpoint) -> Result<(), CheckpointError> {
        if checkpoint.protocol != self.protocol {
            return Err(CheckpointError::Incompatible(format!(
                "Protocol mismatch: expected {}, got {}",
                self.protocol, checkpoint.protocol
            )));
        }

        self.current_state = bincode::deserialize(&checkpoint.state_data)
            .map_err(|e| CheckpointError::Deserialization(e.to_string()))?;
        self.sequence = checkpoint.sequence;

        Ok(())
    }

    fn sequence(&self) -> u64 {
        self.sequence
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum TestLabel {
        Accept,
        Reject,
        Other,
    }

    impl LabelId for TestLabel {
        fn as_str(&self) -> &'static str {
            match self {
                TestLabel::Accept => "Accept",
                TestLabel::Reject => "Reject",
                TestLabel::Other => "Other",
            }
        }

        fn from_str(label: &str) -> Option<Self> {
            match label {
                "Accept" => Some(TestLabel::Accept),
                "Reject" => Some(TestLabel::Reject),
                "Other" => Some(TestLabel::Other),
                _ => None,
            }
        }
    }

    #[test]
    fn test_blocked_on_terminal() {
        assert!(BlockedOn::<TestLabel>::Complete.is_terminal());
        assert!(BlockedOn::<TestLabel>::Failed("error".to_string()).is_terminal());
        assert!(!BlockedOn::<TestLabel>::Send {
            to: RoleName::from_static("Server"),
            message_type: "Request".to_string(),
        }
        .is_terminal());
    }

    #[test]
    fn test_linear_state_machine() {
        let states = vec![
            BlockedOn::Send {
                to: RoleName::from_static("Server"),
                message_type: "Request".to_string(),
            },
            BlockedOn::Recv {
                from: RoleName::from_static("Server"),
                expected_types: vec!["Response".to_string()],
            },
        ];

        let mut sm = LinearStateMachine::<TestLabel>::new(
            "TestProto",
            RoleName::from_static("Client"),
            states,
        );

        assert!(sm.blocked_on().is_send());

        // Create a send envelope
        let send_env = super::super::envelope::ProtocolEnvelope::builder()
            .protocol("TestProto")
            .sender(RoleName::from_static("Client"))
            .recipient(RoleName::from_static("Server"))
            .message_type("Request")
            .payload(vec![])
            .build()
            .unwrap();

        let result = sm.step(StepInput::send(send_env.clone()));
        assert!(result.is_ok());
        assert!(matches!(result.unwrap(), StepOutput::Sent(_)));

        assert!(sm.blocked_on().is_recv());

        // Create a receive envelope
        let recv_env = super::super::envelope::ProtocolEnvelope::builder()
            .protocol("TestProto")
            .sender(RoleName::from_static("Server"))
            .recipient(RoleName::from_static("Client"))
            .message_type("Response")
            .payload(vec![])
            .build()
            .unwrap();

        let result = sm.step(StepInput::recv(recv_env));
        assert!(result.is_ok());

        assert!(sm.blocked_on().is_terminal());
    }

    #[test]
    fn test_checkpoint_roundtrip() {
        let states = vec![BlockedOn::Send {
            to: RoleName::from_static("Server"),
            message_type: "Msg".to_string(),
        }];

        let sm =
            LinearStateMachine::<TestLabel>::new("Proto", RoleName::from_static("Client"), states);
        let checkpoint = sm.checkpoint().unwrap();

        let bytes = checkpoint.to_bytes().unwrap();
        let restored = Checkpoint::from_bytes(&bytes).unwrap();

        assert_eq!(checkpoint.protocol, restored.protocol);
        assert_eq!(checkpoint.sequence, restored.sequence);
    }

    #[test]
    fn test_choice_validation() {
        let states = vec![BlockedOn::Choice {
            branches: vec![TestLabel::Accept, TestLabel::Reject],
        }];

        let mut sm =
            LinearStateMachine::<TestLabel>::new("Proto", RoleName::from_static("Client"), states);

        // Invalid choice should fail
        let result = sm.step(StepInput::choice(TestLabel::Other));
        assert!(result.is_err());

        // Valid choice should succeed
        let result = sm.step(StepInput::choice(TestLabel::Accept));
        assert!(result.is_ok());
    }
}
