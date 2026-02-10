//! Protocol message envelope for structured message passing
//!
//! Envelopes wrap protocol messages with metadata for routing,
//! debugging, and simulation purposes.

use serde::{Deserialize, Serialize};

use crate::effects::RoleId;
use crate::identifiers::RoleName;
use crate::testing::clock::WallClock;

/// A protocol message envelope containing metadata and payload.
///
/// Envelopes provide a standard wrapper for messages that includes
/// routing information and can be inspected without deserializing
/// the payload.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolEnvelope {
    /// Name of the protocol this message belongs to.
    pub protocol: String,
    /// Role sending the message.
    pub from_role: RoleName,
    /// Role index if the sender is a parameterized role.
    pub from_index: Option<u32>,
    /// Role receiving the message.
    pub to_role: RoleName,
    /// Role index if the receiver is a parameterized role.
    pub to_index: Option<u32>,
    /// Type name of the message payload.
    pub message_type: String,
    /// Sequence number for ordering (per sender-receiver pair).
    pub sequence: u64,
    /// Timestamp when the message was created (nanoseconds since epoch).
    pub timestamp_ns: u64,
    /// Correlation ID for tracing across roles.
    pub correlation_id: Option<String>,
    /// The serialized message payload.
    pub payload: Vec<u8>,
}

impl ProtocolEnvelope {
    /// Create a new envelope builder.
    #[must_use]
    pub fn builder() -> EnvelopeBuilder {
        EnvelopeBuilder::default()
    }

    /// Get the payload size in bytes.
    #[must_use]
    pub fn payload_size(&self) -> usize {
        self.payload.len()
    }

    /// Check if this envelope is for a specific protocol.
    #[must_use]
    pub fn is_protocol(&self, name: &str) -> bool {
        self.protocol == name
    }

    /// Check if this envelope is from a specific role.
    #[must_use]
    pub fn is_from(&self, role: &RoleName) -> bool {
        &self.from_role == role
    }

    /// Check if this envelope is to a specific role.
    #[must_use]
    pub fn is_to(&self, role: &RoleName) -> bool {
        &self.to_role == role
    }

    /// Create a routing key for this envelope (useful for message queues).
    #[must_use]
    pub fn routing_key(&self) -> String {
        match (&self.from_index, &self.to_index) {
            (Some(fi), Some(ti)) => {
                format!(
                    "{}.{}[{}].{}[{}]",
                    self.protocol, self.from_role, fi, self.to_role, ti
                )
            }
            (Some(fi), None) => {
                format!(
                    "{}.{}[{}].{}",
                    self.protocol, self.from_role, fi, self.to_role
                )
            }
            (None, Some(ti)) => {
                format!(
                    "{}.{}.{}[{}]",
                    self.protocol, self.from_role, self.to_role, ti
                )
            }
            (None, None) => {
                format!("{}.{}.{}", self.protocol, self.from_role, self.to_role)
            }
        }
    }

    /// Serialize the envelope to bytes.
    pub fn to_bytes(&self) -> Result<Vec<u8>, EnvelopeError> {
        bincode::serialize(self).map_err(|e| EnvelopeError::Serialization(e.to_string()))
    }

    /// Deserialize an envelope from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, EnvelopeError> {
        bincode::deserialize(bytes).map_err(|e| EnvelopeError::Deserialization(e.to_string()))
    }
}

/// Builder for creating protocol envelopes.
///
/// # Determinism
///
/// By default, envelopes are created with `timestamp_ns = 0` for deterministic
/// simulation. Use `timestamp()` to set an explicit timestamp, or
/// `timestamp_now()` for production use with real wall-clock time.
#[derive(Debug, Default)]
pub struct EnvelopeBuilder {
    protocol: Option<String>,
    from_role: Option<RoleName>,
    from_index: Option<u32>,
    to_role: Option<RoleName>,
    to_index: Option<u32>,
    message_type: Option<String>,
    sequence: u64,
    timestamp_ns: Option<u64>,
    correlation_id: Option<String>,
    payload: Vec<u8>,
}

impl EnvelopeBuilder {
    /// Set the protocol name.
    #[must_use]
    pub fn protocol(mut self, protocol: impl Into<String>) -> Self {
        self.protocol = Some(protocol.into());
        self
    }

    /// Set the sender role.
    #[must_use]
    pub fn sender(mut self, role: RoleName) -> Self {
        self.from_role = Some(role);
        self
    }

    /// Set the sender role from a typed role identifier.
    #[must_use]
    pub fn sender_role<R: RoleId>(mut self, role: R) -> Self {
        self.from_role = Some(role.role_name());
        self.from_index = role.role_index();
        self
    }

    /// Set the sender role index.
    #[must_use]
    pub fn sender_index(mut self, index: u32) -> Self {
        self.from_index = Some(index);
        self
    }

    /// Set the receiver role.
    #[must_use]
    pub fn recipient(mut self, role: RoleName) -> Self {
        self.to_role = Some(role);
        self
    }

    /// Set the receiver role from a typed role identifier.
    #[must_use]
    pub fn recipient_role<R: RoleId>(mut self, role: R) -> Self {
        self.to_role = Some(role.role_name());
        self.to_index = role.role_index();
        self
    }

    /// Set the receiver role index.
    #[must_use]
    pub fn recipient_index(mut self, index: u32) -> Self {
        self.to_index = Some(index);
        self
    }

    /// Set the message type name.
    #[must_use]
    pub fn message_type(mut self, msg_type: impl Into<String>) -> Self {
        self.message_type = Some(msg_type.into());
        self
    }

    /// Set the sequence number.
    #[must_use]
    pub fn sequence(mut self, seq: u64) -> Self {
        self.sequence = seq;
        self
    }

    /// Set an explicit timestamp (nanoseconds since epoch).
    ///
    /// For deterministic simulation, use controlled timestamps (or leave unset
    /// to default to 0). For production contexts with real timestamps, use
    /// `SystemClock::timestamp_ns()` from the runtime module.
    #[must_use]
    pub fn timestamp(mut self, timestamp_ns: u64) -> Self {
        self.timestamp_ns = Some(timestamp_ns);
        self
    }

    /// Set timestamp from an injected wall-clock source.
    ///
    /// Use this instead of reading host time directly to keep determinism under
    /// explicit control in simulations/replays.
    #[must_use]
    pub fn timestamp_from<C: WallClock>(mut self, clock: &C) -> Self {
        self.timestamp_ns = Some(clock.now_unix_ns());
        self
    }

    /// Set the correlation ID.
    #[must_use]
    pub fn correlation_id(mut self, id: impl Into<String>) -> Self {
        self.correlation_id = Some(id.into());
        self
    }

    /// Set the payload bytes directly.
    #[must_use]
    pub fn payload(mut self, payload: Vec<u8>) -> Self {
        self.payload = payload;
        self
    }

    /// Serialize a message as the payload.
    pub fn payload_from<T: Serialize>(mut self, msg: &T) -> Result<Self, EnvelopeError> {
        self.payload =
            bincode::serialize(msg).map_err(|e| EnvelopeError::Serialization(e.to_string()))?;
        Ok(self)
    }

    /// Build the envelope.
    pub fn build(self) -> Result<ProtocolEnvelope, EnvelopeError> {
        let protocol = self
            .protocol
            .ok_or(EnvelopeError::MissingField(EnvelopeField::Protocol))?;
        let from_role = self
            .from_role
            .ok_or(EnvelopeError::MissingField(EnvelopeField::FromRole))?;
        let to_role = self
            .to_role
            .ok_or(EnvelopeError::MissingField(EnvelopeField::ToRole))?;
        let message_type = self
            .message_type
            .ok_or(EnvelopeError::MissingField(EnvelopeField::MessageType))?;

        // Default to 0 for deterministic simulation; use timestamp() or timestamp_now()
        // to set an explicit value.
        let timestamp_ns = self.timestamp_ns.unwrap_or(0);

        Ok(ProtocolEnvelope {
            protocol,
            from_role,
            from_index: self.from_index,
            to_role,
            to_index: self.to_index,
            message_type,
            sequence: self.sequence,
            timestamp_ns,
            correlation_id: self.correlation_id,
            payload: self.payload,
        })
    }
}

/// Required fields for protocol envelopes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvelopeField {
    /// Protocol name field.
    Protocol,
    /// Sender role field.
    FromRole,
    /// Recipient role field.
    ToRole,
    /// Message type field.
    MessageType,
}

impl std::fmt::Display for EnvelopeField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvelopeField::Protocol => write!(f, "protocol"),
            EnvelopeField::FromRole => write!(f, "from_role"),
            EnvelopeField::ToRole => write!(f, "to_role"),
            EnvelopeField::MessageType => write!(f, "message_type"),
        }
    }
}

/// Errors that can occur when working with envelopes.
#[derive(Debug, thiserror::Error)]
pub enum EnvelopeError {
    /// A required field was not set.
    #[error("Missing required field: {0}")]
    MissingField(EnvelopeField),

    /// Serialization failed.
    #[error("Serialization error: {0}")]
    Serialization(String),

    /// Deserialization failed.
    #[error("Deserialization error: {0}")]
    Deserialization(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identifiers::RoleName;

    #[test]
    fn test_envelope_builder() {
        let envelope = ProtocolEnvelope::builder()
            .protocol("TestProtocol")
            .sender(RoleName::from_static("Client"))
            .recipient(RoleName::from_static("Server"))
            .message_type("Request")
            .sequence(1)
            .payload(vec![1, 2, 3])
            .build()
            .unwrap();

        assert_eq!(envelope.protocol, "TestProtocol");
        assert_eq!(envelope.from_role.as_str(), "Client");
        assert_eq!(envelope.to_role.as_str(), "Server");
        assert_eq!(envelope.message_type, "Request");
        assert_eq!(envelope.sequence, 1);
        assert_eq!(envelope.payload, vec![1, 2, 3]);
    }

    #[test]
    fn test_routing_key() {
        let envelope = ProtocolEnvelope::builder()
            .protocol("Proto")
            .sender(RoleName::from_static("A"))
            .recipient(RoleName::from_static("B"))
            .message_type("Msg")
            .build()
            .unwrap();

        assert_eq!(envelope.routing_key(), "Proto.A.B");

        let indexed = ProtocolEnvelope::builder()
            .protocol("Proto")
            .sender(RoleName::from_static("Worker"))
            .sender_index(0)
            .recipient(RoleName::from_static("Manager"))
            .message_type("Msg")
            .build()
            .unwrap();

        assert_eq!(indexed.routing_key(), "Proto.Worker[0].Manager");
    }

    #[test]
    fn test_envelope_roundtrip() {
        let original = ProtocolEnvelope::builder()
            .protocol("Test")
            .sender(RoleName::from_static("A"))
            .recipient(RoleName::from_static("B"))
            .message_type("Msg")
            .payload(vec![1, 2, 3, 4, 5])
            .build()
            .unwrap();

        let bytes = original.to_bytes().unwrap();
        let restored = ProtocolEnvelope::from_bytes(&bytes).unwrap();

        assert_eq!(original.protocol, restored.protocol);
        assert_eq!(original.payload, restored.payload);
    }
}
