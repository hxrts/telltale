//! # Resource Types
//!
//! Content-addressed resources for the protocol heap.
//!
//! ## Overview
//!
//! This module defines content-addressed resources for heap-based state management.
//! Resources are immutable values identified by their content hash, enabling:
//! - Replay protection (can't process same message twice)
//! - Byzantine fault detection (prove protocol violations)
//! - ZK compatibility (state is a Merkle tree)
//! - Deterministic execution (heap operations are pure)
//!
//! ## Lean Correspondence
//!
//! This module corresponds to `lean/Rumpsteak/Protocol/Resource.lean`:
//! - `ResourceId` ↔ Lean's `ResourceId`
//! - `Resource` ↔ Lean's `Resource`
//! - `HeapError` ↔ Lean's `HeapError`

use sha2::{Digest, Sha256};
use std::fmt;

/// Unique identifier for heap-allocated resources.
///
/// ResourceId is derived from the content hash of the resource,
/// combined with an allocation counter to ensure uniqueness even
/// for identical content.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ResourceId {
    /// The content hash (SHA-256)
    pub hash: [u8; 32],
    /// Allocation counter (for uniqueness of identical content)
    pub counter: u64,
}

impl ResourceId {
    /// Create a new ResourceId from hash and counter.
    pub fn new(hash: [u8; 32], counter: u64) -> Self {
        Self { hash, counter }
    }

    /// Create a ResourceId from a resource and allocation counter.
    pub fn from_resource(resource: &Resource, counter: u64) -> Self {
        let content_bytes = resource.to_bytes();
        let counter_bytes = counter.to_le_bytes();

        let mut hasher = Sha256::new();
        hasher.update(content_bytes);
        hasher.update(counter_bytes);
        let hash: [u8; 32] = hasher.finalize().into();

        Self { hash, counter }
    }

    /// Display as a short hex string.
    pub fn to_short_hex(&self) -> String {
        let hex: String = self.hash[..4]
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect();
        format!("{}:{}", hex, self.counter)
    }
}

impl fmt::Debug for ResourceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ResourceId({})", self.to_short_hex())
    }
}

impl fmt::Display for ResourceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_short_hex())
    }
}

impl PartialOrd for ResourceId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ResourceId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.hash.cmp(&other.hash) {
            std::cmp::Ordering::Equal => self.counter.cmp(&other.counter),
            ord => ord,
        }
    }
}

/// A message payload with label and data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MessagePayload {
    /// The message label
    pub label: String,
    /// The serialized payload
    pub payload: Vec<u8>,
}

impl MessagePayload {
    /// Create a new message payload.
    pub fn new(label: impl Into<String>, payload: Vec<u8>) -> Self {
        Self {
            label: label.into(),
            payload,
        }
    }
}

/// State of a communication channel between two roles.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChannelState {
    /// The sender role
    pub sender: String,
    /// The receiver role
    pub receiver: String,
    /// Pending messages in the channel
    pub queue: Vec<MessagePayload>,
}

impl ChannelState {
    /// Create a new empty channel.
    pub fn new(sender: impl Into<String>, receiver: impl Into<String>) -> Self {
        Self {
            sender: sender.into(),
            receiver: receiver.into(),
            queue: Vec::new(),
        }
    }

    /// Get the number of pending messages.
    pub fn queue_size(&self) -> usize {
        self.queue.len()
    }
}

/// A message resource representing a message in transit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message {
    /// Source role
    pub source: String,
    /// Destination role
    pub dest: String,
    /// Message content
    pub content: MessagePayload,
    /// Sequence number for ordering
    pub seq_no: u64,
}

impl Message {
    /// Create a new message.
    pub fn new(
        source: impl Into<String>,
        dest: impl Into<String>,
        label: impl Into<String>,
        payload: Vec<u8>,
        seq_no: u64,
    ) -> Self {
        Self {
            source: source.into(),
            dest: dest.into(),
            content: MessagePayload::new(label, payload),
            seq_no,
        }
    }
}

/// Resource kinds that can be allocated on the heap.
///
/// All resources are immutable and content-addressed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resource {
    /// A communication channel between roles
    Channel(ChannelState),
    /// A message in transit
    Message(Message),
    /// Current session state for a role
    Session {
        /// The role name
        role: String,
        /// Hash of the session type (LocalTypeR)
        type_hash: u64,
    },
    /// An arbitrary value
    Value {
        /// Type tag
        tag: String,
        /// Serialized value
        data: Vec<u8>,
    },
}

impl Resource {
    /// Create a channel resource.
    pub fn channel(sender: impl Into<String>, receiver: impl Into<String>) -> Self {
        Resource::Channel(ChannelState::new(sender, receiver))
    }

    /// Create a message resource.
    pub fn message(
        source: impl Into<String>,
        dest: impl Into<String>,
        label: impl Into<String>,
        payload: Vec<u8>,
        seq_no: u64,
    ) -> Self {
        Resource::Message(Message::new(source, dest, label, payload, seq_no))
    }

    /// Create a session resource.
    pub fn session(role: impl Into<String>, type_hash: u64) -> Self {
        Resource::Session {
            role: role.into(),
            type_hash,
        }
    }

    /// Create a value resource.
    pub fn value(tag: impl Into<String>, data: Vec<u8>) -> Self {
        Resource::Value {
            tag: tag.into(),
            data,
        }
    }

    /// Get the resource kind as a string.
    pub fn kind(&self) -> &'static str {
        match self {
            Resource::Channel(_) => "channel",
            Resource::Message(_) => "message",
            Resource::Session { .. } => "session",
            Resource::Value { .. } => "value",
        }
    }

    /// Serialize the resource to bytes for content addressing.
    ///
    /// This is used for computing the content hash. A production
    /// implementation would use DAG-CBOR or similar canonical serialization.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();

        match self {
            Resource::Channel(cs) => {
                bytes.extend_from_slice(b"channel:");
                bytes.extend_from_slice(cs.sender.as_bytes());
                bytes.push(0);
                bytes.extend_from_slice(cs.receiver.as_bytes());
                bytes.push(0);
                bytes.extend_from_slice(&cs.queue.len().to_le_bytes());
            }
            Resource::Message(msg) => {
                bytes.extend_from_slice(b"message:");
                bytes.extend_from_slice(msg.source.as_bytes());
                bytes.push(0);
                bytes.extend_from_slice(msg.dest.as_bytes());
                bytes.push(0);
                bytes.extend_from_slice(msg.content.label.as_bytes());
                bytes.push(0);
                bytes.extend_from_slice(&msg.seq_no.to_le_bytes());
            }
            Resource::Session { role, type_hash } => {
                bytes.extend_from_slice(b"session:");
                bytes.extend_from_slice(role.as_bytes());
                bytes.push(0);
                bytes.extend_from_slice(&type_hash.to_le_bytes());
            }
            Resource::Value { tag, data } => {
                bytes.extend_from_slice(b"value:");
                bytes.extend_from_slice(tag.as_bytes());
                bytes.push(0);
                bytes.extend_from_slice(&data.len().to_le_bytes());
                bytes.extend_from_slice(data);
            }
        }

        bytes
    }
}

impl fmt::Display for Resource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Resource({})", self.kind())
    }
}

/// Errors that can occur during heap operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeapError {
    /// Resource not found in heap
    NotFound(ResourceId),
    /// Resource already consumed (nullified)
    AlreadyConsumed(ResourceId),
    /// Resource already exists with this ID
    AlreadyExists(ResourceId),
    /// Invalid resource type for operation
    TypeMismatch { expected: String, got: String },
    /// Generic error with message
    Other(String),
}

impl fmt::Display for HeapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HeapError::NotFound(rid) => write!(f, "Resource not found: {}", rid),
            HeapError::AlreadyConsumed(rid) => write!(f, "Resource already consumed: {}", rid),
            HeapError::AlreadyExists(rid) => write!(f, "Resource already exists: {}", rid),
            HeapError::TypeMismatch { expected, got } => {
                write!(f, "Type mismatch: expected {}, got {}", expected, got)
            }
            HeapError::Other(msg) => write!(f, "{}", msg),
        }
    }
}

impl std::error::Error for HeapError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resource_id_creation() {
        let r1 = Resource::channel("Alice", "Bob");
        let r2 = Resource::channel("Alice", "Bob");

        let id1 = ResourceId::from_resource(&r1, 0);
        let id2 = ResourceId::from_resource(&r2, 0);
        let id3 = ResourceId::from_resource(&r1, 1);

        // Same resource, same counter → same ID
        assert_eq!(id1, id2);
        // Same resource, different counter → different ID
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_resource_id_ordering() {
        let r = Resource::channel("Alice", "Bob");
        let id1 = ResourceId::from_resource(&r, 0);
        let id2 = ResourceId::from_resource(&r, 1);

        // Same hash, different counter
        assert!(id1 < id2);
    }

    #[test]
    fn test_resource_to_bytes() {
        let channel = Resource::channel("Alice", "Bob");
        let bytes = channel.to_bytes();
        assert!(bytes.starts_with(b"channel:"));

        let msg = Resource::message("Alice", "Bob", "Hello", vec![1, 2, 3], 42);
        let bytes = msg.to_bytes();
        assert!(bytes.starts_with(b"message:"));
    }

    #[test]
    fn test_message_creation() {
        let msg = Message::new("Alice", "Bob", "Ping", vec![1, 2, 3], 1);
        assert_eq!(msg.source, "Alice");
        assert_eq!(msg.dest, "Bob");
        assert_eq!(msg.content.label, "Ping");
        assert_eq!(msg.seq_no, 1);
    }

    #[test]
    fn test_channel_state() {
        let mut channel = ChannelState::new("Alice", "Bob");
        assert_eq!(channel.queue_size(), 0);

        channel.queue.push(MessagePayload::new("Test", vec![]));
        assert_eq!(channel.queue_size(), 1);
    }

    #[test]
    fn test_heap_error_display() {
        let rid = ResourceId::new([0u8; 32], 42);
        let err = HeapError::NotFound(rid);
        assert!(err.to_string().contains("not found"));
    }
}
