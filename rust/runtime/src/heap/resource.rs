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
//! Resource concepts correspond to `lean/Runtime/Resources/ResourceModel.lean`.
//! The specific Rust types (`ResourceId`, `Resource`, `HeapError`) are Rust-only.

use std::fmt;
use std::hash::{Hash, Hasher as StdHasher};
use std::marker::PhantomData;
use telltale_types::{DefaultContentHasher, Hasher};

/// Unique identifier for heap-allocated resources.
///
/// ResourceId is derived from the content hash of the resource,
/// combined with an allocation counter to ensure uniqueness even
/// for identical content.
#[derive(Clone)]
pub struct ResourceId<H: Hasher = DefaultContentHasher> {
    /// The hashed resource identity
    hash: H::Digest,
    /// Allocation counter (for uniqueness of identical content)
    counter: u64,
    _hasher: PhantomData<H>,
}

impl<H: Hasher> ResourceId<H> {
    /// Create a new ResourceId from hash and counter.
    pub fn new(hash: H::Digest, counter: u64) -> Self {
        Self {
            hash,
            counter,
            _hasher: PhantomData,
        }
    }

    /// Create a ResourceId from a resource and allocation counter.
    pub fn from_resource(resource: &Resource, counter: u64) -> Self {
        let content_bytes = resource.to_bytes();
        let counter_bytes = counter.to_le_bytes();
        let mut bytes = Vec::with_capacity(content_bytes.len() + counter_bytes.len());
        bytes.extend_from_slice(&content_bytes);
        bytes.extend_from_slice(&counter_bytes);
        let hash = H::digest(&bytes);

        Self {
            hash,
            counter,
            _hasher: PhantomData,
        }
    }

    /// Display as a short hex string.
    pub fn to_short_hex(&self) -> String {
        let hex: String = self.hash.as_ref()[..4]
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect();
        format!("{}:{}", hex, self.counter)
    }

    /// Get the raw hash bytes.
    #[must_use]
    pub fn hash(&self) -> &H::Digest {
        &self.hash
    }

    /// Get the raw hash bytes as a slice.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.hash.as_ref()
    }

    /// Get the allocation counter.
    #[must_use]
    pub fn counter(&self) -> u64 {
        self.counter
    }
}

impl<H: Hasher> PartialEq for ResourceId<H> {
    fn eq(&self, other: &Self) -> bool {
        self.hash.as_ref() == other.hash.as_ref() && self.counter == other.counter
    }
}

impl<H: Hasher> Eq for ResourceId<H> {}

impl<H: Hasher> Hash for ResourceId<H> {
    fn hash<S: StdHasher>(&self, state: &mut S) {
        self.hash.as_ref().hash(state);
        self.counter.hash(state);
    }
}

impl<H: Hasher> fmt::Debug for ResourceId<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ResourceId<{}>({})",
            H::algorithm_name(),
            self.to_short_hex()
        )
    }
}

impl<H: Hasher> fmt::Display for ResourceId<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_short_hex())
    }
}

impl<H: Hasher> PartialOrd for ResourceId<H> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<H: Hasher> Ord for ResourceId<H> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.hash.as_ref().cmp(other.hash.as_ref()) {
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
#[derive(Clone, PartialEq, Eq)]
pub enum HeapError<H: Hasher = DefaultContentHasher> {
    /// Resource not found in heap
    NotFound(ResourceId<H>),
    /// Resource already consumed (nullified)
    AlreadyConsumed(ResourceId<H>),
    /// Resource already exists with this ID
    AlreadyExists(ResourceId<H>),
    /// Invalid resource type for operation
    TypeMismatch { expected: String, got: String },
    /// Generic error with message
    Other(String),
}

impl<H: Hasher> fmt::Debug for HeapError<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HeapError::NotFound(rid) => f.debug_tuple("NotFound").field(rid).finish(),
            HeapError::AlreadyConsumed(rid) => f.debug_tuple("AlreadyConsumed").field(rid).finish(),
            HeapError::AlreadyExists(rid) => f.debug_tuple("AlreadyExists").field(rid).finish(),
            HeapError::TypeMismatch { expected, got } => f
                .debug_struct("TypeMismatch")
                .field("expected", expected)
                .field("got", got)
                .finish(),
            HeapError::Other(msg) => f.debug_tuple("Other").field(msg).finish(),
        }
    }
}

impl<H: Hasher> fmt::Display for HeapError<H> {
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

impl<H: Hasher> std::error::Error for HeapError<H> {}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::{Blake3Hasher, DefaultContentHasher, Hasher};

    #[test]
    fn test_resource_id_creation() {
        let r1 = Resource::channel("Alice", "Bob");
        let r2 = Resource::channel("Alice", "Bob");

        let id1 = ResourceId::<DefaultContentHasher>::from_resource(&r1, 0);
        let id2 = ResourceId::<DefaultContentHasher>::from_resource(&r2, 0);
        let id3 = ResourceId::<DefaultContentHasher>::from_resource(&r1, 1);

        // Same resource, same counter → same ID
        assert_eq!(id1, id2);
        // Same resource, different counter → different ID
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_resource_id_ordering() {
        let id1 = ResourceId::<DefaultContentHasher>::new([0u8; 32], 0);
        let id2 = ResourceId::<DefaultContentHasher>::new([0u8; 32], 1);

        // When the digest matches, ordering falls back to the counter.
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
        let rid = ResourceId::<DefaultContentHasher>::new([0u8; 32], 42);
        let err = HeapError::NotFound(rid);
        assert!(err.to_string().contains("not found"));
    }

    #[test]
    fn test_default_heap_hasher_is_blake3() {
        let expected = Blake3Hasher::digest(b"heap");
        let actual = DefaultContentHasher::digest(b"heap");
        assert_eq!(expected, actual);
    }
}
