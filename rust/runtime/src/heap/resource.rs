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
//! Resource concepts correspond to `lean/Runtime/Resources/HeapModel.lean`.
//! The Lean parity lane mirrors canonical bytes and tagged preimages for the
//! resource family. The concrete Rust digest type and heap error surface remain
//! operational Rust artifacts.

use super::encoding::{
    resource_id_preimage,
    tag_channel_state, tag_message, tag_message_payload, tag_resource_channel,
    tag_resource_message, tag_resource_session, tag_resource_value, CanonicalHeapEncoder,
    CanonicalHeapEncoding,
};
use std::fmt;
use std::hash::{Hash, Hasher as StdHasher};
use std::marker::PhantomData;
use telltale_types::{DefaultContentHasher, Hasher};

/// Unique identifier for heap-allocated resources.
///
/// `ResourceId` is derived from a tagged hash preimage that contains the
/// canonical resource encoding and the allocation counter.
/// This keeps repeated allocations of identical semantic resources distinct.
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

    /// Create a `ResourceId` from a resource and allocation counter.
    ///
    /// The hasher consumes a tagged preimage that contains the canonical
    /// resource bytes and the little-endian counter.
    pub fn from_resource(resource: &Resource, counter: u64) -> Self {
        let content_bytes = resource.canonical_bytes();
        let preimage = resource_id_preimage(&content_bytes, counter);
        let hash = H::digest(&preimage);

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

impl CanonicalHeapEncoding for MessagePayload {
    fn encode_canonical_body(&self, encoder: &mut CanonicalHeapEncoder) {
        encoder.string(&self.label);
        encoder.bytes(&self.payload);
    }

    fn canonical_tag(&self) -> u8 {
        tag_message_payload()
    }
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

impl CanonicalHeapEncoding for ChannelState {
    fn encode_canonical_body(&self, encoder: &mut CanonicalHeapEncoder) {
        encoder.string(&self.sender);
        encoder.string(&self.receiver);
        encoder.u32(self.queue.len() as u32);
        for payload in &self.queue {
            encoder.nested(payload);
        }
    }

    fn canonical_tag(&self) -> u8 {
        tag_channel_state()
    }
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

impl CanonicalHeapEncoding for Message {
    fn encode_canonical_body(&self, encoder: &mut CanonicalHeapEncoder) {
        encoder.string(&self.source);
        encoder.string(&self.dest);
        encoder.nested(&self.content);
        encoder.u64(self.seq_no);
    }

    fn canonical_tag(&self) -> u8 {
        tag_message()
    }
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

    /// Serialize the resource to canonical heap bytes.
    ///
    /// The heap derives resource identity and Merkle leaves from this
    /// versioned canonical encoding.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        self.to_canonical_bytes()
    }
}

impl CanonicalHeapEncoding for Resource {
    fn encode_canonical_body(&self, encoder: &mut CanonicalHeapEncoder) {
        match self {
            Resource::Channel(channel) => encoder.nested(channel),
            Resource::Message(message) => encoder.nested(message),
            Resource::Session { role, type_hash } => {
                encoder.string(role);
                encoder.u64(*type_hash);
            }
            Resource::Value { tag, data } => {
                encoder.string(tag);
                encoder.bytes(data);
            }
        }
    }

    fn canonical_tag(&self) -> u8 {
        match self {
            Resource::Channel(_) => tag_resource_channel(),
            Resource::Message(_) => tag_resource_message(),
            Resource::Session { .. } => tag_resource_session(),
            Resource::Value { .. } => tag_resource_value(),
        }
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
    use crate::heap::{HEAP_ENCODING_MAGIC, HEAP_ENCODING_VERSION};
    use telltale_types::{Blake3Hasher, DefaultContentHasher, Hasher};

    fn to_hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{:02x}", byte)).collect()
    }

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
    fn test_resource_id_fixed_vector() {
        let resource = Resource::message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
        let resource_id = ResourceId::<DefaultContentHasher>::from_resource(&resource, 1);

        assert_eq!(
            to_hex(resource.canonical_bytes().as_slice()),
            "545448500100415454485001003005000000416c69636503000000426f62545448500100100500000048656c6c6f030000000102030700000000000000"
        );
        assert_eq!(
            to_hex(resource_id.as_bytes()),
            "5a22a0e61e5faa3ea4c2bee86a92761eea62364727a77a4ed7c3a24c456afd8e"
        );
    }

    #[test]
    fn test_resource_id_ordering() {
        let id1 = ResourceId::<DefaultContentHasher>::new([0u8; 32], 0);
        let id2 = ResourceId::<DefaultContentHasher>::new([0u8; 32], 1);

        // When the digest matches, ordering falls back to the counter.
        assert!(id1 < id2);
    }

    #[test]
    fn test_resource_canonical_bytes_use_versioned_encoding() {
        let channel = Resource::channel("Alice", "Bob");
        let bytes = channel.canonical_bytes();
        assert_eq!(&bytes[..4], &HEAP_ENCODING_MAGIC);
        assert_eq!(&bytes[4..6], &HEAP_ENCODING_VERSION.to_le_bytes());

        let message = Resource::message("Alice", "Bob", "Hello", vec![1, 2, 3], 42);
        let bytes = message.canonical_bytes();
        assert_eq!(&bytes[..4], &HEAP_ENCODING_MAGIC);
        assert_eq!(&bytes[4..6], &HEAP_ENCODING_VERSION.to_le_bytes());
    }

    #[test]
    fn test_channel_encoding_includes_full_queue_payloads() {
        let channel = Resource::Channel(ChannelState {
            sender: "Alice".into(),
            receiver: "Bob".into(),
            queue: vec![
                MessagePayload::new("Ping", vec![1, 2, 3]),
                MessagePayload::new("Pong", vec![4, 5, 6]),
            ],
        });
        let bytes = channel.canonical_bytes();

        assert!(bytes.windows(4).any(|window| window == b"Ping"));
        assert!(bytes.windows(4).any(|window| window == b"Pong"));
        assert!(bytes.windows(3).any(|window| window == [1, 2, 3]));
        assert!(bytes.windows(3).any(|window| window == [4, 5, 6]));
    }

    #[test]
    fn test_message_encoding_includes_full_payload_bytes() {
        let message = Resource::message("Alice", "Bob", "Hello", vec![7, 8, 9, 10], 42);
        let bytes = message.canonical_bytes();

        assert!(bytes.windows(5).any(|window| window == b"Hello"));
        assert!(bytes.windows(4).any(|window| window == [7, 8, 9, 10]));
    }

    #[test]
    fn test_canonical_encoding_is_stable_per_resource_kind() {
        let channel = Resource::Channel(ChannelState {
            sender: "Alice".into(),
            receiver: "Bob".into(),
            queue: vec![MessagePayload::new("Ping", vec![1, 2, 3])],
        });
        let message = Resource::message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
        let session = Resource::session("Alice", 12345);
        let value = Resource::value("blob", vec![9, 8, 7]);

        assert_eq!(channel.canonical_bytes(), channel.canonical_bytes());
        assert_eq!(message.canonical_bytes(), message.canonical_bytes());
        assert_eq!(session.canonical_bytes(), session.canonical_bytes());
        assert_eq!(value.canonical_bytes(), value.canonical_bytes());
    }

    #[test]
    fn test_canonical_encoding_distinguishes_semantic_changes() {
        let left = Resource::message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
        let right = Resource::message("Alice", "Bob", "Hello", vec![1, 2, 4], 7);

        assert_ne!(left.canonical_bytes(), right.canonical_bytes());
    }

    #[test]
    fn test_canonical_encoding_matches_for_semantically_identical_values() {
        let left = Resource::Channel(ChannelState {
            sender: "Alice".into(),
            receiver: "Bob".into(),
            queue: vec![MessagePayload::new("Ping", vec![1, 2, 3])],
        });
        let right = Resource::Channel(ChannelState {
            sender: "Alice".into(),
            receiver: "Bob".into(),
            queue: vec![MessagePayload::new("Ping", vec![1, 2, 3])],
        });

        assert_eq!(left.canonical_bytes(), right.canonical_bytes());
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
