//! Canonical heap encoding utilities.
//!
//! The runtime heap uses a heap-local canonical binary encoding.
//! This encoding is deterministic, versioned, and complete for all
//! semantically relevant fields in the current heap resource model.

/// Heap encoding magic bytes.
pub const HEAP_ENCODING_MAGIC: [u8; 4] = *b"TTHP";

/// Heap encoding format version.
pub const HEAP_ENCODING_VERSION: u16 = 1;

const TAG_MESSAGE_PAYLOAD: u8 = 0x10;
const TAG_CHANNEL_STATE: u8 = 0x20;
const TAG_MESSAGE: u8 = 0x30;
const TAG_RESOURCE_CHANNEL: u8 = 0x40;
const TAG_RESOURCE_MESSAGE: u8 = 0x41;
const TAG_RESOURCE_SESSION: u8 = 0x42;
const TAG_RESOURCE_VALUE: u8 = 0x43;
const TAG_RESOURCE_ID_PREIMAGE: u8 = 0x50;
const TAG_RESOURCE_LEAF_PREIMAGE: u8 = 0x51;
const TAG_NULLIFIER_LEAF_PREIMAGE: u8 = 0x52;
const TAG_MERKLE_NODE_PREIMAGE: u8 = 0x53;
const TAG_HEAP_COMMITMENT_PREIMAGE: u8 = 0x54;

/// Canonical heap encoding boundary.
///
/// Types that participate in heap resource identity and commitments encode
/// themselves through this trait.
pub trait CanonicalHeapEncoding {
    /// Append the canonical body for this value.
    fn encode_canonical_body(&self, encoder: &mut CanonicalHeapEncoder);

    /// The canonical tag for this value.
    fn canonical_tag(&self) -> u8;

    /// Encode this value to canonical bytes.
    fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut encoder = CanonicalHeapEncoder::new(self.canonical_tag());
        self.encode_canonical_body(&mut encoder);
        encoder.finish()
    }
}

/// Minimal binary encoder for canonical heap values.
#[derive(Debug, Clone, Default)]
pub struct CanonicalHeapEncoder {
    bytes: Vec<u8>,
}

impl CanonicalHeapEncoder {
    /// Create a new canonical encoder with the shared heap prelude.
    pub fn new(tag: u8) -> Self {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&HEAP_ENCODING_MAGIC);
        bytes.extend_from_slice(&HEAP_ENCODING_VERSION.to_le_bytes());
        bytes.push(tag);
        Self { bytes }
    }

    /// Append a nested canonical value.
    pub fn nested<T: CanonicalHeapEncoding>(&mut self, value: &T) {
        self.bytes.extend_from_slice(&value.to_canonical_bytes());
    }

    /// Append a UTF-8 string with a length prefix.
    pub fn string(&mut self, value: &str) {
        self.bytes
            .extend_from_slice(&(value.len() as u32).to_le_bytes());
        self.bytes.extend_from_slice(value.as_bytes());
    }

    /// Append a byte slice with a length prefix.
    pub fn bytes(&mut self, value: &[u8]) {
        self.bytes
            .extend_from_slice(&(value.len() as u32).to_le_bytes());
        self.bytes.extend_from_slice(value);
    }

    /// Append a `u32`.
    pub fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    /// Append a `u64`.
    pub fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    /// Finish encoding.
    pub fn finish(self) -> Vec<u8> {
        self.bytes
    }
}

pub(crate) const fn tag_message_payload() -> u8 {
    TAG_MESSAGE_PAYLOAD
}

pub(crate) const fn tag_channel_state() -> u8 {
    TAG_CHANNEL_STATE
}

pub(crate) const fn tag_message() -> u8 {
    TAG_MESSAGE
}

pub(crate) const fn tag_resource_channel() -> u8 {
    TAG_RESOURCE_CHANNEL
}

pub(crate) const fn tag_resource_message() -> u8 {
    TAG_RESOURCE_MESSAGE
}

pub(crate) const fn tag_resource_session() -> u8 {
    TAG_RESOURCE_SESSION
}

pub(crate) const fn tag_resource_value() -> u8 {
    TAG_RESOURCE_VALUE
}

/// Build the tagged preimage for `ResourceId` derivation.
pub fn resource_id_preimage(resource_bytes: &[u8], counter: u64) -> Vec<u8> {
    let mut encoder = CanonicalHeapEncoder::new(TAG_RESOURCE_ID_PREIMAGE);
    encoder.bytes(resource_bytes);
    encoder.u64(counter);
    encoder.finish()
}

/// Build the tagged preimage for an active-resource Merkle leaf.
pub fn resource_leaf_preimage(resource_id_bytes: &[u8], resource_bytes: &[u8]) -> Vec<u8> {
    let mut encoder = CanonicalHeapEncoder::new(TAG_RESOURCE_LEAF_PREIMAGE);
    encoder.bytes(resource_id_bytes);
    encoder.bytes(resource_bytes);
    encoder.finish()
}

/// Build the tagged preimage for a nullifier Merkle leaf.
pub fn nullifier_leaf_preimage(resource_id_bytes: &[u8]) -> Vec<u8> {
    let mut encoder = CanonicalHeapEncoder::new(TAG_NULLIFIER_LEAF_PREIMAGE);
    encoder.bytes(resource_id_bytes);
    encoder.finish()
}

/// Build the tagged preimage for a Merkle parent node.
pub fn merkle_node_preimage(left: &[u8], right: &[u8]) -> Vec<u8> {
    let mut encoder = CanonicalHeapEncoder::new(TAG_MERKLE_NODE_PREIMAGE);
    encoder.bytes(left);
    encoder.bytes(right);
    encoder.finish()
}

/// Build the tagged preimage for `HeapCommitment::hash()`.
pub fn heap_commitment_preimage(
    resource_root: &[u8],
    nullifier_root: &[u8],
    counter: u64,
) -> Vec<u8> {
    let mut encoder = CanonicalHeapEncoder::new(TAG_HEAP_COMMITMENT_PREIMAGE);
    encoder.bytes(resource_root);
    encoder.bytes(nullifier_root);
    encoder.u64(counter);
    encoder.finish()
}
