//! # Heap Module
//!
//! Explicit heap-based state management with nullifier tracking.
//!
//! ## Overview
//!
//! This module provides content-addressed resources and a deterministic heap
//! for managing protocol state. Key features:
//!
//! - **Hash-Policy Reuse**: Resource IDs use the shared `Hasher` abstraction
//! - **Nullifier Tracking**: Consumed resources are tracked to prevent double-spending
//! - **Deterministic Operations**: Same operations produce identical results
//! - **Functional and Mutable APIs**: Both persistent and in-place update paths exist
//!
//! ## Lean Correspondence
//!
//! Resource concepts correspond to `lean/Runtime/Resources/ResourceModel.lean`.
//! The heap abstraction is currently Rust-only.
//!
//! ## Example
//!
//! ```rust
//! use telltale_runtime::heap::{DefaultHeapHasher, Heap, Resource};
//!
//! // Create a new heap
//! let heap = Heap::<DefaultHeapHasher>::new();
//!
//! // Allocate a channel resource
//! let (channel_id, heap) = heap.alloc_channel("Alice", "Bob");
//!
//! // Allocate a message
//! let (msg_id, heap) = heap.alloc_message(
//!     "Alice", "Bob", "Ping", vec![1, 2, 3], 0
//! );
//!
//! // Read a resource
//! let resource = heap.read(&channel_id).unwrap();
//!
//! // Consume a resource (adds to nullifier set)
//! let heap = heap.consume(&msg_id).unwrap();
//!
//! // Resource is now nullified
//! assert!(heap.is_consumed(&msg_id));
//! ```

mod heap_impl;
mod encoding;
mod merkle;
mod resource;

pub use encoding::{
    CanonicalHeapEncoder, CanonicalHeapEncoding, HEAP_ENCODING_MAGIC, HEAP_ENCODING_VERSION,
};
pub use heap_impl::Heap;
pub use merkle::{
    merkle_node_hash, nullifier_leaf_hash, resource_leaf_hash, Direction, HeapCommitment,
    MerkleProof, MerkleTree, ProofStep,
};
pub use resource::{ChannelState, HeapError, Message, MessagePayload, Resource, ResourceId};
pub use telltale_types::{DefaultContentHasher as DefaultHeapHasher, Hasher};
