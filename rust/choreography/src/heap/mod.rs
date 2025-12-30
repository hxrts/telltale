//! # Heap Module
//!
//! Explicit heap-based state management with nullifier tracking.
//!
//! ## Overview
//!
//! This module provides content-addressed resources and a deterministic heap
//! for managing protocol state. Key features:
//!
//! - **Content Addressing**: Resources are identified by their content hash
//! - **Nullifier Tracking**: Consumed resources are tracked to prevent double-spending
//! - **Deterministic Operations**: Same operations produce identical results
//! - **Immutable API**: All operations return new heaps (functional style)
//!
//! ## Lean Correspondence
//!
//! This module corresponds to the Lean formalization:
//! - `lean/Rumpsteak/Protocol/Resource.lean` - Resource types
//! - `lean/Rumpsteak/Protocol/Heap.lean` - Heap operations
//!
//! ## Example
//!
//! ```rust
//! use rumpsteak_aura_choreography::heap::{Heap, Resource};
//!
//! // Create a new heap
//! let heap = Heap::new();
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
mod merkle;
mod resource;

pub use heap_impl::Heap;
pub use merkle::{Direction, HeapCommitment, MerkleProof, MerkleTree, ProofStep};
pub use resource::{ChannelState, HeapError, Message, MessagePayload, Resource, ResourceId};
