//! Runtime support for choreographic protocol execution
//!
//! This module provides:
//!
//! - [`ChoreographicAdapter`] trait for simplified protocol execution
//! - Cross-platform async spawning utilities
//! - Protocol execution context and metadata
//!
//! # Architecture
//!
//! The runtime module provides the infrastructure for executing generated
//! protocol code. The key abstraction is [`ChoreographicAdapter`], which
//! provides a simpler interface than the effect handler system for use
//! by generated `run_{role}` functions.
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    Generated Code                            │
//! │  run_client(), run_server(), execute_as()                   │
//! └─────────────────────────────────────────────────────────────┘
//!                              │
//!                              ▼
//! ┌─────────────────────────────────────────────────────────────┐
//! │                ChoreographicAdapter Trait                    │
//! │  send(), recv(), broadcast(), collect()                     │
//! └─────────────────────────────────────────────────────────────┘
//!                              │
//!                              ▼
//! ┌─────────────────────────────────────────────────────────────┐
//! │                 Transport Implementation                     │
//! │  ChannelAdapter, NetworkAdapter, SimulatedAdapter           │
//! └─────────────────────────────────────────────────────────────┘
//! ```

pub mod adapter;
pub mod clock;
pub mod spawn;
pub mod sync;
pub mod test_adapter;

// Re-export main types
pub use adapter::{
    ChoiceLabel, ChoreographicAdapter, ChoreographicAdapterExt, ExecutionMetadata, Message,
    ProtocolContext, ProtocolOutput,
};
pub use clock::{SystemClock, SystemRng};
pub use spawn::{spawn, spawn_local, AsyncRuntime};
pub use test_adapter::TestAdapter;
