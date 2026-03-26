//! Runtime support for choreographic protocol execution
//!
//! This module provides:
//!
//! - Cross-platform async spawning utilities
//!
//! # Architecture
//!
//! The runtime module provides the infrastructure for executing generated
//! protocol code on native and WASM targets. Execution itself is modeled
//! through the effect system in [`crate::effects`]; this module is only the
//! platform/runtime support layer.
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    Generated Code                            │
//! │          Effect Programs + ChoreoHandler                    │
//! └─────────────────────────────────────────────────────────────┘
//!                              │
//!                              ▼
//! ┌─────────────────────────────────────────────────────────────┐
//! │                   Runtime Utilities                          │
//! │          spawn(), spawn_local(), clocks                      │
//! └─────────────────────────────────────────────────────────────┘
//!                              │
//!                              ▼
//! ┌─────────────────────────────────────────────────────────────┐
//! │                 Transport Implementation                     │
//! │              Handlers / Transport Layers                    │
//! └─────────────────────────────────────────────────────────────┘
//! ```

pub mod clock;
pub mod spawn;
pub mod sync;

// Re-export main types
pub use clock::{SystemClock, SystemRng};
pub use spawn::{spawn, spawn_local, AsyncRuntime};
