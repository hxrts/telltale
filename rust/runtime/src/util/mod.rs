//! Utility layer for choreographic protocol execution.
//!
//! This module provides small platform-facing helpers used by higher-level
//! effect, transport, and topology code:
//!
//! - Cross-platform async spawning utilities
//! - System clock and RNG adapters
//! - Platform-specific synchronization primitives
//!
//! # Architecture
//!
//! The utility layer provides the infrastructure needed to execute generated
//! protocol code on native and WASM targets. Execution itself is modeled
//! through the effect system in [`crate::effects`]; this module is only the
//! platform support layer.
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    Generated Code                           │
//! │          Effect Programs + ChoreoHandler                    │
//! └─────────────────────────────────────────────────────────────┘
//!                              │
//!                              ▼
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    Utility Layer                            │
//! │          spawn(), spawn_local(), clocks                     │
//! └─────────────────────────────────────────────────────────────┘
//!                              │
//!                              ▼
//! ┌─────────────────────────────────────────────────────────────┐
//! │                 Transport Implementation                    │
//! │              Handlers / Transport Layers                    │
//! └─────────────────────────────────────────────────────────────┘
//! ```

pub mod clock;
pub mod spawn;
pub mod sync;

// Re-export the main utility helpers at the module boundary.
pub use clock::{SystemClock, SystemRng};
pub use spawn::{spawn, spawn_local, AsyncRuntime};
