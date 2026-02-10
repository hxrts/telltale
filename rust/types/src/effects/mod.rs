//! Algebraic effect traits for deterministic simulation.
//!
//! This module provides injected time and randomness primitives that enable
//! reproducible protocol execution. Both `choreography::testing` and
//! `telltale-simulator` use these shared trait definitions.
//!
//! # Design
//!
//! These are "algebraic effects" in the sense that they abstract over
//! side-effectful operations (time, randomness) with pure interfaces.
//! Implementations can be:
//!
//! - **Deterministic**: For reproducible testing and simulation
//! - **Real**: For production runtime using host APIs
//!
//! # Provided Implementations
//!
//! | Type | Algorithm | Use Case |
//! |------|-----------|----------|
//! | `MockClock` | Atomic counter | Testing |
//! | `SeededRng` | Xorshift64 | Fast deterministic testing |
//!
//! More sophisticated implementations (e.g., ChaCha8-based RNG) are provided
//! by downstream crates like `telltale-simulator`.

mod clock;
mod rng;

pub use clock::{Clock, MockClock, WallClock};
pub use rng::{Rng, SeededRng};
