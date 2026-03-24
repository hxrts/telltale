#![forbid(unsafe_code)]
#![deny(unused_must_use, unreachable_pub)]
//! Session Type Theory Algorithms
//!
//! This crate provides pure algorithms for session type operations:
//!
//! - **Projection**: Transform global types to local types for each role
//! - **Merge**: Combine local types when a role is not involved in a choice
//! - **Subtyping**: Check subtype relations between local types
//! - **Well-formedness**: Validate session type properties
//! - **Duality**: Compute dual types for binary sessions
//! - **Bounded Recursion**: Limit recursive types for runtime execution
//! - **Semantics**: Async step semantics for global and local types
//! - **Coherence**: Coherence predicates for global types
//!
//! Core semantics-facing algorithms are maintained for Lean parity by default.
//! Some advanced checks remain conservative or experimental and are documented
//! at their API surfaces.
//!
//! # Features
//!
//! - `projection` (default) - Global to local type projection
//! - `duality` (default) - Dual type computation
//! - `merge` (default) - Local type merging
//! - `well-formedness` (default) - Type validation
//! - `semantics` (default) - Async step semantics
//! - `coherence` (default) - Coherence predicates
//! - `async-subtyping` - Experimental conservative async-subtyping checker
//! - `sync-subtyping` - Synchronous subtyping
//! - `bounded` - Bounded recursion strategies
//!
//! # References
//!
//! - "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//! - "Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al., POPL 2021)
//! - "Mechanised Subject Reduction for Multiparty Asynchronous Session Types" (ECOOP 2025)

// Core modules (feature-gated but on by default)
#[cfg(feature = "coherence")]
pub mod coherence;
#[cfg(feature = "duality")]
pub mod duality;
#[cfg(feature = "projection")]
pub mod projection;
#[cfg(feature = "semantics")]
pub mod semantics;
#[cfg(feature = "well-formedness")]
pub mod well_formedness;

// Optional modules
#[cfg(feature = "bounded")]
pub mod bounded;

// Subtyping module - contains both sync and async subtyping
pub mod limits;
pub mod policy;
pub mod subtyping;
