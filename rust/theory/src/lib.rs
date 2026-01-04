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
//! All algorithms are designed to match their Lean implementations exactly.
//!
//! # Features
//!
//! - `projection` (default) - Global to local type projection
//! - `duality` (default) - Dual type computation
//! - `merge` (default) - Local type merging
//! - `well-formedness` (default) - Type validation
//! - `semantics` (default) - Async step semantics
//! - `coherence` (default) - Coherence predicates
//! - `async-subtyping` - POPL 2021 asynchronous subtyping algorithm
//! - `sync-subtyping` - Synchronous subtyping
//! - `bounded` - Bounded recursion strategies
//!
//! # References
//!
//! - "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//! - "Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al., POPL 2021)
//! - "Mechanised Subject Reduction for Multiparty Asynchronous Session Types" (ECOOP 2025)

// Core modules (feature-gated but on by default)
#[cfg(feature = "duality")]
pub mod duality;
#[cfg(feature = "merge")]
pub mod merge;
#[cfg(feature = "projection")]
pub mod projection;
#[cfg(feature = "well-formedness")]
pub mod well_formedness;
#[cfg(feature = "semantics")]
pub mod semantics;
#[cfg(feature = "coherence")]
pub mod coherence;

// Optional modules
#[cfg(feature = "bounded")]
pub mod bounded;

// Subtyping module - contains both sync and async subtyping
pub mod subtyping;
pub mod limits;
pub mod policy;

// Re-exports for core modules
#[cfg(feature = "duality")]
pub use duality::{dual, is_dual};
#[cfg(feature = "merge")]
pub use merge::{can_merge, merge, merge_all, MergeError};
#[cfg(feature = "projection")]
pub use projection::{project, project_all, MemoizedProjector, ProjectionError};
#[cfg(feature = "well-formedness")]
pub use well_formedness::{validate_global, validate_local, unique_labels, ValidationError};
#[cfg(feature = "semantics")]
pub use semantics::{
    can_step, step, local_can_step, local_step,
    consume_with_proof, reduces, reduces_star, good_g,
    GlobalAction, LocalAction, LocalKind, ConsumeResult,
};
pub use limits::{
    FuelSteps, YieldAfterSteps, UnfoldSteps, CacheEntries,
    DEFAULT_SISO_UNFOLD_STEPS, DEFAULT_PROJECTOR_CACHE_ENTRIES,
};
pub use policy::{BreadthFirst, DepthFirst, RoundRobin, SchedulerPolicy};
#[cfg(feature = "coherence")]
pub use coherence::{check_coherent, projectable, CoherentG};

// Re-exports for optional modules
#[cfg(feature = "bounded")]
pub use bounded::{bound_recursion, unfold_bounded, BoundingStrategy};

// Subtyping re-exports (conditionally based on features)
#[cfg(feature = "async-subtyping")]
pub use subtyping::{
    async_subtype, orphan_free, siso_decompose, siso_decompose_with_fuel, AsyncSubtypeError,
    InputTree, OutputTree, SisoSegment,
};
#[cfg(feature = "sync-subtyping")]
pub use subtyping::{sync_subtype, SyncSubtypeError};
