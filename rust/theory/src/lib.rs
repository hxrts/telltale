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
//!
//! All algorithms are designed to match their Lean implementations exactly.
//!
//! # References
//!
//! - "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//! - "Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al., POPL 2021)

pub mod bounded;
pub mod duality;
pub mod merge;
pub mod projection;
pub mod subtyping;
pub mod well_formedness;

pub use bounded::{bound_recursion, unfold_bounded, BoundingStrategy};
pub use duality::{dual, is_dual};
pub use merge::{can_merge, merge, merge_all, MergeError};
pub use projection::{project, ProjectionError};
pub use subtyping::{
    async_subtype, orphan_free, siso_decompose, sync_subtype, AsyncSubtypeError, InputTree,
    OutputTree, SisoSegment, SyncSubtypeError,
};
pub use well_formedness::{validate_global, validate_local, ValidationError};
