//! Local Type Merging for Projection
//!
//! This module re-exports the merge implementation from `rumpsteak_types`.
//! The merge operation is essential for correct projection of global types
//! to local types when a role is not involved in a choice.
//!
//! See `rumpsteak_types::merge` for full documentation.

pub use rumpsteak_types::merge::{can_merge, merge, merge_all, MergeError, MergeResult};
