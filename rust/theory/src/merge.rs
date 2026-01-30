//! Local Type Merging for Projection
//!
//! This module re-exports the merge implementation from `telltale_types`.
//! The merge operation is essential for correct projection of global types
//! to local types when a role is not involved in a choice.
//!
//! See `telltale_types::merge` for full documentation.

pub use telltale_types::merge::{can_merge, merge, merge_all, MergeError, MergeResult};
