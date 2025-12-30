//! Subtyping for Local Session Types
//!
//! This module implements subtyping relations for local session types.
//! Session type subtyping allows a more specific type to be used where a
//! more general type is expected.
//!
//! # Features
//!
//! This module requires at least one of these features to be useful:
//!
//! - `async-subtyping` - POPL 2021 asynchronous subtyping
//! - `sync-subtyping` - Synchronous subtyping
//!
//! # Subtyping Modes
//!
//! ## Synchronous Subtyping
//!
//! Simple structural subtyping based on action sequences. A type S is a
//! subtype of T if S can perform all the actions T expects.
//!
//! ## Asynchronous Subtyping
//!
//! Precise subtyping for asynchronous communication based on the POPL 2021
//! paper "Precise Subtyping for Asynchronous Multiparty Sessions".
//! Uses SISO (Single-Input-Single-Output) tree decomposition.
//!
//! # References
//!
//! - "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//! - "Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al., POPL 2021)

#[cfg(feature = "async-subtyping")]
mod r#async;
#[cfg(feature = "sync-subtyping")]
mod sync;

#[cfg(feature = "async-subtyping")]
pub use r#async::{
    async_subtype, orphan_free, siso_decompose, AsyncSubtypeError, InputTree, OutputTree,
    SisoSegment,
};
#[cfg(feature = "sync-subtyping")]
pub use sync::{sync_subtype, SyncSubtypeError};
