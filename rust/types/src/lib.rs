//! Core Session Types for Multiparty Session Type Protocols
//!
//! This crate provides the foundational type definitions for multiparty session types.
//! All types are designed to match their corresponding Lean definitions exactly,
//! enabling formal verification and proof correspondence.
//!
//! # Lean Correspondence
//!
//! Each type in this crate has a direct counterpart in the Lean formalization:
//!
//! | Rust Type | Lean Definition |
//! |-----------|-----------------|
//! | `GlobalType` | `lean/Telltale/Protocol/GlobalType.lean` |
//! | `LocalTypeR` | `lean/Telltale/Protocol/LocalTypeR.lean` |
//! | `PayloadSort` | `lean/Telltale/Protocol/GlobalType.lean` |
//! | `Label` | `lean/Telltale/Protocol/GlobalType.lean` |
//!
//! # References
//!
//! - "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//! - "Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al., POPL 2021)

mod action;
pub mod content_id;
pub mod content_store;
pub mod contentable;
pub mod de_bruijn;
mod global;
mod label;
mod local;
pub mod merge;
mod role;

pub use action::{Action, LocalAction};
pub use content_id::{ContentId, ContentIdSha256, Hasher, Sha256Hasher};
pub use content_store::{CacheMetrics, ContentStore, KeyedContentStore};
pub use contentable::{Contentable, ContentableError};
pub use global::{GlobalType, PayloadSort};
pub use label::Label;
pub use local::LocalTypeR;
pub use merge::{can_merge, merge, merge_all, MergeError, MergeResult};
pub use role::{Role, RoleSet};
