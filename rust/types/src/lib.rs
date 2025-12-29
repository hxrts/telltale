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
//! | `GlobalType` | `lean/Rumpsteak/Protocol/GlobalType.lean` |
//! | `LocalTypeR` | `lean/Rumpsteak/Protocol/LocalTypeR.lean` |
//! | `PayloadSort` | `lean/Rumpsteak/Protocol/GlobalType.lean` |
//! | `Label` | `lean/Rumpsteak/Protocol/GlobalType.lean` |
//!
//! # References
//!
//! - "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//! - "Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al., POPL 2021)

mod action;
mod global;
mod label;
mod local;
mod role;

pub use action::{Action, LocalAction};
pub use global::{GlobalType, PayloadSort};
pub use label::Label;
pub use local::LocalTypeR;
pub use role::{Role, RoleSet};
