//! Lean Verification Bridge for Rumpsteak Session Types
//!
//! This crate provides bidirectional conversion between Rust session types
//! and Lean-compatible JSON format, enabling formal verification of
//! protocol properties in Lean.
//!
//! # Overview
//!
//! The bridge supports:
//!
//! - **Export**: Convert Rust types to Lean-compatible JSON
//! - **Import**: Parse Lean JSON output into Rust types
//! - **Validation**: Cross-validate Rust implementations against Lean proofs
//!
//! # JSON Format
//!
//! The JSON format matches the Lean type definitions:
//!
//! ```json
//! {
//!   "kind": "comm",
//!   "sender": "Client",
//!   "receiver": "Server",
//!   "branches": [
//!     {
//!       "label": { "name": "request", "sort": "unit" },
//!       "continuation": { "kind": "end" }
//!     }
//!   ]
//! }
//! ```
//!
//! # Example
//!
//! ```
//! use rumpsteak_types::{GlobalType, Label};
//! use rumpsteak_lean_bridge::export::global_to_json;
//!
//! let g = GlobalType::comm(
//!     "Client",
//!     "Server",
//!     vec![(Label::new("hello"), GlobalType::End)],
//! );
//!
//! let json = global_to_json(&g);
//! assert_eq!(json["kind"], "comm");
//! ```

pub mod export;
pub mod import;
pub mod validate;

pub use export::{global_to_json, local_to_json};
pub use import::{json_to_global, json_to_local, ImportError};
pub use validate::{ValidationResult, Validator};
