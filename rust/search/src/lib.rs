//! Generic deterministic weighted-graph search substrate for Telltale.
//!
//! `telltale-search` is intended to hold a reusable search machine,
//! determinism/admission vocabulary, replay artifacts, and runtime traits for
//! weighted graph search over explicit graph epochs.
//!
//! The crate is intentionally generic:
//!
//! - it does not define application-specific transport or routing concepts,
//! - it does not depend on simulator, viewer, or web crates,
//! - it is meant to be extended by downstream domain implementations via typed
//!   search traits and adapters.

pub mod admission;
pub mod cost;
pub mod domain;
pub mod machine;
pub mod observe;
pub mod runtime;

/// Phase-1 crate scope statement used by smoke tests and boundary checks.
pub const CRATE_SCOPE: &str = "generic weighted-graph-plus-epoch search";
