//! Runtime and proposal-execution boundary for `telltale-search`.
//!
//! This module is reserved for speculative proposal generation, scheduler
//! policy, and host-loop orchestration.

/// Marker type for future runtime policy surfaces.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SearchRuntimeMarker;
