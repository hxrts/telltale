//! Cost and epsilon vocabulary for the generic search crate.
//!
//! Phase 1 intentionally keeps this module minimal; the real semantic surface
//! is added in later implementation phases.

/// Marker type for future fixed-point epsilon modeling.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct EpsilonMarker;
