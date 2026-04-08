//! Observation, replay-artifact, and comparison boundary for `telltale-search`.
//!
//! This crate keeps artifact and comparison logic separate from simulator and
//! viewer integration layers.

/// Marker type for future observation and replay artifacts.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SearchObservationMarker;
