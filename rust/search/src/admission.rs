//! Admission and capability vocabulary for `telltale-search`.
//!
//! This module will eventually hold determinism-profile, scheduler-profile, and
//! fairness-bundle containment checks.

/// Marker type for future search capability admission surfaces.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SearchAdmissionMarker;
