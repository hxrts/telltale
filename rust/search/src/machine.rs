//! Canonical search-machine boundary.
//!
//! The authoritative serial machine, invariants, replay interpretation, and
//! batch legality rules will live here in later phases.

/// Marker type for the future canonical search machine.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SearchMachineMarker;
