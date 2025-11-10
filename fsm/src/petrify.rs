//! Petrify output format for FSMs.
//!
//! This module provides export of FSMs to Petrify format, which can be used
//! with Petri net analysis tools.

use super::Fsm;
use std::fmt::{self, Display, Formatter};

/// Wrapper for exporting an FSM in Petrify format.
///
/// Petrify is a tool for synthesis and verification of Petri nets.
/// This format can be used for formal analysis of session type protocols.
pub struct Petrify<'a, R, N, E>(&'a Fsm<R, N, E>);

impl<'a, R, N, E> Petrify<'a, R, N, E> {
    /// Creates a new Petrify exporter for the given FSM.
    ///
    /// # Panics
    ///
    /// Panics if the FSM has no states.
    pub fn new(fsm: &'a Fsm<R, N, E>) -> Self {
        assert!(fsm.size().0 > 0);
        Self(fsm)
    }
}

impl<R: Display, N: Display, E> Display for Petrify<'_, R, N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, ".outputs")?;
        writeln!(f, ".state graph")?;

        for (from, to, transition) in self.0.transitions() {
            let (from, to) = (from.index(), to.index());
            let (role, action, message) = (transition.role, transition.action, transition.message);
            writeln!(f, "s{} {} {} {} s{}", from, role, action, message.label, to)?;
        }

        writeln!(f, ".marking s0")?;
        write!(f, ".end")
    }
}
