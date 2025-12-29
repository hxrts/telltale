//! Local session types represented as recursive types.
//!
//! This module provides conversion from FSMs to textual local session type representations.

use super::{Fsm, StateIndex, Transition};
use std::fmt::{self, Display, Formatter};

/// Local session type representation.
///
/// Converts an FSM into a textual recursive type that represents the local session type.
/// This is useful for displaying protocols in a readable format and for understanding
/// the session type structure.
///
/// # Example Output
///
/// ```text
/// rec X0 . Server!Request; [Server?Accept; end, Server?Reject; X0]
/// ```
pub enum Local<R, N, E> {
    /// End of the protocol
    End,
    /// Recursion variable reference
    Recursion(usize),
    /// Recursion variable binding
    Variable(usize, Box<Self>),
    /// Choice between multiple transitions
    Transitions(Vec<(Transition<R, N, E>, Box<Self>)>),
}

impl<R: Clone, N: Clone, E: Clone> Local<R, N, E> {
    /// Constructs a local type representation from an FSM.
    ///
    /// # Panics
    ///
    /// Panics if the FSM has no states.
    pub fn new(fsm: &Fsm<R, N, E>) -> Self {
        let size = fsm.size().0;
        assert!(size > 0);

        let mut builder = Builder {
            fsm,
            seen: &mut vec![false; size],
            looped: &mut vec![None; size],
            variables: &mut 0,
        };

        builder.build(Default::default())
    }
}

struct Builder<'a, R, N, E> {
    fsm: &'a Fsm<R, N, E>,
    seen: &'a mut Vec<bool>,
    looped: &'a mut Vec<Option<usize>>,
    variables: &'a mut usize,
}

impl<R: Clone, N: Clone, E: Clone> Builder<'_, R, N, E> {
    fn variable(&mut self, state: StateIndex) -> usize {
        let variable = &mut self.looped[state.index()];
        if let Some(variable) = variable {
            *variable
        } else {
            let next = *self.variables;
            *variable = Some(next);
            *self.variables += 1;
            next
        }
    }

    fn build(&mut self, state: StateIndex) -> Local<R, N, E> {
        if self.seen[state.index()] {
            return Local::Recursion(self.variable(state));
        }

        let mut transitions = self.fsm.transitions_from(state).peekable();
        if transitions.peek().is_none() {
            return Local::End;
        }

        self.seen[state.index()] = true;
        let transitions =
            transitions.map(|(to, transition)| (transition.to_owned(), Box::new(self.build(to))));
        let ty = Local::Transitions(transitions.collect());
        self.seen[state.index()] = false;

        if let Some(variable) = self.looped[state.index()].take() {
            return Local::Variable(variable, Box::new(ty));
        }

        ty
    }
}

impl<R: Display, N: Display, E: Display> Display for Local<R, N, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::End => write!(f, "end"),
            Self::Recursion(variable) => write!(f, "X{variable}"),
            Self::Variable(variable, ty) => write!(f, "rec X{variable} . {ty}"),
            Self::Transitions(transitions) => {
                assert!(!transitions.is_empty());

                if let [(transition, ty)] = transitions.as_slice() {
                    return write!(f, "{transition}; {ty}");
                }

                let (transition, ty) = &transitions[0];
                write!(f, "[{transition}; {ty}")?;

                for (transition, ty) in &transitions[1..] {
                    write!(f, ", {transition}; {ty}")?;
                }

                write!(f, "]")
            }
        }
    }
}
