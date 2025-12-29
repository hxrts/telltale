//! Asynchronous subtyping verification for session types.
//!
//! This module implements the asynchronous subtyping algorithm from the paper
//! "Precise Subtyping for Asynchronous Multiparty Sessions". It verifies whether
//! one FSM is a valid implementation of another, allowing message reordering
//! according to asynchronous semantics.
//!
//! The algorithm checks if one protocol can safely replace another by exploring
//! the state space and verifying that all message sequences are compatible with
//! the given bound on visits.

#![cfg(feature = "subtyping")]

mod matrix;
mod pair;
mod prefix;

use self::{
    matrix::Matrix,
    pair::Pair,
    prefix::{Index, Prefix, Snapshot},
};
use crate::{Action, Fsm, StateIndex, TransitionRef};
use std::{convert::Infallible, iter::Peekable, mem};

#[derive(Clone)]
struct Previous {
    visits: usize,
    snapshots: Option<Pair<Snapshot>>,
}

impl Previous {
    fn new(visits: usize, snapshots: Option<Pair<Snapshot>>) -> Self {
        Self { visits, snapshots }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Quantifier {
    All,
    Any,
}

struct SubtypeVisitor<'a, R, N> {
    fsms: Pair<&'a Fsm<R, N, Infallible>>,
    history: Matrix<Previous>,
    prefixes: Pair<Prefix<'a, R, N>>,
}

impl<'a, R: Eq, N: Eq> SubtypeVisitor<'a, R, N> {
    #[inline]
    fn unroll<
        I: Iterator<Item = (StateIndex, TransitionRef<'a, R, N, Infallible>)>,
        const SWAP: bool,
    >(
        &mut self,
        mut transitions: Pair<I>,
        mut quantifiers: Pair<Quantifier>,
    ) -> bool {
        let mut prefixes = self.prefixes.as_ref();
        if SWAP {
            prefixes.swap();
            transitions.swap();
            quantifiers.swap();
        }

        let right_transitions = transitions.right.collect::<Vec<_>>();
        let left_snapshot = prefixes.left.snapshot();
        let right_snapshot = prefixes.right.snapshot();

        for (left_state, left_transition) in transitions.left {
            let mut prefixes = self.prefixes.as_mut();
            if SWAP {
                prefixes.swap();
            }

            prefixes.left.revert(&left_snapshot);
            prefixes.left.push(left_transition);
            let left_snapshot = prefixes.left.snapshot();

            let mut output = quantifiers.right == Quantifier::All;
            for (right_state, right_transition) in &right_transitions {
                let mut prefixes = self.prefixes.as_mut();
                if SWAP {
                    prefixes.swap();
                }

                prefixes.left.revert(&left_snapshot);
                prefixes.right.revert(&right_snapshot);
                prefixes.right.push(right_transition.clone());

                let mut states = Pair::new(left_state, *right_state);
                if SWAP {
                    states.swap();
                }

                output = self.visit(states);

                if output == (quantifiers.right == Quantifier::Any) {
                    break;
                }
            }

            if output == (quantifiers.left == Quantifier::Any) {
                return output;
            }
        }

        quantifiers.left == Quantifier::All
    }

    fn visit(&mut self, states: Pair<StateIndex>) -> bool {
        let index = states.map(StateIndex::index);
        if self.history[index].visits == 0 {
            return false;
        }

        if !reduce(&mut self.prefixes) {
            return false;
        }

        if let Some(snapshots) = &self.history[index].snapshots {
            let mut prefixes = self.prefixes.as_ref().zip(snapshots.as_ref()).into_iter();
            if prefixes.all(|(prefix, snapshot)| !prefix.is_modified(snapshot)) {
                return true;
            }
        }

        let mut transitions = self.fsms.zip(states).map(|(fsm, state)| {
            let transitions = fsm.transitions_from(state);
            transitions.peekable()
        });

        let empty_prefixes = self.prefixes.iter().all(Prefix::is_empty);
        match transitions.as_mut().map(Peekable::peek).into() {
            (None, None) if empty_prefixes => true,
            (Some((_, left)), Some((_, right))) => {
                let snapshots = self.prefixes.as_ref().map(Prefix::snapshot);
                let previous = Previous::new(self.history[index].visits - 1, Some(snapshots));
                let previous = mem::replace(&mut self.history[index], previous);

                let output = match (left.action, right.action) {
                    (Action::Output, Action::Output) => {
                        let quantifiers = Pair::new(Quantifier::All, Quantifier::Any);
                        self.unroll::<_, false>(transitions, quantifiers)
                    }
                    (Action::Output, Action::Input) => {
                        let quantifiers = Pair::new(Quantifier::All, Quantifier::All);
                        self.unroll::<_, false>(transitions, quantifiers)
                    }
                    (Action::Input, Action::Output) => {
                        let quantifiers = Pair::new(Quantifier::Any, Quantifier::Any);
                        self.unroll::<_, false>(transitions, quantifiers)
                    }
                    (Action::Input, Action::Input) => {
                        let quantifiers = Pair::new(Quantifier::Any, Quantifier::All);
                        self.unroll::<_, true>(transitions, quantifiers)
                    }
                };

                self.history[index] = previous;
                output
            }
            _ => false,
        }
    }
}

fn reduce<R: Eq, N: Eq>(prefixes: &mut Pair<Prefix<R, N>>) -> bool {
    fn reorder<R: Eq, N: Eq>(
        left: &TransitionRef<R, N, Infallible>,
        rights: &Prefix<R, N>,
        reject: impl Fn(&TransitionRef<R, N, Infallible>, &TransitionRef<R, N, Infallible>) -> bool,
    ) -> Option<Option<Index>> {
        let mut rights = rights.iter_full();

        let (_, right) = rights.next().unwrap();
        if reject(left, right) {
            return None;
        }

        for (i, right) in rights {
            if left == right {
                return Some(Some(i));
            }

            if reject(left, right) {
                return None;
            }
        }

        Some(None)
    }

    while let (Some(left), Some(right)) = prefixes.as_ref().map(Prefix::first).into() {
        // Fast path to avoid added control flow.
        if left == right {
            for prefix in prefixes.iter_mut() {
                prefix.remove_first();
            }

            continue;
        }

        // Note: Caching reorder results would improve performance but requires
        // refactoring to pass cache state through the reduce function
        let i = match left.action {
            Action::Input => reorder(left, &prefixes.right, |left, right| {
                right.role == left.role || right.action == Action::Output
            }),
            Action::Output => reorder(left, &prefixes.right, |left, right| {
                right.role == left.role && right.action == Action::Output
            }),
        };

        match i {
            Some(Some(i)) => {
                prefixes.left.remove_first();
                prefixes.right.remove(i);
            }
            Some(None) => break,
            None => return false,
        }
    }

    true
}

/// Checks if `left` is an asynchronous subtype of `right`.
///
/// Returns true if the left FSM can safely implement the right FSM according
/// to asynchronous subtyping rules. The `visits` parameter bounds the search depth.
///
/// # Arguments
///
/// * `left` - The implementation FSM
/// * `right` - The specification FSM
/// * `visits` - Maximum number of times to visit each state pair
///
/// # Panics
///
/// Panics if the FSMs represent different roles.
///
/// # Example
///
/// ```rust,ignore
/// use rumpsteak_aura_fsm::subtype::is_subtype;
///
/// let implementation = /* ... */;
/// let specification = /* ... */;
///
/// if is_subtype(&implementation, &specification, 2) {
///     println!("Implementation is valid!");
/// }
/// ```
pub fn is_subtype<R: Eq, N: Eq>(
    left: &Fsm<R, N, Infallible>,
    right: &Fsm<R, N, Infallible>,
    visits: usize,
) -> bool {
    assert!(
        !(left.role() != right.role()),
        "FSMs are for different roles"
    );

    let sizes = Pair::new(left.size().0, right.size().0);
    let mut visitor = SubtypeVisitor {
        fsms: Pair::new(left, right),
        history: Matrix::new(sizes, Previous::new(visits, None)),
        prefixes: Default::default(),
    };

    visitor.visit(Default::default())
}
