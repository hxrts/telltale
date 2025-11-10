//! Message sequence tracking for asynchronous subtyping.
//!
//! This module provides data structures for tracking sequences of transitions
//! (message prefixes) during subtyping verification, with support for efficient
//! insertion, removal, and backtracking.

use crate::TransitionRef;
use std::{
    convert::Infallible,
    fmt::{self, Display, Formatter},
};

/// Index into a prefix sequence.
#[derive(Clone, Copy)]
pub struct Index(usize);

/// Snapshot of a prefix's state for backtracking.
///
/// Captures the state of a prefix at a point in time, allowing
/// efficient rollback during the search algorithm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Snapshot {
    size: usize,
    start: usize,
    removed: usize,
}

/// A sequence of transitions representing pending messages.
///
/// Supports efficient addition, removal, snapshotting, and restoration
/// of transition sequences during subtyping verification.
#[derive(Debug)]
pub struct Prefix<'a, R, N> {
    transitions: Vec<(bool, TransitionRef<'a, R, N, Infallible>)>,
    start: usize,
    removed: Vec<usize>,
}

impl<R, N> Default for Prefix<'_, R, N> {
    fn default() -> Self {
        Self {
            transitions: Default::default(),
            start: Default::default(),
            removed: Default::default(),
        }
    }
}

impl<'a, R, N> Prefix<'a, R, N> {
    /// Returns true if the prefix has no transitions.
    pub fn is_empty(&self) -> bool {
        self.start >= self.transitions.len()
    }

    /// Returns a reference to the first transition in the prefix, if any.
    pub(super) fn first(&self) -> Option<&TransitionRef<'a, R, N, Infallible>> {
        if let Some((removed, transition)) = self.transitions.get(self.start) {
            assert!(!removed);
            return Some(transition);
        }

        None
    }

    /// Adds a transition to the end of the prefix.
    pub(super) fn push(&mut self, transition: TransitionRef<'a, R, N, Infallible>) {
        self.transitions.push((false, transition));
    }

    /// Removes the first transition from the prefix.
    pub fn remove_first(&mut self) {
        assert!(matches!(self.transitions.get(self.start), Some((false, _))));
        self.start += 1;
        while let Some((true, _)) = self.transitions.get(self.start) {
            self.start += 1;
        }
    }

    /// Removes a transition at the given index.
    pub fn remove(&mut self, Index(i): Index) {
        if i == self.start {
            self.remove_first();
            return;
        }

        let (removed, _) = &mut self.transitions[i];
        assert!(!*removed);
        *removed = true;
        self.removed.push(i);
    }

    /// Creates a snapshot of the current state for later restoration.
    pub fn snapshot(&self) -> Snapshot {
        Snapshot {
            size: self.transitions.len(),
            start: self.start,
            removed: self.removed.len(),
        }
    }

    fn valid_snapshot(&self, snapshot: &Snapshot) -> bool {
        snapshot.removed <= self.removed.len()
            && snapshot.size <= self.transitions.len()
            && snapshot.start <= self.start
    }

    /// Returns true if the prefix has been modified since the snapshot.
    pub fn is_modified(&self, snapshot: &Snapshot) -> bool
    where
        R: Eq,
        N: Eq,
    {
        assert!(self.valid_snapshot(snapshot));
        self.transitions[self.start..] != self.transitions[..snapshot.size][snapshot.start..]
    }

    /// Restores the prefix to the state captured in the snapshot.
    pub fn revert(&mut self, snapshot: &Snapshot) {
        assert!(self.valid_snapshot(snapshot));
        for &i in self.removed.get(snapshot.removed..).unwrap_or_default() {
            let (removed, _) = &mut self.transitions[i];
            assert!(*removed);
            *removed = false;
        }

        self.removed.truncate(snapshot.removed);
        self.transitions.truncate(snapshot.size);
        self.start = snapshot.start;
    }

    pub(super) fn iter_full(
        &self,
    ) -> impl Iterator<Item = (Index, &TransitionRef<'a, R, N, Infallible>)> {
        let prefixes = self.transitions.iter().enumerate().skip(self.start);
        prefixes
            .filter(|&(_, (removed, _))| !removed)
            .map(|(i, (_, transition))| (Index(i), transition))
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = &TransitionRef<'a, R, N, Infallible>> {
        self.iter_full().map(|(_, transition)| transition)
    }
}

impl<R: Display, N: Display> Display for Prefix<'_, R, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut transitions = self.iter();
        if let Some(transition) = transitions.next() {
            write!(f, "{transition}")?;
            for transition in transitions {
                write!(f, " . {transition}")?;
            }

            return Ok(());
        }

        write!(f, "empty")
    }
}
