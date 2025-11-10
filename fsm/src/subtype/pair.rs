//! Pair data structure for holding left/right values.

use std::{
    fmt::{self, Display, Formatter},
    mem,
};

/// A pair of values, typically representing left and right FSMs being compared.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Pair<T> {
    /// The left value
    pub left: T,
    /// The right value
    pub right: T,
}

impl<T> Pair<T> {
    /// Creates a new pair with the given left and right values.
    pub fn new(left: T, right: T) -> Self {
        Self { left, right }
    }

    /// Returns a pair of references to the values.
    pub fn as_ref(&self) -> Pair<&T> {
        Pair::new(&self.left, &self.right)
    }

    /// Returns a pair of mutable references to the values.
    pub fn as_mut(&mut self) -> Pair<&mut T> {
        Pair::new(&mut self.left, &mut self.right)
    }

    /// Swaps the left and right values.
    pub fn swap(&mut self) {
        mem::swap(&mut self.left, &mut self.right);
    }

    /// Zips this pair with another, creating a pair of tuples.
    pub fn zip<U>(self, other: Pair<U>) -> Pair<(T, U)> {
        Pair::new((self.left, other.left), (self.right, other.right))
    }

    /// Maps a function over both values in the pair.
    pub fn map<U>(self, f: impl Fn(T) -> U) -> Pair<U> {
        Pair::new(f(self.left), f(self.right))
    }

    /// Converts the pair into an iterator over its values.
    pub fn into_iter(self) -> impl Iterator<Item = T> {
        self.map(Some)
    }

    /// Returns an iterator over references to the values.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.as_ref().into_iter()
    }

    /// Returns an iterator over mutable references to the values.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.as_mut().into_iter()
    }
}

impl<T: Display> Display for Pair<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "<{}, {}>", self.left, self.right)
    }
}

impl<T> Iterator for Pair<Option<T>> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.left.take().or_else(|| self.right.take())
    }
}

impl<T> From<Pair<T>> for (T, T) {
    fn from(pair: Pair<T>) -> Self {
        (pair.left, pair.right)
    }
}

impl<T> From<Pair<T>> for [T; 2] {
    fn from(pair: Pair<T>) -> Self {
        [pair.left, pair.right]
    }
}
