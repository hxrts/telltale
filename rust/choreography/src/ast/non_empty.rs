//! Non-empty collection utilities for protocol ASTs.

use std::fmt;
use std::ops::Deref;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NonEmptyError;

impl fmt::Display for NonEmptyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("collection must be non-empty")
    }
}

impl std::error::Error for NonEmptyError {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NonEmptyVec<T>(Vec<T>);

impl<T> NonEmptyVec<T> {
    pub fn new(values: Vec<T>) -> Result<Self, NonEmptyError> {
        if values.is_empty() {
            Err(NonEmptyError)
        } else {
            Ok(Self(values))
        }
    }

    pub fn from_head_tail(head: T, tail: Vec<T>) -> Self {
        let mut values = Vec::with_capacity(1 + tail.len());
        values.push(head);
        values.extend(tail);
        Self(values)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn first(&self) -> &T {
        &self.0[0]
    }

    pub fn as_slice(&self) -> &[T] {
        &self.0
    }

    pub fn into_vec(self) -> Vec<T> {
        self.0
    }

    pub fn push(&mut self, value: T) {
        self.0.push(value);
    }
}

impl<T> Deref for NonEmptyVec<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> TryFrom<Vec<T>> for NonEmptyVec<T> {
    type Error = NonEmptyError;

    fn try_from(values: Vec<T>) -> Result<Self, Self::Error> {
        Self::new(values)
    }
}

impl<T> IntoIterator for NonEmptyVec<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a NonEmptyVec<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut NonEmptyVec<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}
