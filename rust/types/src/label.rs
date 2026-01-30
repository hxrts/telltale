//! Message Labels for Session Types
//!
//! Labels identify message types in communications between roles.
//!
//! # Lean Correspondence
//!
//! Corresponds to the `Label` structure in `lean/Telltale/Protocol/GlobalType.lean`.

use crate::PayloadSort;
use serde::{Deserialize, Serialize};

/// A message label with its payload sort.
///
/// Labels identify message types in communications.
/// Each label has a name and an associated payload type.
///
/// # Examples
///
/// ```
/// use telltale_types::{Label, PayloadSort};
///
/// // Simple label with unit payload
/// let hello = Label::new("hello");
/// assert_eq!(hello.name, "hello");
///
/// // Label with typed payload
/// let data = Label::with_sort("data", PayloadSort::Nat);
/// assert!(!data.sort.is_simple() || matches!(data.sort, PayloadSort::Nat));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Label {
    /// The label name identifying this message type
    pub name: String,
    /// The payload sort for this message
    #[serde(default)]
    pub sort: PayloadSort,
}

impl Label {
    /// Create a new label with unit payload
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            sort: PayloadSort::Unit,
        }
    }

    /// Create a new label with a specific sort
    #[must_use]
    pub fn with_sort(name: impl Into<String>, sort: PayloadSort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    /// Check if this label matches another by name
    #[must_use]
    pub fn matches(&self, other: &Label) -> bool {
        self.name == other.name
    }

    /// Check if this label matches a name
    #[must_use]
    pub fn matches_name(&self, name: &str) -> bool {
        self.name == name
    }
}

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if self.sort != PayloadSort::Unit {
            write!(f, "({})", self.sort)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_label_new() {
        let label = Label::new("hello");
        assert_eq!(label.name, "hello");
        assert_eq!(label.sort, PayloadSort::Unit);
    }

    #[test]
    fn test_label_with_sort() {
        let label = Label::with_sort("data", PayloadSort::Nat);
        assert_eq!(label.name, "data");
        assert_eq!(label.sort, PayloadSort::Nat);
    }

    #[test]
    fn test_label_matches() {
        let l1 = Label::new("msg");
        let l2 = Label::with_sort("msg", PayloadSort::Bool);
        let l3 = Label::new("other");

        assert!(l1.matches(&l2)); // Same name, different sort
        assert!(!l1.matches(&l3)); // Different name
    }

    #[test]
    fn test_label_display() {
        let unit_label = Label::new("hello");
        assert_eq!(format!("{}", unit_label), "hello");

        let typed_label = Label::with_sort("data", PayloadSort::Nat);
        assert_eq!(format!("{}", typed_label), "data(Nat)");
    }
}
