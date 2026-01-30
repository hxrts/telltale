//! Roles in Multiparty Session Types
//!
//! Roles represent participants in a multiparty session.
//! Each role has a unique name and optionally an index for parameterized protocols.

use serde::{Deserialize, Serialize};
use std::collections::HashSet;

/// A role (participant) in a multiparty session.
///
/// # Examples
///
/// ```
/// use telltale_types::Role;
///
/// let client = Role::new("Client");
/// let server = Role::indexed("Worker", 0);
///
/// assert_eq!(client.name(), "Client");
/// assert_eq!(server.full_name(), "Worker_0");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Role {
    /// The base name of the role
    name: String,
    /// Optional index for parameterized roles
    index: Option<usize>,
}

impl Role {
    /// Create a new role with the given name
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            index: None,
        }
    }

    /// Create an indexed role (for parameterized protocols)
    #[must_use]
    pub fn indexed(name: impl Into<String>, index: usize) -> Self {
        Self {
            name: name.into(),
            index: Some(index),
        }
    }

    /// Get the base name of the role
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the index if this is a parameterized role
    #[must_use]
    pub fn index(&self) -> Option<usize> {
        self.index
    }

    /// Get the full name including index
    #[must_use]
    pub fn full_name(&self) -> String {
        match self.index {
            Some(i) => format!("{}_{}", self.name, i),
            None => self.name.clone(),
        }
    }

    /// Check if this role matches another by name (ignoring index)
    #[must_use]
    pub fn matches_name(&self, other: &Role) -> bool {
        self.name == other.name
    }
}

impl std::fmt::Display for Role {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.full_name())
    }
}

impl From<&str> for Role {
    fn from(name: &str) -> Self {
        Role::new(name)
    }
}

impl From<String> for Role {
    fn from(name: String) -> Self {
        Role::new(name)
    }
}

/// A set of roles participating in a protocol.
///
/// Provides convenient operations for working with collections of roles.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoleSet {
    roles: HashSet<Role>,
}

impl RoleSet {
    /// Create an empty role set
    #[must_use]
    pub fn new() -> Self {
        Self {
            roles: HashSet::new(),
        }
    }

    /// Create a role set from an iterator
    ///
    /// Note: Consider using `collect()` directly via the `FromIterator` implementation.
    #[must_use]
    pub fn from_roles(iter: impl IntoIterator<Item = Role>) -> Self {
        Self {
            roles: iter.into_iter().collect(),
        }
    }

    /// Add a role to the set
    pub fn insert(&mut self, role: Role) -> bool {
        self.roles.insert(role)
    }

    /// Remove a role from the set
    pub fn remove(&mut self, role: &Role) -> bool {
        self.roles.remove(role)
    }

    /// Check if the set contains a role
    #[must_use]
    pub fn contains(&self, role: &Role) -> bool {
        self.roles.contains(role)
    }

    /// Check if the set contains a role by name
    #[must_use]
    pub fn contains_name(&self, name: &str) -> bool {
        self.roles.iter().any(|r| r.name == name)
    }

    /// Get the number of roles
    #[must_use]
    pub fn len(&self) -> usize {
        self.roles.len()
    }

    /// Check if the set is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.roles.is_empty()
    }

    /// Iterate over the roles
    pub fn iter(&self) -> impl Iterator<Item = &Role> {
        self.roles.iter()
    }

    /// Get roles as a vector of names
    #[must_use]
    pub fn names(&self) -> Vec<String> {
        self.roles.iter().map(|r| r.full_name()).collect()
    }
}

impl IntoIterator for RoleSet {
    type Item = Role;
    type IntoIter = std::collections::hash_set::IntoIter<Role>;

    fn into_iter(self) -> Self::IntoIter {
        self.roles.into_iter()
    }
}

impl<'a> IntoIterator for &'a RoleSet {
    type Item = &'a Role;
    type IntoIter = std::collections::hash_set::Iter<'a, Role>;

    fn into_iter(self) -> Self::IntoIter {
        self.roles.iter()
    }
}

impl FromIterator<Role> for RoleSet {
    fn from_iter<T: IntoIterator<Item = Role>>(iter: T) -> Self {
        Self {
            roles: iter.into_iter().collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_role_new() {
        let role = Role::new("Client");
        assert_eq!(role.name(), "Client");
        assert_eq!(role.index(), None);
        assert_eq!(role.full_name(), "Client");
    }

    #[test]
    fn test_role_indexed() {
        let role = Role::indexed("Worker", 2);
        assert_eq!(role.name(), "Worker");
        assert_eq!(role.index(), Some(2));
        assert_eq!(role.full_name(), "Worker_2");
    }

    #[test]
    fn test_role_display() {
        let simple = Role::new("Server");
        let indexed = Role::indexed("Node", 5);

        assert_eq!(format!("{}", simple), "Server");
        assert_eq!(format!("{}", indexed), "Node_5");
    }

    #[test]
    fn test_role_set() {
        let mut set = RoleSet::new();
        set.insert(Role::new("A"));
        set.insert(Role::new("B"));
        set.insert(Role::new("C"));

        assert_eq!(set.len(), 3);
        assert!(set.contains_name("A"));
        assert!(set.contains_name("B"));
        assert!(!set.contains_name("D"));
    }

    #[test]
    fn test_role_set_from_iter() {
        let roles = vec![Role::new("X"), Role::new("Y"), Role::new("Z")];
        let set: RoleSet = roles.into_iter().collect();

        assert_eq!(set.len(), 3);
        assert!(set.contains_name("X"));
    }
}
