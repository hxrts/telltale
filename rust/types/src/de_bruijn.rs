//! De Bruijn Index Representation for Session Types
//!
//! This module provides de Bruijn index representations for session types,
//! enabling α-equivalence: types that differ only in variable names produce
//! identical serializations.
//!
//! # De Bruijn Indices
//!
//! De Bruijn indices replace named variables with numeric indices representing
//! binding depth. For example:
//!
//! ```text
//! Named:       μx. A → B : x        μy. A → B : y
//! De Bruijn:   μ. A → B : 0         μ. A → B : 0
//!                    ↑ same canonical form ↑
//! ```
//!
//! # Usage
//!
//! These types are **transient** - they exist only during serialization.
//! The named representation (`GlobalType`, `LocalTypeR`) is preserved at runtime;
//! de Bruijn conversion is performed only when computing content IDs.
//!
//! # Lean Correspondence
//!
//! This module corresponds to `lean/Rumpsteak/Protocol/DeBruijn.lean`.

use crate::{GlobalType, Label, LocalTypeR};
use serde::{Deserialize, Serialize};

/// Global type with de Bruijn indices (for serialization only).
///
/// This representation erases variable names, using numeric indices
/// to reference binders. Two α-equivalent global types produce
/// identical `GlobalTypeDB` values.
///
/// # Examples
///
/// ```
/// use rumpsteak_types::{GlobalType, Label, de_bruijn::GlobalTypeDB};
///
/// // These two types are α-equivalent
/// let g1 = GlobalType::mu("x", GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")));
/// let g2 = GlobalType::mu("y", GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")));
///
/// // They produce identical de Bruijn representations
/// let db1 = GlobalTypeDB::from(&g1);
/// let db2 = GlobalTypeDB::from(&g2);
/// assert_eq!(db1, db2);
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum GlobalTypeDB {
    /// Protocol termination
    End,
    /// Communication: sender → receiver with choice of labeled continuations
    Comm {
        sender: String,
        receiver: String,
        branches: Vec<(Label, GlobalTypeDB)>,
    },
    /// Recursive type: μ.G (no variable name)
    Rec(Box<GlobalTypeDB>),
    /// Type variable: de Bruijn index (0 = innermost binder)
    Var(usize),
}

impl GlobalTypeDB {
    /// Convert a `GlobalType` to de Bruijn representation.
    ///
    /// Corresponds to Lean's `GlobalType.toDeBruijn`.
    #[must_use]
    pub fn from_global_type(g: &GlobalType) -> Self {
        Self::from_global_type_with_env(g, &[])
    }

    fn from_global_type_with_env(g: &GlobalType, env: &[&str]) -> Self {
        match g {
            GlobalType::End => GlobalTypeDB::End,
            GlobalType::Comm {
                sender,
                receiver,
                branches,
            } => GlobalTypeDB::Comm {
                sender: sender.clone(),
                receiver: receiver.clone(),
                branches: branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), Self::from_global_type_with_env(cont, env)))
                    .collect(),
            },
            GlobalType::Mu { var, body } => {
                // Push the variable name onto the environment stack
                let mut new_env = vec![var.as_str()];
                new_env.extend(env);
                GlobalTypeDB::Rec(Box::new(Self::from_global_type_with_env(body, &new_env)))
            }
            GlobalType::Var(name) => {
                // Find the index of this variable in the environment
                let index = env.iter().position(|&v| v == name).unwrap_or(env.len()); // Unbound var gets index beyond env
                GlobalTypeDB::Var(index)
            }
        }
    }

    /// Normalize branch ordering for deterministic serialization.
    ///
    /// Sorts branches by label name to ensure consistent ordering.
    #[must_use]
    pub fn normalize(&self) -> Self {
        match self {
            GlobalTypeDB::End => GlobalTypeDB::End,
            GlobalTypeDB::Comm {
                sender,
                receiver,
                branches,
            } => {
                let mut sorted_branches: Vec<_> = branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), cont.normalize()))
                    .collect();
                sorted_branches.sort_by(|a, b| a.0.name.cmp(&b.0.name));
                GlobalTypeDB::Comm {
                    sender: sender.clone(),
                    receiver: receiver.clone(),
                    branches: sorted_branches,
                }
            }
            GlobalTypeDB::Rec(body) => GlobalTypeDB::Rec(Box::new(body.normalize())),
            GlobalTypeDB::Var(idx) => GlobalTypeDB::Var(*idx),
        }
    }
}

impl From<&GlobalType> for GlobalTypeDB {
    fn from(g: &GlobalType) -> Self {
        GlobalTypeDB::from_global_type(g)
    }
}

/// Local type with de Bruijn indices (for serialization only).
///
/// This representation erases variable names, using numeric indices
/// to reference binders. Two α-equivalent local types produce
/// identical `LocalTypeRDB` values.
///
/// # Examples
///
/// ```
/// use rumpsteak_types::{LocalTypeR, Label, de_bruijn::LocalTypeRDB};
///
/// // These two types are α-equivalent
/// let t1 = LocalTypeR::mu("x", LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("x")));
/// let t2 = LocalTypeR::mu("y", LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("y")));
///
/// // They produce identical de Bruijn representations
/// let db1 = LocalTypeRDB::from(&t1);
/// let db2 = LocalTypeRDB::from(&t2);
/// assert_eq!(db1, db2);
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LocalTypeRDB {
    /// Protocol termination
    End,
    /// Internal choice: send to partner
    Send {
        partner: String,
        branches: Vec<(Label, LocalTypeRDB)>,
    },
    /// External choice: receive from partner
    Recv {
        partner: String,
        branches: Vec<(Label, LocalTypeRDB)>,
    },
    /// Recursive type: μ.T (no variable name)
    Rec(Box<LocalTypeRDB>),
    /// Type variable: de Bruijn index (0 = innermost binder)
    Var(usize),
}

impl LocalTypeRDB {
    /// Convert a `LocalTypeR` to de Bruijn representation.
    ///
    /// Corresponds to Lean's `LocalTypeR.toDeBruijn`.
    #[must_use]
    pub fn from_local_type(t: &LocalTypeR) -> Self {
        Self::from_local_type_with_env(t, &[])
    }

    fn from_local_type_with_env(t: &LocalTypeR, env: &[&str]) -> Self {
        match t {
            LocalTypeR::End => LocalTypeRDB::End,
            LocalTypeR::Send { partner, branches } => LocalTypeRDB::Send {
                partner: partner.clone(),
                branches: branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), Self::from_local_type_with_env(cont, env)))
                    .collect(),
            },
            LocalTypeR::Recv { partner, branches } => LocalTypeRDB::Recv {
                partner: partner.clone(),
                branches: branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), Self::from_local_type_with_env(cont, env)))
                    .collect(),
            },
            LocalTypeR::Mu { var, body } => {
                // Push the variable name onto the environment stack
                let mut new_env = vec![var.as_str()];
                new_env.extend(env);
                LocalTypeRDB::Rec(Box::new(Self::from_local_type_with_env(body, &new_env)))
            }
            LocalTypeR::Var(name) => {
                // Find the index of this variable in the environment
                let index = env.iter().position(|&v| v == name).unwrap_or(env.len()); // Unbound var gets index beyond env
                LocalTypeRDB::Var(index)
            }
        }
    }

    /// Normalize branch ordering for deterministic serialization.
    ///
    /// Sorts branches by label name to ensure consistent ordering.
    #[must_use]
    pub fn normalize(&self) -> Self {
        match self {
            LocalTypeRDB::End => LocalTypeRDB::End,
            LocalTypeRDB::Send { partner, branches } => {
                let mut sorted_branches: Vec<_> = branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), cont.normalize()))
                    .collect();
                sorted_branches.sort_by(|a, b| a.0.name.cmp(&b.0.name));
                LocalTypeRDB::Send {
                    partner: partner.clone(),
                    branches: sorted_branches,
                }
            }
            LocalTypeRDB::Recv { partner, branches } => {
                let mut sorted_branches: Vec<_> = branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), cont.normalize()))
                    .collect();
                sorted_branches.sort_by(|a, b| a.0.name.cmp(&b.0.name));
                LocalTypeRDB::Recv {
                    partner: partner.clone(),
                    branches: sorted_branches,
                }
            }
            LocalTypeRDB::Rec(body) => LocalTypeRDB::Rec(Box::new(body.normalize())),
            LocalTypeRDB::Var(idx) => LocalTypeRDB::Var(*idx),
        }
    }
}

impl From<&LocalTypeR> for LocalTypeRDB {
    fn from(t: &LocalTypeR) -> Self {
        LocalTypeRDB::from_local_type(t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn test_alpha_equivalent_global_types() {
        // μx. A → B : msg. x
        let g1 = GlobalType::mu(
            "x",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
        );
        // μy. A → B : msg. y (same structure, different variable name)
        let g2 = GlobalType::mu(
            "y",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")),
        );

        let db1 = GlobalTypeDB::from(&g1);
        let db2 = GlobalTypeDB::from(&g2);

        assert_eq!(db1, db2);
    }

    #[test]
    fn test_alpha_equivalent_local_types() {
        // μx. !B{msg.x}
        let t1 = LocalTypeR::mu(
            "x",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("x")),
        );
        // μy. !B{msg.y} (same structure, different variable name)
        let t2 = LocalTypeR::mu(
            "y",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("y")),
        );

        let db1 = LocalTypeRDB::from(&t1);
        let db2 = LocalTypeRDB::from(&t2);

        assert_eq!(db1, db2);
    }

    #[test]
    fn test_nested_recursion() {
        // μx. μy. A → B : msg. y
        let g1 = GlobalType::mu(
            "x",
            GlobalType::mu(
                "y",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")),
            ),
        );
        // μa. μb. A → B : msg. b (same structure, different names)
        let g2 = GlobalType::mu(
            "a",
            GlobalType::mu(
                "b",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("b")),
            ),
        );

        let db1 = GlobalTypeDB::from(&g1);
        let db2 = GlobalTypeDB::from(&g2);

        assert_eq!(db1, db2);

        // Check the structure: innermost var should have index 0
        assert_matches!(db1, GlobalTypeDB::Rec(outer) => {
            assert_matches!(*outer, GlobalTypeDB::Rec(inner) => {
                assert_matches!(*inner, GlobalTypeDB::Comm { ref branches, .. } => {
                    assert_matches!(branches[0].1, GlobalTypeDB::Var(0));
                });
            });
        });
    }

    #[test]
    fn test_reference_to_outer_binder() {
        // μx. μy. A → B : msg. x (reference to OUTER binder)
        let g = GlobalType::mu(
            "x",
            GlobalType::mu(
                "y",
                GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
            ),
        );

        let db = GlobalTypeDB::from(&g);

        // The variable x should have index 1 (one level out)
        assert_matches!(db, GlobalTypeDB::Rec(outer) => {
            assert_matches!(*outer, GlobalTypeDB::Rec(inner) => {
                assert_matches!(*inner, GlobalTypeDB::Comm { ref branches, .. } => {
                    assert_matches!(branches[0].1, GlobalTypeDB::Var(1));
                });
            });
        });
    }

    #[test]
    fn test_different_structures_not_equal() {
        // μx. A → B : msg. end
        let g1 = GlobalType::mu(
            "x",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::End),
        );
        // μx. A → B : msg. x
        let g2 = GlobalType::mu(
            "x",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
        );

        let db1 = GlobalTypeDB::from(&g1);
        let db2 = GlobalTypeDB::from(&g2);

        assert_ne!(db1, db2);
    }

    #[test]
    fn test_normalize_branch_order() {
        // A → B : {b.end, a.end}
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("b"), GlobalType::End),
                (Label::new("a"), GlobalType::End),
            ],
        );

        let db = GlobalTypeDB::from(&g).normalize();

        assert_matches!(db, GlobalTypeDB::Comm { branches, .. } => {
            assert_eq!(branches[0].0.name, "a");
            assert_eq!(branches[1].0.name, "b");
        });
    }

    #[test]
    fn test_unbound_variable() {
        // A → B : msg. t (t is unbound)
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t"));

        let db = GlobalTypeDB::from(&g);

        // Unbound variables get index 0 (beyond empty env)
        assert_matches!(db, GlobalTypeDB::Comm { ref branches, .. } => {
            assert_matches!(branches[0].1, GlobalTypeDB::Var(0));
        });
    }

    #[test]
    fn test_local_type_send_recv() {
        // μx. !B{msg.?A{reply.x}}
        let t = LocalTypeR::mu(
            "x",
            LocalTypeR::send(
                "B",
                Label::new("msg"),
                LocalTypeR::recv("A", Label::new("reply"), LocalTypeR::var("x")),
            ),
        );

        let db = LocalTypeRDB::from(&t);

        assert_matches!(db, LocalTypeRDB::Rec(body) => {
            assert_matches!(*body, LocalTypeRDB::Send { ref partner, ref branches } => {
                assert_eq!(partner, "B");
                assert_matches!(&branches[0].1, LocalTypeRDB::Recv { partner, branches: recv_branches } => {
                    assert_eq!(partner, "A");
                    assert_matches!(recv_branches[0].1, LocalTypeRDB::Var(0));
                });
            });
        });
    }
}
