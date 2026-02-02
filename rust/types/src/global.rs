//! Global Types for Multiparty Session Type Protocols
//!
//! This module defines global types that describe protocols from a bird's-eye view.
//! Global types specify the complete interaction pattern between all participants,
//! including message exchanges, choices, and recursive behavior.
//!
//! Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//!
//! # Lean Correspondence
//!
//! This module mirrors the definitions in `lean/Telltale/Protocol/GlobalType.lean`:
//! - `PayloadSort` ↔ Lean's `PayloadSort`
//! - `GlobalType` ↔ Lean's `GlobalType`

use crate::Label;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

/// Payload sort types for message payloads.
///
/// Corresponds to Lean's `PayloadSort` inductive type.
/// These represent the data types that can be sent in messages.
///
/// # Examples
///
/// ```
/// use telltale_types::PayloadSort;
///
/// let unit = PayloadSort::Unit;
/// assert!(unit.is_simple());
///
/// let pair = PayloadSort::prod(PayloadSort::Nat, PayloadSort::Bool);
/// assert!(!pair.is_simple());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum PayloadSort {
    /// Unit type (no payload)
    #[default]
    Unit,
    /// Natural numbers
    Nat,
    /// Booleans
    Bool,
    /// Strings
    String,
    /// Real numbers (floating point physical quantities)
    Real,
    /// Fixed-size vectors (e.g. configuration space, phase space)
    Vector(usize),
    /// Product types (pairs)
    Prod(Box<PayloadSort>, Box<PayloadSort>),
}

impl PayloadSort {
    /// Create a product sort
    #[must_use]
    pub fn prod(left: PayloadSort, right: PayloadSort) -> Self {
        PayloadSort::Prod(Box::new(left), Box::new(right))
    }

    /// Create a vector sort
    #[must_use]
    pub fn vector(n: usize) -> Self {
        PayloadSort::Vector(n)
    }

    /// Check if this is a simple (non-compound) sort
    #[must_use]
    pub fn is_simple(&self) -> bool {
        !matches!(self, PayloadSort::Prod(_, _) | PayloadSort::Vector(_))
    }
}

impl std::fmt::Display for PayloadSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PayloadSort::Unit => write!(f, "Unit"),
            PayloadSort::Nat => write!(f, "Nat"),
            PayloadSort::Bool => write!(f, "Bool"),
            PayloadSort::String => write!(f, "String"),
            PayloadSort::Real => write!(f, "Real"),
            PayloadSort::Vector(n) => write!(f, "Vector({})", n),
            PayloadSort::Prod(l, r) => write!(f, "({} × {})", l, r),
        }
    }
}

/// Global types describe protocols from the bird's-eye view.
///
/// Corresponds to Lean's `GlobalType` inductive type.
///
/// # Syntax
///
/// - `End`: Protocol termination
/// - `Comm { sender, receiver, branches }`: Communication with labeled branches
/// - `Mu { var, body }`: Recursive type μt.G
/// - `Var(t)`: Type variable reference
///
/// The `Comm` variant models `p → q : {l₁(S₁).G₁, l₂(S₂).G₂, ...}`
/// where the sender p chooses which branch to take.
///
/// # Examples
///
/// ```
/// use telltale_types::{GlobalType, Label};
///
/// // Simple protocol: A -> B: hello. end
/// let g = GlobalType::send("A", "B", Label::new("hello"), GlobalType::End);
/// assert!(g.well_formed());
///
/// // Recursive protocol: μt. A -> B: msg. t
/// let rec = GlobalType::mu(
///     "t",
///     GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
/// );
/// assert!(rec.well_formed());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum GlobalType {
    /// Protocol termination
    End,
    /// Communication: sender → receiver with choice of labeled continuations
    Comm {
        sender: String,
        receiver: String,
        branches: Vec<(Label, GlobalType)>,
    },
    /// Recursive type: μt.G binds variable t in body G
    Mu { var: String, body: Box<GlobalType> },
    /// Type variable: reference to enclosing μ-binder
    Var(String),
}

impl GlobalType {
    /// Create a simple send without choice
    #[must_use]
    pub fn send(
        sender: impl Into<String>,
        receiver: impl Into<String>,
        label: Label,
        cont: GlobalType,
    ) -> Self {
        GlobalType::Comm {
            sender: sender.into(),
            receiver: receiver.into(),
            branches: vec![(label, cont)],
        }
    }

    /// Create a communication with multiple branches
    #[must_use]
    pub fn comm(
        sender: impl Into<String>,
        receiver: impl Into<String>,
        branches: Vec<(Label, GlobalType)>,
    ) -> Self {
        GlobalType::Comm {
            sender: sender.into(),
            receiver: receiver.into(),
            branches,
        }
    }

    /// Create a recursive type
    #[must_use]
    pub fn mu(var: impl Into<String>, body: GlobalType) -> Self {
        GlobalType::Mu {
            var: var.into(),
            body: Box::new(body),
        }
    }

    /// Create a type variable
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        GlobalType::Var(name.into())
    }

    /// Extract all role names from this global type.
    ///
    /// Corresponds to Lean's `GlobalType.roles`.
    #[must_use]
    pub fn roles(&self) -> Vec<String> {
        let mut result = HashSet::new();
        self.collect_roles(&mut result);
        result.into_iter().collect()
    }

    fn collect_roles(&self, roles: &mut HashSet<String>) {
        match self {
            GlobalType::End => {}
            GlobalType::Comm {
                sender,
                receiver,
                branches,
            } => {
                roles.insert(sender.clone());
                roles.insert(receiver.clone());
                for (_, cont) in branches {
                    cont.collect_roles(roles);
                }
            }
            GlobalType::Mu { body, .. } => body.collect_roles(roles),
            GlobalType::Var(_) => {}
        }
    }

    /// Extract free type variables from this global type.
    ///
    /// Corresponds to Lean's `GlobalType.freeVars`.
    #[must_use]
    pub fn free_vars(&self) -> Vec<String> {
        let mut result = Vec::new();
        let mut bound = HashSet::new();
        self.collect_free_vars(&mut result, &mut bound);
        result
    }

    fn collect_free_vars(&self, free: &mut Vec<String>, bound: &mut HashSet<String>) {
        match self {
            GlobalType::End => {}
            GlobalType::Comm { branches, .. } => {
                for (_, cont) in branches {
                    cont.collect_free_vars(free, bound);
                }
            }
            GlobalType::Mu { var, body } => {
                bound.insert(var.clone());
                body.collect_free_vars(free, bound);
                bound.remove(var);
            }
            GlobalType::Var(t) => {
                if !bound.contains(t) && !free.contains(t) {
                    free.push(t.clone());
                }
            }
        }
    }

    /// Substitute a global type for a variable.
    ///
    /// Corresponds to Lean's `GlobalType.substitute`.
    #[must_use]
    pub fn substitute(&self, var_name: &str, replacement: &GlobalType) -> GlobalType {
        match self {
            GlobalType::End => GlobalType::End,
            GlobalType::Comm {
                sender,
                receiver,
                branches,
            } => GlobalType::Comm {
                sender: sender.clone(),
                receiver: receiver.clone(),
                branches: branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), cont.substitute(var_name, replacement)))
                    .collect(),
            },
            GlobalType::Mu { var, body } => {
                if var == var_name {
                    // Variable is shadowed by this binder
                    GlobalType::Mu {
                        var: var.clone(),
                        body: body.clone(),
                    }
                } else {
                    GlobalType::Mu {
                        var: var.clone(),
                        body: Box::new(body.substitute(var_name, replacement)),
                    }
                }
            }
            GlobalType::Var(t) => {
                if t == var_name {
                    replacement.clone()
                } else {
                    GlobalType::Var(t.clone())
                }
            }
        }
    }

    /// Unfold one level of recursion: μt.G ↦ G[μt.G/t]
    ///
    /// Corresponds to Lean's `GlobalType.unfold`.
    #[must_use]
    pub fn unfold(&self) -> GlobalType {
        match self {
            GlobalType::Mu { var, body } => body.substitute(var, self),
            _ => self.clone(),
        }
    }

    /// Check if all recursion variables are bound.
    ///
    /// Corresponds to Lean's `GlobalType.allVarsBound`.
    #[must_use]
    pub fn all_vars_bound(&self) -> bool {
        self.check_vars_bound(&HashSet::new())
    }

    fn check_vars_bound(&self, bound: &HashSet<String>) -> bool {
        match self {
            GlobalType::End => true,
            GlobalType::Comm { branches, .. } => branches
                .iter()
                .all(|(_, cont)| cont.check_vars_bound(bound)),
            GlobalType::Mu { var, body } => {
                let mut new_bound = bound.clone();
                new_bound.insert(var.clone());
                body.check_vars_bound(&new_bound)
            }
            GlobalType::Var(t) => bound.contains(t),
        }
    }

    /// Check if each communication has at least one branch.
    ///
    /// Corresponds to Lean's `GlobalType.allCommsNonEmpty`.
    #[must_use]
    pub fn all_comms_non_empty(&self) -> bool {
        match self {
            GlobalType::End => true,
            GlobalType::Comm { branches, .. } => {
                !branches.is_empty() && branches.iter().all(|(_, cont)| cont.all_comms_non_empty())
            }
            GlobalType::Mu { body, .. } => body.all_comms_non_empty(),
            GlobalType::Var(_) => true,
        }
    }

    /// Check if sender and receiver are different in each communication.
    ///
    /// Corresponds to Lean's `GlobalType.noSelfComm`.
    #[must_use]
    pub fn no_self_comm(&self) -> bool {
        match self {
            GlobalType::End => true,
            GlobalType::Comm {
                sender,
                receiver,
                branches,
            } => sender != receiver && branches.iter().all(|(_, cont)| cont.no_self_comm()),
            GlobalType::Mu { body, .. } => body.no_self_comm(),
            GlobalType::Var(_) => true,
        }
    }

    /// Well-formedness predicate for global types.
    ///
    /// Corresponds to Lean's `GlobalType.wellFormed`.
    /// A global type is well-formed if:
    /// 1. All recursion variables are bound
    /// 2. Each communication has at least one branch
    /// 3. Sender ≠ receiver in each communication
    /// 4. All recursion is guarded (no immediate recursion without communication)
    #[must_use]
    pub fn well_formed(&self) -> bool {
        self.all_vars_bound()
            && self.all_comms_non_empty()
            && self.no_self_comm()
            && self.is_guarded()
    }

    /// Check if a role participates in the global type.
    ///
    /// Corresponds to Lean's `GlobalType.mentionsRole`.
    #[must_use]
    pub fn mentions_role(&self, role: &str) -> bool {
        self.roles().contains(&role.to_string())
    }

    /// Count the depth of a global type (for termination proofs).
    ///
    /// Corresponds to Lean's `GlobalType.depth`.
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            GlobalType::End => 0,
            GlobalType::Comm { branches, .. } => {
                1 + branches.iter().map(|(_, g)| g.depth()).max().unwrap_or(0)
            }
            GlobalType::Mu { body, .. } => 1 + body.depth(),
            GlobalType::Var(_) => 0,
        }
    }

    /// Check if a global type is guarded (no immediate recursion without communication).
    ///
    /// Corresponds to Lean's `GlobalType.isGuarded`.
    #[must_use]
    pub fn is_guarded(&self) -> bool {
        match self {
            GlobalType::End => true,
            GlobalType::Comm { branches, .. } => branches.iter().all(|(_, cont)| cont.is_guarded()),
            GlobalType::Mu { body, .. } => match body.as_ref() {
                GlobalType::Var(_) | GlobalType::Mu { .. } => false,
                _ => body.is_guarded(),
            },
            GlobalType::Var(_) => true,
        }
    }

    /// Consume a communication from a global type.
    ///
    /// Corresponds to Lean's `GlobalType.consume`.
    /// G \ p →ℓ q represents the global type after the communication p →ℓ q
    /// has been performed.
    #[must_use]
    pub fn consume(&self, sender: &str, receiver: &str, label: &str) -> Option<GlobalType> {
        match self {
            GlobalType::Comm {
                sender: s,
                receiver: r,
                branches,
            } => {
                if s == sender && r == receiver {
                    branches
                        .iter()
                        .find(|(l, _)| l.name == label)
                        .map(|(_, cont)| cont.clone())
                } else {
                    None
                }
            }
            GlobalType::Mu { var, body } => {
                // Unfold and try again
                body.substitute(var, self).consume(sender, receiver, label)
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn test_simple_protocol() {
        // A -> B: hello. end
        let g = GlobalType::send("A", "B", Label::new("hello"), GlobalType::End);
        assert!(g.well_formed());
        assert_eq!(g.roles().len(), 2);
        assert!(g.mentions_role("A"));
        assert!(g.mentions_role("B"));
    }

    #[test]
    fn test_recursive_protocol() {
        // μt. A -> B: msg. t
        let g = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );
        assert!(g.well_formed());
        assert!(g.all_vars_bound());
    }

    #[test]
    fn test_unbound_variable() {
        // A -> B: msg. t (t is unbound)
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t"));
        assert!(!g.all_vars_bound());
        assert!(!g.well_formed());
    }

    #[test]
    fn test_self_communication() {
        // A -> A: msg. end (self-communication)
        let g = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
        assert!(!g.no_self_comm());
        assert!(!g.well_formed());
    }

    #[test]
    fn test_unfold() {
        // μt. A -> B: msg. t unfolds to A -> B: msg. (μt. A -> B: msg. t)
        let g = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );
        let unfolded = g.unfold();
        assert_matches!(unfolded, GlobalType::Comm { sender, receiver, branches } => {
            assert_eq!(sender, "A");
            assert_eq!(receiver, "B");
            assert_eq!(branches.len(), 1);
            // Continuation should be the original recursive type
            assert_matches!(branches[0].1, GlobalType::Mu { .. });
        });
    }

    #[test]
    fn test_substitute() {
        let g = GlobalType::var("t");
        let replacement = GlobalType::End;
        assert_eq!(g.substitute("t", &replacement), GlobalType::End);
        assert_eq!(g.substitute("s", &replacement), GlobalType::var("t"));
    }

    #[test]
    fn test_consume() {
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("accept"), GlobalType::End),
                (Label::new("reject"), GlobalType::End),
            ],
        );

        assert_eq!(g.consume("A", "B", "accept"), Some(GlobalType::End));
        assert_eq!(g.consume("A", "B", "reject"), Some(GlobalType::End));
        assert_eq!(g.consume("A", "B", "unknown"), None);
        assert_eq!(g.consume("B", "A", "accept"), None);
    }

    #[test]
    fn test_payload_sort() {
        let sort = PayloadSort::prod(PayloadSort::Nat, PayloadSort::Bool);
        assert!(!sort.is_simple());

        let label = Label::with_sort("data", sort);
        assert_eq!(label.name, "data");
    }

    #[test]
    fn test_guarded() {
        // μt. t is not guarded (immediate recursion)
        let unguarded = GlobalType::mu("t", GlobalType::var("t"));
        assert!(!unguarded.is_guarded());
        assert!(!unguarded.well_formed()); // Unguarded recursion should fail well_formed()

        // μt. A -> B: msg. t is guarded
        let guarded = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );
        assert!(guarded.is_guarded());
        assert!(guarded.well_formed()); // Guarded recursion should pass well_formed()
    }
}
