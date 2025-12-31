//! Local Session Types for Multiparty Protocols
//!
//! This module defines local types that describe protocols from a single participant's
//! perspective. Local types are obtained by projecting global types onto specific roles.
//!
//! Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//!
//! # Lean Correspondence
//!
//! The core `LocalTypeR` enum mirrors `lean/Rumpsteak/Protocol/LocalTypeR.lean`:
//! - `LocalTypeR::End` ↔ Lean's `LocalTypeR.end`
//! - `LocalTypeR::Send` ↔ Lean's `LocalTypeR.send`
//! - `LocalTypeR::Recv` ↔ Lean's `LocalTypeR.recv`
//! - `LocalTypeR::Mu` ↔ Lean's `LocalTypeR.mu`
//! - `LocalTypeR::Var` ↔ Lean's `LocalTypeR.var`

use crate::Label;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

/// Core local type matching Lean's `LocalTypeR`.
///
/// This is the minimal type used for validation and correspondence proofs.
/// For code generation, see the extended `LocalType` in the DSL crate.
///
/// # Examples
///
/// ```
/// use rumpsteak_types::{LocalTypeR, Label};
///
/// // Simple send: !B{msg.end}
/// let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// assert!(lt.well_formed());
///
/// // Recursive type: μt. !B{msg.t}
/// let rec = LocalTypeR::mu(
///     "t",
///     LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
/// );
/// assert!(rec.well_formed());
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LocalTypeR {
    /// Protocol termination
    End,
    /// Internal choice: send to partner with choice of continuations
    Send {
        partner: String,
        branches: Vec<(Label, LocalTypeR)>,
    },
    /// External choice: receive from partner with offered continuations
    Recv {
        partner: String,
        branches: Vec<(Label, LocalTypeR)>,
    },
    /// Recursive type: μt.T binds variable t in body T
    Mu { var: String, body: Box<LocalTypeR> },
    /// Type variable: reference to enclosing μ-binder
    Var(String),
}

impl LocalTypeR {
    /// Create a simple send with one label
    #[must_use]
    pub fn send(partner: impl Into<String>, label: Label, cont: LocalTypeR) -> Self {
        LocalTypeR::Send {
            partner: partner.into(),
            branches: vec![(label, cont)],
        }
    }

    /// Create a send with multiple branches
    #[must_use]
    pub fn send_choice(partner: impl Into<String>, branches: Vec<(Label, LocalTypeR)>) -> Self {
        LocalTypeR::Send {
            partner: partner.into(),
            branches,
        }
    }

    /// Create a simple recv with one label
    #[must_use]
    pub fn recv(partner: impl Into<String>, label: Label, cont: LocalTypeR) -> Self {
        LocalTypeR::Recv {
            partner: partner.into(),
            branches: vec![(label, cont)],
        }
    }

    /// Create a recv with multiple branches
    #[must_use]
    pub fn recv_choice(partner: impl Into<String>, branches: Vec<(Label, LocalTypeR)>) -> Self {
        LocalTypeR::Recv {
            partner: partner.into(),
            branches,
        }
    }

    /// Create a recursive type
    #[must_use]
    pub fn mu(var: impl Into<String>, body: LocalTypeR) -> Self {
        LocalTypeR::Mu {
            var: var.into(),
            body: Box::new(body),
        }
    }

    /// Create a type variable
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        LocalTypeR::Var(name.into())
    }

    /// Extract free type variables from a local type.
    ///
    /// Corresponds to Lean's `LocalTypeR.freeVars`.
    #[must_use]
    pub fn free_vars(&self) -> Vec<String> {
        let mut result = Vec::new();
        let mut bound = HashSet::new();
        self.collect_free_vars(&mut result, &mut bound);
        result
    }

    fn collect_free_vars(&self, free: &mut Vec<String>, bound: &mut HashSet<String>) {
        match self {
            LocalTypeR::End => {}
            LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
                for (_, cont) in branches {
                    cont.collect_free_vars(free, bound);
                }
            }
            LocalTypeR::Mu { var, body } => {
                bound.insert(var.clone());
                body.collect_free_vars(free, bound);
                bound.remove(var);
            }
            LocalTypeR::Var(t) => {
                if !bound.contains(t) && !free.contains(t) {
                    free.push(t.clone());
                }
            }
        }
    }

    /// Substitute a local type for a variable.
    ///
    /// Corresponds to Lean's `LocalTypeR.substitute`.
    #[must_use]
    pub fn substitute(&self, var_name: &str, replacement: &LocalTypeR) -> LocalTypeR {
        match self {
            LocalTypeR::End => LocalTypeR::End,
            LocalTypeR::Send { partner, branches } => LocalTypeR::Send {
                partner: partner.clone(),
                branches: branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), cont.substitute(var_name, replacement)))
                    .collect(),
            },
            LocalTypeR::Recv { partner, branches } => LocalTypeR::Recv {
                partner: partner.clone(),
                branches: branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), cont.substitute(var_name, replacement)))
                    .collect(),
            },
            LocalTypeR::Mu { var, body } => {
                if var == var_name {
                    // Variable is shadowed by this binder
                    LocalTypeR::Mu {
                        var: var.clone(),
                        body: body.clone(),
                    }
                } else {
                    LocalTypeR::Mu {
                        var: var.clone(),
                        body: Box::new(body.substitute(var_name, replacement)),
                    }
                }
            }
            LocalTypeR::Var(t) => {
                if t == var_name {
                    replacement.clone()
                } else {
                    LocalTypeR::Var(t.clone())
                }
            }
        }
    }

    /// Unfold one level of recursion: μt.T ↦ T[μt.T/t]
    ///
    /// Corresponds to Lean's `LocalTypeR.unfold`.
    #[must_use]
    pub fn unfold(&self) -> LocalTypeR {
        match self {
            LocalTypeR::Mu { var, body } => body.substitute(var, self),
            _ => self.clone(),
        }
    }

    /// Compute the dual of a local type (swap send/recv).
    ///
    /// The dual of role A's view is role B's view when A and B are the only participants.
    /// Corresponds to Lean's `LocalTypeR.dual`.
    #[must_use]
    pub fn dual(&self) -> LocalTypeR {
        match self {
            LocalTypeR::End => LocalTypeR::End,
            LocalTypeR::Send { partner, branches } => LocalTypeR::Recv {
                partner: partner.clone(),
                branches: branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), cont.dual()))
                    .collect(),
            },
            LocalTypeR::Recv { partner, branches } => LocalTypeR::Send {
                partner: partner.clone(),
                branches: branches
                    .iter()
                    .map(|(l, cont)| (l.clone(), cont.dual()))
                    .collect(),
            },
            LocalTypeR::Mu { var, body } => LocalTypeR::Mu {
                var: var.clone(),
                body: Box::new(body.dual()),
            },
            LocalTypeR::Var(t) => LocalTypeR::Var(t.clone()),
        }
    }

    /// Check if all recursion variables are bound.
    ///
    /// Corresponds to Lean's `LocalTypeR.allVarsBound`.
    #[must_use]
    pub fn all_vars_bound(&self) -> bool {
        self.check_vars_bound(&HashSet::new())
    }

    fn check_vars_bound(&self, bound: &HashSet<String>) -> bool {
        match self {
            LocalTypeR::End => true,
            LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => branches
                .iter()
                .all(|(_, cont)| cont.check_vars_bound(bound)),
            LocalTypeR::Mu { var, body } => {
                let mut new_bound = bound.clone();
                new_bound.insert(var.clone());
                body.check_vars_bound(&new_bound)
            }
            LocalTypeR::Var(t) => bound.contains(t),
        }
    }

    /// Check if each choice has at least one branch.
    ///
    /// Corresponds to Lean's `LocalTypeR.allChoicesNonEmpty`.
    #[must_use]
    pub fn all_choices_non_empty(&self) -> bool {
        match self {
            LocalTypeR::End => true,
            LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
                !branches.is_empty()
                    && branches
                        .iter()
                        .all(|(_, cont)| cont.all_choices_non_empty())
            }
            LocalTypeR::Mu { body, .. } => body.all_choices_non_empty(),
            LocalTypeR::Var(_) => true,
        }
    }

    /// Well-formedness predicate for local types.
    ///
    /// Corresponds to Lean's `LocalTypeR.wellFormed`.
    /// A local type is well-formed if:
    /// 1. All recursion variables are bound
    /// 2. Each choice has at least one branch
    #[must_use]
    pub fn well_formed(&self) -> bool {
        self.all_vars_bound() && self.all_choices_non_empty()
    }

    /// Count the depth of a local type (for termination proofs).
    ///
    /// Corresponds to Lean's `LocalTypeR.depth`.
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            LocalTypeR::End => 0,
            LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
                1 + branches.iter().map(|(_, t)| t.depth()).max().unwrap_or(0)
            }
            LocalTypeR::Mu { body, .. } => 1 + body.depth(),
            LocalTypeR::Var(_) => 0,
        }
    }

    /// Check if a local type is guarded (no immediate recursion).
    ///
    /// Corresponds to Lean's `LocalTypeR.isGuarded`.
    #[must_use]
    pub fn is_guarded(&self) -> bool {
        match self {
            LocalTypeR::End => true,
            LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
                branches.iter().all(|(_, cont)| cont.is_guarded())
            }
            LocalTypeR::Mu { body, .. } => match body.as_ref() {
                LocalTypeR::Var(_) | LocalTypeR::Mu { .. } => false,
                _ => body.is_guarded(),
            },
            LocalTypeR::Var(_) => true,
        }
    }

    /// Extract all labels from a local type.
    ///
    /// Corresponds to Lean's `LocalTypeR.labels`.
    #[must_use]
    pub fn labels(&self) -> Vec<String> {
        match self {
            LocalTypeR::End | LocalTypeR::Var(_) => vec![],
            LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
                branches.iter().map(|(l, _)| l.name.clone()).collect()
            }
            LocalTypeR::Mu { body, .. } => body.labels(),
        }
    }

    /// Extract all partners from a local type.
    ///
    /// Corresponds to Lean's `LocalTypeR.partners`.
    #[must_use]
    pub fn partners(&self) -> Vec<String> {
        let mut result = HashSet::new();
        self.collect_partners(&mut result);
        result.into_iter().collect()
    }

    fn collect_partners(&self, partners: &mut HashSet<String>) {
        match self {
            LocalTypeR::End | LocalTypeR::Var(_) => {}
            LocalTypeR::Send { partner, branches } | LocalTypeR::Recv { partner, branches } => {
                partners.insert(partner.clone());
                for (_, cont) in branches {
                    cont.collect_partners(partners);
                }
            }
            LocalTypeR::Mu { body, .. } => body.collect_partners(partners),
        }
    }

    /// Check if a local type mentions a specific partner.
    #[must_use]
    pub fn mentions_partner(&self, role: &str) -> bool {
        self.partners().contains(&role.to_string())
    }

    /// Check if this is an internal choice (send)
    #[must_use]
    pub fn is_send(&self) -> bool {
        matches!(self, LocalTypeR::Send { .. })
    }

    /// Check if this is an external choice (recv)
    #[must_use]
    pub fn is_recv(&self) -> bool {
        matches!(self, LocalTypeR::Recv { .. })
    }

    /// Check if this is a terminated type
    #[must_use]
    pub fn is_end(&self) -> bool {
        matches!(self, LocalTypeR::End)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PayloadSort;
    use assert_matches::assert_matches;

    #[test]
    fn test_simple_local_type() {
        // !B{msg.end}
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        assert!(lt.well_formed());
        assert_eq!(lt.partners().len(), 1);
        assert!(lt.mentions_partner("B"));
    }

    #[test]
    fn test_recursive_local_type() {
        // μt. !B{msg.t}
        let lt = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        assert!(lt.well_formed());
        assert!(lt.all_vars_bound());
    }

    #[test]
    fn test_dual() {
        // !B{msg.end} dual is ?B{msg.end}
        let send = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let recv = send.dual();

        assert_matches!(recv, LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "B");
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, "msg");
        });
    }

    #[test]
    fn test_unfold() {
        // μt. !B{msg.t} unfolds to !B{msg.(μt. !B{msg.t})}
        let lt = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        let unfolded = lt.unfold();

        assert_matches!(unfolded, LocalTypeR::Send { partner, branches } => {
            assert_eq!(partner, "B");
            assert_matches!(branches[0].1, LocalTypeR::Mu { .. });
        });
    }

    #[test]
    fn test_substitute() {
        let lt = LocalTypeR::var("t");
        let replacement = LocalTypeR::End;
        assert_eq!(lt.substitute("t", &replacement), LocalTypeR::End);
        assert_eq!(lt.substitute("s", &replacement), LocalTypeR::var("t"));
    }

    #[test]
    fn test_unbound_variable() {
        // !B{msg.t} where t is unbound
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t"));
        assert!(!lt.all_vars_bound());
        assert!(!lt.well_formed());
    }

    #[test]
    fn test_guarded() {
        // μt. t is not guarded
        let unguarded = LocalTypeR::mu("t", LocalTypeR::var("t"));
        assert!(!unguarded.is_guarded());

        // μt. !B{msg.t} is guarded
        let guarded = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        assert!(guarded.is_guarded());
    }

    #[test]
    fn test_free_vars() {
        // μt. !B{msg.s} has free var s
        let lt = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("s")),
        );
        let free = lt.free_vars();
        assert_eq!(free, vec!["s"]);
    }

    #[test]
    fn test_choice_with_payload() {
        let branches = vec![
            (
                Label::with_sort("accept", PayloadSort::Bool),
                LocalTypeR::End,
            ),
            (Label::with_sort("data", PayloadSort::Nat), LocalTypeR::End),
        ];
        let lt = LocalTypeR::recv_choice("A", branches);
        assert!(lt.well_formed());
        assert_eq!(lt.labels(), vec!["accept", "data"]);
    }

    #[test]
    fn test_depth() {
        let lt = LocalTypeR::send(
            "B",
            Label::new("outer"),
            LocalTypeR::send("C", Label::new("inner"), LocalTypeR::End),
        );
        assert_eq!(lt.depth(), 2);
    }

    #[test]
    fn test_is_send_recv() {
        let send = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let recv = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);

        assert!(send.is_send());
        assert!(!send.is_recv());
        assert!(recv.is_recv());
        assert!(!recv.is_send());
    }
}
