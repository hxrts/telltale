//! Coherence Predicates for Global Types
//!
//! This module implements the coherence bundle from the ECOOP 2025 paper
//! "Mechanised Subject Reduction for Multiparty Asynchronous Session Types".
//!
//! A global type is coherent if it satisfies several well-formedness predicates
//! that ensure safe protocol execution.
//!
//! # Lean Correspondence
//!
//! This module mirrors `lean/Telltale/Protocol/Coherence.lean`:
//! - `CoherentG` ↔ Lean's `coherentG` structure
//! - `projectable` ↔ Lean's `projectable` definition
//! - `check_coherent` bundles all predicates

use crate::merge::can_merge;
use crate::projection::MemoizedProjector;
use crate::semantics::{can_step, step, GlobalAction};
use crate::well_formedness::unique_labels;
use telltale_types::GlobalType;
use std::collections::HashSet;

/// Coherence bundle for global types.
///
/// Corresponds to Lean's `coherentG` structure.
/// A coherent global type satisfies all of the following:
///
/// - `linear`: Linearity predicate (placeholder, always true for now)
/// - `size`: All communications have non-empty branches
/// - `action`: Sender ≠ receiver in all communications
/// - `uniq_labels`: Branch labels are unique in each choice
/// - `projectable`: Every role has a successful projection
/// - `good`: Enabledness implies step exists (goodG condition)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoherentG {
    /// Linearity predicate (placeholder - always true for now)
    pub linear: bool,
    /// Size predicate: all communications have non-empty branches
    pub size: bool,
    /// Action predicate: sender ≠ receiver in each communication
    pub action: bool,
    /// Label uniqueness: branch labels are unique in each choice
    pub uniq_labels: bool,
    /// Total projection: every role has a successful projection
    pub projectable: bool,
    /// Good global: enabledness implies step existence
    pub good: bool,
}

impl CoherentG {
    /// Check if all coherence conditions are satisfied
    #[must_use]
    pub fn is_coherent(&self) -> bool {
        self.linear && self.size && self.action && self.uniq_labels && self.projectable && self.good
    }
}

/// Check if a global type is coherent, returning the coherence bundle.
///
/// This performs all coherence checks and returns the results as a bundle.
///
/// # Examples
///
/// ```
/// use telltale_theory::check_coherent;
/// use telltale_types::{GlobalType, Label};
///
/// let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
/// let bundle = check_coherent(&g);
/// assert!(bundle.is_coherent());
/// ```
#[must_use]
pub fn check_coherent(g: &GlobalType) -> CoherentG {
    CoherentG {
        linear: linear_pred(g),
        size: size_pred(g),
        action: action_pred(g),
        uniq_labels: unique_labels(g),
        projectable: projectable(g),
        good: good_g(g),
    }
}

/// Placeholder linearity predicate for globals.
///
/// Corresponds to Lean's `linearPred`.
/// Currently always returns true (refinement needed for full linearity checks).
#[must_use]
pub fn linear_pred(_g: &GlobalType) -> bool {
    // Linearity would ensure channels are used without races and choices are well-scoped.
    // We stub this out to mirror the current Lean placeholder and keep checks explicit
    // until a full linearity predicate is implemented.
    true
}

/// Size predicate: each communication has at least one branch.
///
/// Corresponds to Lean's `sizePred`.
#[must_use]
pub fn size_pred(g: &GlobalType) -> bool {
    g.all_comms_non_empty()
}

/// Action predicate: sender ≠ receiver in each communication.
///
/// Corresponds to Lean's `actionPred`.
#[must_use]
pub fn action_pred(g: &GlobalType) -> bool {
    action_pred_rec(g)
}

fn action_pred_rec(g: &GlobalType) -> bool {
    match g {
        GlobalType::End => true,
        GlobalType::Var(_) => true,
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            if sender == receiver {
                return false;
            }
            branches.iter().all(|(_, cont)| action_pred_rec(cont))
        }
        GlobalType::Mu { body, .. } => action_pred_rec(body),
    }
}

/// Total projection check: every role has a successful projection.
///
/// Corresponds to Lean's `projectable`.
/// This verifies that projection would succeed for all participating roles.
///
/// # Examples
///
/// ```
/// use telltale_theory::projectable;
/// use telltale_types::{GlobalType, Label};
///
/// let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
/// assert!(projectable(&g));
/// ```
#[must_use]
pub fn projectable(g: &GlobalType) -> bool {
    // Get all roles mentioned in the global type
    let roles = g.roles();
    let mut projector = MemoizedProjector::new();

    // Check that projection would succeed for each role
    // For now, we check structural properties that ensure projection succeeds
    for role in &roles {
        if !can_project_role(g, role, &mut HashSet::new(), &mut projector) {
            return false;
        }
    }
    true
}

/// Check if a specific role can be projected from the global type.
///
/// For non-participant roles in a choice, this verifies that the projected
/// continuations from all branches can be merged together.
fn can_project_role(
    g: &GlobalType,
    role: &str,
    visited: &mut HashSet<GlobalType>,
    projector: &mut MemoizedProjector,
) -> bool {
    if visited.contains(g) {
        return true; // Assume projectable for cycles
    }
    visited.insert(g.clone());

    match g {
        GlobalType::End => true,
        GlobalType::Var(_) => true,
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            // Role involved: check all branches are projectable
            if sender == role || receiver == role {
                branches
                    .iter()
                    .all(|(_, cont)| can_project_role(cont, role, visited, projector))
            } else {
                // Role not involved: branches must be mergeable
                if branches.is_empty() {
                    return false;
                }

                // First check all continuations are recursively projectable
                if !branches
                    .iter()
                    .all(|(_, cont)| can_project_role(cont, role, visited, projector))
                {
                    return false;
                }

                // Then verify the projected continuations can be merged
                // Project each continuation for this role
                let mut projected = Vec::with_capacity(branches.len());
                for (_, cont) in branches {
                    match projector.project(cont, role) {
                        Ok(local) => projected.push(local),
                        Err(_) => return false,
                    }
                }

                // If any projection failed, not projectable
                if projected.len() != branches.len() {
                    return false;
                }

                // Check that all projected types can be merged pairwise
                if projected.len() <= 1 {
                    return true;
                }

                // Check that each pair can merge (transitive property)
                let first = &projected[0];
                for other in &projected[1..] {
                    if !can_merge(first, other) {
                        return false;
                    }
                }

                true
            }
        }
        GlobalType::Mu { body, .. } => {
            // Check body is projectable
            can_project_role(body, role, visited, projector)
        }
    }
}

/// Good global check: enabledness implies step existence.
///
/// Corresponds to Lean's `goodG`.
/// For every action that is enabled (can_step returns true),
/// a step must exist (step returns Some).
#[must_use]
pub fn good_g(g: &GlobalType) -> bool {
    good_g_fuel(g, 100, &mut HashSet::new())
}

fn good_g_fuel(g: &GlobalType, fuel: usize, visited: &mut HashSet<GlobalType>) -> bool {
    if fuel == 0 {
        return true; // Assume good if we run out of fuel
    }

    if visited.contains(g) {
        return true; // Avoid infinite loops
    }
    visited.insert(g.clone());

    match g {
        GlobalType::End => true,
        GlobalType::Var(_) => true,
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            // Check all head actions have steps
            for (l, cont) in branches {
                let act = GlobalAction::new(sender, receiver, l.clone());
                if can_step(g, &act) && step(g, &act).is_none() {
                    return false;
                }
                // Recursively check continuations
                if !good_g_fuel(cont, fuel - 1, visited) {
                    return false;
                }
            }
            true
        }
        GlobalType::Mu { .. } => {
            // Check the unfolded type (unfold handles substitution)
            let unfolded = g.unfold();
            good_g_fuel(&unfolded, fuel - 1, visited)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::Label;

    #[test]
    fn test_coherent_simple() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let bundle = check_coherent(&g);
        assert!(bundle.is_coherent());
    }

    #[test]
    fn test_coherent_choice() {
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("accept"), GlobalType::End),
                (Label::new("reject"), GlobalType::End),
            ],
        );
        let bundle = check_coherent(&g);
        assert!(bundle.is_coherent());
    }

    #[test]
    fn test_coherent_recursive() {
        let g = GlobalType::mu(
            "t",
            GlobalType::comm(
                "A",
                "B",
                vec![
                    (Label::new("continue"), GlobalType::var("t")),
                    (Label::new("stop"), GlobalType::End),
                ],
            ),
        );
        let bundle = check_coherent(&g);
        assert!(bundle.is_coherent());
    }

    #[test]
    fn test_incoherent_self_comm() {
        let g = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
        let bundle = check_coherent(&g);
        assert!(!bundle.action);
        assert!(!bundle.is_coherent());
    }

    #[test]
    fn test_incoherent_duplicate_labels() {
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("msg"), GlobalType::End),
                (Label::new("msg"), GlobalType::End),
            ],
        );
        let bundle = check_coherent(&g);
        assert!(!bundle.uniq_labels);
        assert!(!bundle.is_coherent());
    }

    #[test]
    fn test_incoherent_empty_branches() {
        let g = GlobalType::Comm {
            sender: "A".to_string(),
            receiver: "B".to_string(),
            branches: vec![],
        };
        let bundle = check_coherent(&g);
        assert!(!bundle.size);
        assert!(!bundle.is_coherent());
    }

    #[test]
    fn test_projectable_simple() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        assert!(projectable(&g));
    }

    #[test]
    fn test_projectable_three_party() {
        // A -> B: m1. B -> C: m2. end
        let g = GlobalType::send(
            "A",
            "B",
            Label::new("m1"),
            GlobalType::send("B", "C", Label::new("m2"), GlobalType::End),
        );
        assert!(projectable(&g));
    }

    #[test]
    fn test_not_projectable_non_mergeable_branches() {
        // A -> B: { yes: end, no: C -> D: msg. end }
        // Role C is not involved in the choice, but:
        // - "yes" branch projects C to: End
        // - "no" branch projects C to: Send D: msg. End
        // These cannot merge, so C is not projectable
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("yes"), GlobalType::End),
                (
                    Label::new("no"),
                    GlobalType::send("C", "D", Label::new("msg"), GlobalType::End),
                ),
            ],
        );
        assert!(!projectable(&g));
    }

    #[test]
    fn test_projectable_mergeable_branches_identical_sends() {
        // A -> B: { yes: C -> D: msg. end, no: C -> D: msg. end }
        // Role C projects to: Send D: msg. end in both branches (identical)
        // These can merge because labels are identical
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (
                    Label::new("yes"),
                    GlobalType::send("C", "D", Label::new("msg"), GlobalType::End),
                ),
                (
                    Label::new("no"),
                    GlobalType::send("C", "D", Label::new("msg"), GlobalType::End),
                ),
            ],
        );
        assert!(projectable(&g));
    }

    #[test]
    fn test_projectable_mergeable_branches_recv_union() {
        // A -> B: { yes: A -> C: m1. end, no: A -> C: m2. end }
        //
        // Role C is not involved in the outer choice, so its projections must merge:
        // - "yes" branch: C projects to Recv A: m1. end
        // - "no" branch: C projects to Recv A: m2. end
        //
        // Recvs with different labels CAN merge (union of labels), so:
        // G↓C = ?A{m1: end, m2: end}
        //
        // Role A is the sender in both communications, so it doesn't need to merge.
        // Role B is the receiver but A->C happens after, so B merges End with End.
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (
                    Label::new("yes"),
                    GlobalType::send("A", "C", Label::new("m1"), GlobalType::End),
                ),
                (
                    Label::new("no"),
                    GlobalType::send("A", "C", Label::new("m2"), GlobalType::End),
                ),
            ],
        );
        assert!(projectable(&g));
    }

    #[test]
    fn test_not_projectable_different_send_labels() {
        // A -> B: { yes: C -> D: m1. end, no: C -> D: m2. end }
        // Role C projects to sends with DIFFERENT labels
        // Sends require identical label sets to merge, so this fails
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (
                    Label::new("yes"),
                    GlobalType::send("C", "D", Label::new("m1"), GlobalType::End),
                ),
                (
                    Label::new("no"),
                    GlobalType::send("C", "D", Label::new("m2"), GlobalType::End),
                ),
            ],
        );
        assert!(!projectable(&g));
    }

    #[test]
    fn test_size_pred() {
        let good = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        assert!(size_pred(&good));

        let bad = GlobalType::Comm {
            sender: "A".to_string(),
            receiver: "B".to_string(),
            branches: vec![],
        };
        assert!(!size_pred(&bad));
    }

    #[test]
    fn test_action_pred() {
        let good = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        assert!(action_pred(&good));

        let bad = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
        assert!(!action_pred(&bad));
    }

    #[test]
    fn test_good_g() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        assert!(good_g(&g));
    }

    #[test]
    fn test_good_g_choice() {
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("yes"), GlobalType::End),
                (Label::new("no"), GlobalType::End),
            ],
        );
        assert!(good_g(&g));
    }
}
