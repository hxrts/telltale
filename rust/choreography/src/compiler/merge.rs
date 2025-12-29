//! Local Type Merging for Projection
//!
//! This module implements the merge operation for local types, which is essential
//! for correct projection of global types to local types when a role is not
//! involved in a choice.
//!
//! Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//!
//! # Merge Semantics
//!
//! When projecting a global type `G` with a choice made by role `p` onto a role `q`
//! that is not `p` and doesn't receive the choice, we need to merge the projections
//! of all branches:
//!
//! ```text
//! G = p → r : {l₁.G₁, l₂.G₂}    (q ≠ p, q ≠ r)
//! G↓q = merge(G₁↓q, G₂↓q)
//! ```
//!
//! # Merge Rules
//!
//! The merge operation `T₁ ⊔ T₂` is defined as:
//!
//! 1. `end ⊔ end = end`
//! 2. `!q{lᵢ.Tᵢ} ⊔ !q{l'ⱼ.T'ⱼ} = !q{(lᵢ.Tᵢ) ∪ (l'ⱼ.T'ⱼ)}` if continuations with same labels are compatible
//! 3. `?p{lᵢ.Tᵢ} ⊔ ?p{l'ⱼ.T'ⱼ} = ?p{(lᵢ.Tᵢ) ∪ (l'ⱼ.T'ⱼ)}` if continuations with same labels are compatible
//! 4. `μt.T ⊔ μt.T' = μt.(T ⊔ T')` if T and T' use the same variable
//! 5. `t ⊔ t = t` for type variables
//!
//! The merge fails if the types have incompatible structure (different partners,
//! conflicting labels with different continuations, etc.).

use crate::ast::global_type::Label;
use crate::ast::local_type::LocalTypeR;
use std::collections::HashMap;
use thiserror::Error;

/// Errors that can occur during type merging
#[derive(Debug, Clone, Error)]
pub enum MergeError {
    /// Cannot merge End with a non-End type
    #[error("cannot merge end with non-end type: {0:?}")]
    EndMismatch(LocalTypeR),

    /// Cannot merge types with different partners
    #[error("partner mismatch in merge: expected {expected}, found {found}")]
    PartnerMismatch { expected: String, found: String },

    /// Cannot merge types with different directions (send vs recv)
    #[error("direction mismatch in merge: cannot merge send with recv")]
    DirectionMismatch,

    /// Labels with the same name have incompatible continuations
    #[error("incompatible continuations for label '{label}'")]
    IncompatibleContinuations { label: String },

    /// Cannot merge recursive types with different variable names
    #[error("recursive variable mismatch: expected {expected}, found {found}")]
    RecursiveVariableMismatch { expected: String, found: String },

    /// Cannot merge type variables with different names
    #[error("type variable mismatch: expected {expected}, found {found}")]
    VariableMismatch { expected: String, found: String },

    /// Merge of these types is not defined
    #[error("cannot merge incompatible types")]
    IncompatibleTypes,
}

/// Result type for merge operations
pub type MergeResult = Result<LocalTypeR, MergeError>;

/// Merge two local types.
///
/// This is the main entry point for the merge algorithm.
/// Returns `Ok(merged)` if the types can be merged, or `Err(error)` if they
/// have incompatible structure.
///
/// # Examples
///
/// ```ignore
/// use rumpsteak_aura_choreography::compiler::merge::merge;
/// use rumpsteak_aura_choreography::ast::local_type::LocalTypeR;
/// use rumpsteak_aura_choreography::ast::global_type::Label;
///
/// // Merging identical types yields the same type
/// let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let t2 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let merged = merge(&t1, &t2).unwrap();
/// assert_eq!(merged, t1);
///
/// // Merging sends with different labels creates a choice
/// let t1 = LocalTypeR::send("B", Label::new("yes"), LocalTypeR::End);
/// let t2 = LocalTypeR::send("B", Label::new("no"), LocalTypeR::End);
/// let merged = merge(&t1, &t2).unwrap();
/// // merged = !B{yes.end, no.end}
/// ```
pub fn merge(t1: &LocalTypeR, t2: &LocalTypeR) -> MergeResult {
    // Fast path: identical types
    if t1 == t2 {
        return Ok(t1.clone());
    }

    match (t1, t2) {
        // Rule 1: end ⊔ end = end
        (LocalTypeR::End, LocalTypeR::End) => Ok(LocalTypeR::End),

        // End with non-End is an error (unless one is End, in which case we could use the other)
        // Some formulations allow this, treating End as a neutral element
        (LocalTypeR::End, other) | (other, LocalTypeR::End) => {
            // In some systems, End is neutral. For strict merging, this is an error.
            // We'll be strict here but could make this configurable.
            Err(MergeError::EndMismatch(other.clone()))
        }

        // Rule 2: !q{branches₁} ⊔ !q{branches₂} = !q{branches₁ ∪ branches₂}
        (
            LocalTypeR::Send {
                partner: p1,
                branches: b1,
            },
            LocalTypeR::Send {
                partner: p2,
                branches: b2,
            },
        ) => {
            if p1 != p2 {
                return Err(MergeError::PartnerMismatch {
                    expected: p1.clone(),
                    found: p2.clone(),
                });
            }
            let merged_branches = merge_branches(b1, b2)?;
            Ok(LocalTypeR::Send {
                partner: p1.clone(),
                branches: merged_branches,
            })
        }

        // Rule 3: ?p{branches₁} ⊔ ?p{branches₂} = ?p{branches₁ ∪ branches₂}
        (
            LocalTypeR::Recv {
                partner: p1,
                branches: b1,
            },
            LocalTypeR::Recv {
                partner: p2,
                branches: b2,
            },
        ) => {
            if p1 != p2 {
                return Err(MergeError::PartnerMismatch {
                    expected: p1.clone(),
                    found: p2.clone(),
                });
            }
            let merged_branches = merge_branches(b1, b2)?;
            Ok(LocalTypeR::Recv {
                partner: p1.clone(),
                branches: merged_branches,
            })
        }

        // Rule 4: μt.T₁ ⊔ μt.T₂ = μt.(T₁ ⊔ T₂)
        (
            LocalTypeR::Mu {
                var: v1,
                body: body1,
            },
            LocalTypeR::Mu {
                var: v2,
                body: body2,
            },
        ) => {
            if v1 != v2 {
                return Err(MergeError::RecursiveVariableMismatch {
                    expected: v1.clone(),
                    found: v2.clone(),
                });
            }
            let merged_body = merge(body1, body2)?;
            Ok(LocalTypeR::Mu {
                var: v1.clone(),
                body: Box::new(merged_body),
            })
        }

        // Rule 5: t ⊔ t = t
        (LocalTypeR::Var(v1), LocalTypeR::Var(v2)) => {
            if v1 != v2 {
                return Err(MergeError::VariableMismatch {
                    expected: v1.clone(),
                    found: v2.clone(),
                });
            }
            Ok(LocalTypeR::Var(v1.clone()))
        }

        // Send ⊔ Recv is an error
        (LocalTypeR::Send { .. }, LocalTypeR::Recv { .. })
        | (LocalTypeR::Recv { .. }, LocalTypeR::Send { .. }) => Err(MergeError::DirectionMismatch),

        // All other combinations are incompatible
        _ => Err(MergeError::IncompatibleTypes),
    }
}

/// Merge two sets of labeled branches.
///
/// For labels that appear in both sets, their continuations must be mergeable.
/// Labels that appear in only one set are included as-is.
fn merge_branches(
    branches1: &[(Label, LocalTypeR)],
    branches2: &[(Label, LocalTypeR)],
) -> Result<Vec<(Label, LocalTypeR)>, MergeError> {
    let mut result: HashMap<String, (Label, LocalTypeR)> = HashMap::new();

    // Add all branches from the first set
    for (label, cont) in branches1 {
        result.insert(label.name.clone(), (label.clone(), cont.clone()));
    }

    // Merge with branches from the second set
    for (label, cont) in branches2 {
        if let Some((existing_label, existing_cont)) = result.get(&label.name) {
            // Label exists - merge continuations
            let merged_cont =
                merge(existing_cont, cont).map_err(|_| MergeError::IncompatibleContinuations {
                    label: label.name.clone(),
                })?;
            // Use the label with matching sort (they should be the same)
            if existing_label.sort != label.sort {
                return Err(MergeError::IncompatibleContinuations {
                    label: label.name.clone(),
                });
            }
            result.insert(label.name.clone(), (label.clone(), merged_cont));
        } else {
            // New label - add it
            result.insert(label.name.clone(), (label.clone(), cont.clone()));
        }
    }

    // Convert back to vector, sorted by label name for determinism
    let mut branches: Vec<_> = result.into_values().collect();
    branches.sort_by(|a, b| a.0.name.cmp(&b.0.name));

    Ok(branches)
}

/// Merge multiple local types.
///
/// This is a convenience function for merging more than two types.
/// It folds the merge operation over the list.
///
/// Returns an error if the list is empty or if any pair cannot be merged.
pub fn merge_all(types: &[LocalTypeR]) -> MergeResult {
    match types {
        [] => Err(MergeError::IncompatibleTypes),
        [single] => Ok(single.clone()),
        [first, rest @ ..] => {
            let mut result = first.clone();
            for t in rest {
                result = merge(&result, t)?;
            }
            Ok(result)
        }
    }
}

/// Check if two local types are mergeable without actually merging them.
///
/// This is useful for validation without constructing the merged type.
pub fn can_merge(t1: &LocalTypeR, t2: &LocalTypeR) -> bool {
    merge(t1, t2).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merge_identical_end() {
        let result = merge(&LocalTypeR::End, &LocalTypeR::End).unwrap();
        assert_eq!(result, LocalTypeR::End);
    }

    #[test]
    fn test_merge_identical_send() {
        let t = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let result = merge(&t, &t).unwrap();
        assert_eq!(result, t);
    }

    #[test]
    fn test_merge_sends_different_labels() {
        // !B{yes.end} ⊔ !B{no.end} = !B{yes.end, no.end}
        let t1 = LocalTypeR::send("B", Label::new("yes"), LocalTypeR::End);
        let t2 = LocalTypeR::send("B", Label::new("no"), LocalTypeR::End);

        let result = merge(&t1, &t2).unwrap();

        match result {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 2);
                let labels: Vec<_> = branches.iter().map(|(l, _)| l.name.as_str()).collect();
                assert!(labels.contains(&"yes"));
                assert!(labels.contains(&"no"));
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_merge_sends_same_label_same_continuation() {
        // !B{msg.end} ⊔ !B{msg.end} = !B{msg.end}
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);

        let result = merge(&t1, &t2).unwrap();

        match result {
            LocalTypeR::Send { branches, .. } => {
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_merge_sends_different_partners_fails() {
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::send("C", Label::new("msg"), LocalTypeR::End);

        let result = merge(&t1, &t2);
        assert!(matches!(result, Err(MergeError::PartnerMismatch { .. })));
    }

    #[test]
    fn test_merge_send_recv_fails() {
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);

        let result = merge(&t1, &t2);
        assert!(matches!(result, Err(MergeError::DirectionMismatch)));
    }

    #[test]
    fn test_merge_recv_different_labels() {
        // ?A{yes.end} ⊔ ?A{no.end} = ?A{yes.end, no.end}
        let t1 = LocalTypeR::recv("A", Label::new("yes"), LocalTypeR::End);
        let t2 = LocalTypeR::recv("A", Label::new("no"), LocalTypeR::End);

        let result = merge(&t1, &t2).unwrap();

        match result {
            LocalTypeR::Recv { partner, branches } => {
                assert_eq!(partner, "A");
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Recv"),
        }
    }

    #[test]
    fn test_merge_recursive_types() {
        // μt.!B{msg.t} ⊔ μt.!B{msg.t} = μt.!B{msg.t}
        let t1 = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        let t2 = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );

        let result = merge(&t1, &t2).unwrap();
        assert_eq!(result, t1);
    }

    #[test]
    fn test_merge_recursive_different_vars_fails() {
        let t1 = LocalTypeR::mu("t", LocalTypeR::var("t"));
        let t2 = LocalTypeR::mu("s", LocalTypeR::var("s"));

        let result = merge(&t1, &t2);
        assert!(matches!(
            result,
            Err(MergeError::RecursiveVariableMismatch { .. })
        ));
    }

    #[test]
    fn test_merge_variables() {
        let t1 = LocalTypeR::var("t");
        let t2 = LocalTypeR::var("t");

        let result = merge(&t1, &t2).unwrap();
        assert_eq!(result, LocalTypeR::var("t"));
    }

    #[test]
    fn test_merge_variables_different_fails() {
        let t1 = LocalTypeR::var("t");
        let t2 = LocalTypeR::var("s");

        let result = merge(&t1, &t2);
        assert!(matches!(result, Err(MergeError::VariableMismatch { .. })));
    }

    #[test]
    fn test_merge_all() {
        let types = vec![
            LocalTypeR::send("B", Label::new("a"), LocalTypeR::End),
            LocalTypeR::send("B", Label::new("b"), LocalTypeR::End),
            LocalTypeR::send("B", Label::new("c"), LocalTypeR::End),
        ];

        let result = merge_all(&types).unwrap();

        match result {
            LocalTypeR::Send { branches, .. } => {
                assert_eq!(branches.len(), 3);
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_merge_all_empty_fails() {
        let result = merge_all(&[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_can_merge() {
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::send("B", Label::new("other"), LocalTypeR::End);
        let t3 = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);

        assert!(can_merge(&t1, &t2));
        assert!(!can_merge(&t1, &t3));
    }

    #[test]
    fn test_merge_nested_sends() {
        // !B{a.!C{x.end}} ⊔ !B{b.!C{y.end}}
        // = !B{a.!C{x.end}, b.!C{y.end}}
        let t1 = LocalTypeR::send(
            "B",
            Label::new("a"),
            LocalTypeR::send("C", Label::new("x"), LocalTypeR::End),
        );
        let t2 = LocalTypeR::send(
            "B",
            Label::new("b"),
            LocalTypeR::send("C", Label::new("y"), LocalTypeR::End),
        );

        let result = merge(&t1, &t2).unwrap();

        match result {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 2);
                // Check nested structure preserved
                for (_, cont) in &branches {
                    assert!(matches!(cont, LocalTypeR::Send { partner, .. } if partner == "C"));
                }
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_merge_same_label_incompatible_continuation() {
        // !B{msg.!C{x.end}} ⊔ !B{msg.?C{y.end}} should fail
        // because msg has incompatible continuations (send vs recv)
        let t1 = LocalTypeR::send(
            "B",
            Label::new("msg"),
            LocalTypeR::send("C", Label::new("x"), LocalTypeR::End),
        );
        let t2 = LocalTypeR::send(
            "B",
            Label::new("msg"),
            LocalTypeR::recv("C", Label::new("y"), LocalTypeR::End),
        );

        let result = merge(&t1, &t2);
        assert!(matches!(
            result,
            Err(MergeError::IncompatibleContinuations { .. })
        ));
    }
}
