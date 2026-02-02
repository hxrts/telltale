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
//! 2. `!q{lᵢ.Tᵢ} ⊔ !q{l'ⱼ.T'ⱼ}` requires **identical** label sets (fails if different)
//! 3. `?p{lᵢ.Tᵢ} ⊔ ?p{l'ⱼ.T'ⱼ} = ?p{(lᵢ.Tᵢ) ∪ (l'ⱼ.T'ⱼ)}` unions labels
//! 4. `μt.T ⊔ μt.T' = μt.(T ⊔ T')` if T and T' use the same variable
//! 5. `t ⊔ t = t` for type variables
//!
//! # Lean Correspondence
//!
//! This implementation corresponds to `lean/Telltale/Protocol/ProjectionR.lean`:
//! - `merge_send_branches` ↔ Lean's `LocalTypeR.mergeSendSorted`
//! - `merge_recv_branches` ↔ Lean's `LocalTypeR.mergeRecvSorted`
//!
//! The key difference between send and recv merge:
//! - **Send merge**: Requires identical label sets. A non-participant cannot choose
//!   different outgoing messages based on a choice it didn't observe.
//! - **Recv merge**: Unions label sets. A non-participant can handle any incoming
//!   message regardless of which branch was taken.

use crate::{Label, LocalTypeR};
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

    /// Send branches have different label sets (not allowed for internal choice)
    #[error("send branch label mismatch: cannot merge sends with different labels '{left}' vs '{right}'")]
    SendLabelMismatch { left: String, right: String },

    /// Send branches have different number of labels
    #[error("send branch count mismatch: {left} labels vs {right} labels")]
    SendBranchCountMismatch { left: usize, right: usize },

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
/// ```
/// use telltale_types::{merge, can_merge, LocalTypeR, Label};
///
/// // Merging identical send types succeeds
/// let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let t2 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let merged = merge(&t1, &t2).unwrap();
/// assert_eq!(merged, t1);
///
/// // Merging sends with DIFFERENT labels FAILS (Lean correspondence)
/// // A non-participant cannot choose different sends based on unseen choice
/// let s1 = LocalTypeR::send("B", Label::new("yes"), LocalTypeR::End);
/// let s2 = LocalTypeR::send("B", Label::new("no"), LocalTypeR::End);
/// assert!(!can_merge(&s1, &s2));
///
/// // Merging recvs with different labels SUCCEEDS (unions labels)
/// let r1 = LocalTypeR::recv("A", Label::new("yes"), LocalTypeR::End);
/// let r2 = LocalTypeR::recv("A", Label::new("no"), LocalTypeR::End);
/// let merged = merge(&r1, &r2).unwrap();
/// // merged = ?A{yes.end, no.end}
/// ```
pub fn merge(t1: &LocalTypeR, t2: &LocalTypeR) -> MergeResult {
    // Fast path: identical types
    if t1 == t2 {
        return Ok(t1.clone());
    }

    match (t1, t2) {
        // Rule 1: end ⊔ end = end
        (LocalTypeR::End, LocalTypeR::End) => Ok(LocalTypeR::End),

        // End with non-End is an error
        (LocalTypeR::End, other) | (other, LocalTypeR::End) => {
            Err(MergeError::EndMismatch(other.clone()))
        }

        // Rule 2: !q{branches₁} ⊔ !q{branches₂} requires IDENTICAL label sets
        // This matches Lean's `mergeSendSorted` - a non-participant cannot choose
        // different outgoing messages based on a choice it didn't observe.
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
            let merged_branches = merge_send_branches(b1, b2)?;
            Ok(LocalTypeR::Send {
                partner: p1.clone(),
                branches: merged_branches,
            })
        }

        // Rule 3: ?p{branches₁} ⊔ ?p{branches₂} = ?p{branches₁ ∪ branches₂} unions labels
        // This matches Lean's `mergeRecvSorted` - a non-participant can handle
        // any incoming message regardless of which branch was taken.
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
            let merged_branches = merge_recv_branches(b1, b2)?;
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

/// Merge two sets of send branches (internal choice).
///
/// **Requires identical label sets.** This matches Lean's `mergeSendSorted`.
///
/// A non-participant role cannot choose different outgoing messages based on
/// a choice it didn't observe. If the two branch sets have different labels,
/// merge fails because the role would need to "know" which branch was taken.
///
/// # Example
///
/// - `!B{x.end} ⊔ !B{x.end}` = `!B{x.end}` ✓ (same labels)
/// - `!B{x.end} ⊔ !B{y.end}` = ERROR (different labels)
fn merge_send_branches(
    branches1: &[(Label, Option<crate::ValType>, LocalTypeR)],
    branches2: &[(Label, Option<crate::ValType>, LocalTypeR)],
) -> Result<Vec<(Label, Option<crate::ValType>, LocalTypeR)>, MergeError> {
    // Sort both branch lists for comparison
    let mut sorted1: Vec<_> = branches1.to_vec();
    let mut sorted2: Vec<_> = branches2.to_vec();
    sorted1.sort_by(|a, b| a.0.name.cmp(&b.0.name));
    sorted2.sort_by(|a, b| a.0.name.cmp(&b.0.name));

    // Must have same number of branches
    if sorted1.len() != sorted2.len() {
        return Err(MergeError::SendBranchCountMismatch {
            left: sorted1.len(),
            right: sorted2.len(),
        });
    }

    // Each branch must have the same label, merge continuations
    let mut result = Vec::with_capacity(sorted1.len());
    for ((label1, vt1, cont1), (label2, _vt2, cont2)) in sorted1.iter().zip(sorted2.iter()) {
        // Labels must match exactly (name and sort)
        if label1.name != label2.name {
            return Err(MergeError::SendLabelMismatch {
                left: label1.name.clone(),
                right: label2.name.clone(),
            });
        }
        if label1.sort != label2.sort {
            return Err(MergeError::IncompatibleContinuations {
                label: label1.name.clone(),
            });
        }

        // Merge continuations
        let merged_cont =
            merge(cont1, cont2).map_err(|_| MergeError::IncompatibleContinuations {
                label: label1.name.clone(),
            })?;

        result.push((label1.clone(), vt1.clone(), merged_cont));
    }

    Ok(result)
}

/// Merge two sets of recv branches (external choice).
///
/// **Unions label sets.** This matches Lean's `mergeRecvSorted`.
///
/// A non-participant role can handle any incoming message regardless of which
/// branch was taken. Labels that appear in both sets have their continuations
/// merged; labels that appear in only one set are included as-is.
///
/// # Example
///
/// - `?A{x.end} ⊔ ?A{y.end}` = `?A{x.end, y.end}` ✓ (union of labels)
/// - `?A{x.T1} ⊔ ?A{x.T2}` = `?A{x.(T1 ⊔ T2)}` ✓ (same label, merge continuations)
fn merge_recv_branches(
    branches1: &[(Label, Option<crate::ValType>, LocalTypeR)],
    branches2: &[(Label, Option<crate::ValType>, LocalTypeR)],
) -> Result<Vec<(Label, Option<crate::ValType>, LocalTypeR)>, MergeError> {
    let mut result: HashMap<String, (Label, Option<crate::ValType>, LocalTypeR)> = HashMap::new();

    // Add all branches from the first set
    for (label, vt, cont) in branches1 {
        result.insert(label.name.clone(), (label.clone(), vt.clone(), cont.clone()));
    }

    // Union with branches from the second set
    for (label, vt, cont) in branches2 {
        if let Some((existing_label, _existing_vt, existing_cont)) = result.get(&label.name) {
            // Label exists in both - merge continuations
            let merged_cont =
                merge(existing_cont, cont).map_err(|_| MergeError::IncompatibleContinuations {
                    label: label.name.clone(),
                })?;
            // Labels must have matching sort
            if existing_label.sort != label.sort {
                return Err(MergeError::IncompatibleContinuations {
                    label: label.name.clone(),
                });
            }
            result.insert(label.name.clone(), (label.clone(), vt.clone(), merged_cont));
        } else {
            // New label - add it (this is the key difference from send merge)
            result.insert(label.name.clone(), (label.clone(), vt.clone(), cont.clone()));
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
    use assert_matches::assert_matches;

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

    // =========================================================================
    // Send merge tests - requires IDENTICAL label sets (Lean correspondence)
    // =========================================================================

    #[test]
    fn test_merge_sends_same_labels_succeeds() {
        // !B{x.end} ⊔ !B{x.end} = !B{x.end}
        let t1 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);
        let t2 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);

        let result = merge(&t1, &t2).unwrap();
        assert_matches!(result, LocalTypeR::Send { partner, branches } => {
            assert_eq!(partner, "B");
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, "x");
        });
    }

    #[test]
    fn test_merge_sends_different_labels_fails() {
        // !B{x.end} ⊔ !B{y.end} = ERROR (different labels)
        // This matches Lean's mergeSendSorted behavior
        let t1 = LocalTypeR::send("B", Label::new("yes"), LocalTypeR::End);
        let t2 = LocalTypeR::send("B", Label::new("no"), LocalTypeR::End);

        let result = merge(&t1, &t2);
        assert!(
            matches!(result, Err(MergeError::SendLabelMismatch { .. })),
            "Expected SendLabelMismatch, got {:?}",
            result
        );
    }

    #[test]
    fn test_merge_sends_different_count_fails() {
        // !B{x.end, y.end} ⊔ !B{x.end} = ERROR (different count)
        let t1 = LocalTypeR::Send {
            partner: "B".to_string(),
            branches: vec![
                (Label::new("x"), None, LocalTypeR::End),
                (Label::new("y"), None, LocalTypeR::End),
            ],
        };
        let t2 = LocalTypeR::send("B", Label::new("x"), LocalTypeR::End);

        let result = merge(&t1, &t2);
        assert!(
            matches!(result, Err(MergeError::SendBranchCountMismatch { .. })),
            "Expected SendBranchCountMismatch, got {:?}",
            result
        );
    }

    #[test]
    fn test_merge_sends_different_partners_fails() {
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::send("C", Label::new("msg"), LocalTypeR::End);

        let result = merge(&t1, &t2);
        assert!(matches!(result, Err(MergeError::PartnerMismatch { .. })));
    }

    // =========================================================================
    // Recv merge tests - UNIONS label sets (Lean correspondence)
    // =========================================================================

    #[test]
    fn test_merge_recvs_different_labels_succeeds() {
        // ?A{x.end} ⊔ ?A{y.end} = ?A{x.end, y.end}
        // This matches Lean's mergeRecvSorted behavior
        let t1 = LocalTypeR::recv("A", Label::new("x"), LocalTypeR::End);
        let t2 = LocalTypeR::recv("A", Label::new("y"), LocalTypeR::End);

        let result = merge(&t1, &t2).unwrap();
        assert_matches!(result, LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "A");
            assert_eq!(branches.len(), 2);
            let labels: Vec<_> = branches.iter().map(|(l, _, _)| l.name.as_str()).collect();
            assert!(labels.contains(&"x"));
            assert!(labels.contains(&"y"));
        });
    }

    #[test]
    fn test_merge_recvs_same_label_merges_continuations() {
        // ?A{x.T1} ⊔ ?A{x.T2} = ?A{x.(T1 ⊔ T2)}
        let t1 = LocalTypeR::recv(
            "A",
            Label::new("x"),
            LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
        );
        let t2 = LocalTypeR::recv(
            "A",
            Label::new("x"),
            LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
        );

        let result = merge(&t1, &t2).unwrap();
        assert_matches!(result, LocalTypeR::Recv { branches, .. } => {
            assert_eq!(branches.len(), 1);
            // Continuation should be merged (same as input since identical)
            assert_matches!(&branches[0].2, LocalTypeR::Send { partner, .. } => {
                assert_eq!(partner, "B");
            });
        });
    }

    #[test]
    fn test_merge_recvs_overlapping_labels() {
        // ?A{x.end, y.end} ⊔ ?A{y.end, z.end} = ?A{x.end, y.end, z.end}
        let t1 = LocalTypeR::Recv {
            partner: "A".to_string(),
            branches: vec![
                (Label::new("x"), None, LocalTypeR::End),
                (Label::new("y"), None, LocalTypeR::End),
            ],
        };
        let t2 = LocalTypeR::Recv {
            partner: "A".to_string(),
            branches: vec![
                (Label::new("y"), None, LocalTypeR::End),
                (Label::new("z"), None, LocalTypeR::End),
            ],
        };

        let result = merge(&t1, &t2).unwrap();
        assert_matches!(result, LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "A");
            assert_eq!(branches.len(), 3);
            let labels: Vec<_> = branches.iter().map(|(l, _, _)| l.name.as_str()).collect();
            assert!(labels.contains(&"x"));
            assert!(labels.contains(&"y"));
            assert!(labels.contains(&"z"));
        });
    }

    // =========================================================================
    // Direction mismatch tests
    // =========================================================================

    #[test]
    fn test_merge_send_recv_fails() {
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);

        let result = merge(&t1, &t2);
        assert!(matches!(result, Err(MergeError::DirectionMismatch)));
    }

    // =========================================================================
    // merge_all tests
    // =========================================================================

    #[test]
    fn test_merge_all_sends_same_labels() {
        // All sends with same labels should succeed
        let types = vec![
            LocalTypeR::send("B", Label::new("x"), LocalTypeR::End),
            LocalTypeR::send("B", Label::new("x"), LocalTypeR::End),
            LocalTypeR::send("B", Label::new("x"), LocalTypeR::End),
        ];

        let result = merge_all(&types).unwrap();
        assert_matches!(result, LocalTypeR::Send { branches, .. } => {
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, "x");
        });
    }

    #[test]
    fn test_merge_all_sends_different_labels_fails() {
        // Sends with different labels should fail
        let types = vec![
            LocalTypeR::send("B", Label::new("a"), LocalTypeR::End),
            LocalTypeR::send("B", Label::new("b"), LocalTypeR::End),
        ];

        let result = merge_all(&types);
        assert!(result.is_err());
    }

    #[test]
    fn test_merge_all_recvs_different_labels() {
        // Recvs with different labels should union
        let types = vec![
            LocalTypeR::recv("A", Label::new("a"), LocalTypeR::End),
            LocalTypeR::recv("A", Label::new("b"), LocalTypeR::End),
            LocalTypeR::recv("A", Label::new("c"), LocalTypeR::End),
        ];

        let result = merge_all(&types).unwrap();
        assert_matches!(result, LocalTypeR::Recv { branches, .. } => {
            assert_eq!(branches.len(), 3);
        });
    }

    // =========================================================================
    // can_merge tests
    // =========================================================================

    #[test]
    fn test_can_merge_sends_same_label() {
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        assert!(can_merge(&t1, &t2));
    }

    #[test]
    fn test_can_merge_sends_different_labels_false() {
        // Different labels for sends should NOT be mergeable
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::send("B", Label::new("other"), LocalTypeR::End);
        assert!(!can_merge(&t1, &t2));
    }

    #[test]
    fn test_can_merge_recvs_different_labels_true() {
        // Different labels for recvs SHOULD be mergeable
        let t1 = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::recv("A", Label::new("other"), LocalTypeR::End);
        assert!(can_merge(&t1, &t2));
    }

    #[test]
    fn test_can_merge_send_recv_false() {
        let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let t2 = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);
        assert!(!can_merge(&t1, &t2));
    }
}
