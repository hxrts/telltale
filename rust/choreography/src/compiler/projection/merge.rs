use super::*;
use proc_macro2::Ident;

#[path = "merge_eq.rs"]
mod merge_eq;

/// A LocalType paired with its choice label.
///
/// Used during merging to preserve semantic choice labels when creating Branch nodes.
pub(super) struct LabeledLocalType {
    pub(super) label: Ident,
    pub(super) local_type: LocalType,
}

/// Merge two labeled LocalTypes, preserving choice labels.
///
/// When merging Receive operations with different messages, this uses the choice labels
/// instead of message type names for the resulting Branch node.
pub(super) fn merge_labeled_local_types(
    t1: &LabeledLocalType,
    t2: &LabeledLocalType,
) -> Result<LabeledLocalType, ProjectionError> {
    // Fast path: identical types (label doesn't matter if types are identical)
    if t1.local_type == t2.local_type {
        return Ok(LabeledLocalType {
            label: t1.label.clone(),
            local_type: t1.local_type.clone(),
        });
    }

    match (&t1.local_type, &t2.local_type) {
        // End merges with End
        (LocalType::End, LocalType::End) => Ok(LabeledLocalType {
            label: t1.label.clone(),
            local_type: LocalType::End,
        }),

        // End can merge with any type (End is neutral)
        (LocalType::End, other) => Ok(LabeledLocalType {
            label: t2.label.clone(),
            local_type: other.clone(),
        }),
        (other, LocalType::End) => Ok(LabeledLocalType {
            label: t1.label.clone(),
            local_type: other.clone(),
        }),

        // Send with same target - must have same message
        (
            LocalType::Send {
                to: to1,
                message: msg1,
                continuation: cont1,
            },
            LocalType::Send {
                to: to2,
                message: msg2,
                continuation: cont2,
            },
        ) if to1 == to2 => {
            if msg1.name == msg2.name {
                // Same message - merge continuations
                let merged_cont = merge_local_types(cont1, cont2)?;
                Ok(LabeledLocalType {
                    label: t1.label.clone(), // Label doesn't matter for Send
                    local_type: LocalType::Send {
                        to: to1.clone(),
                        message: msg1.clone(),
                        continuation: Box::new(merged_cont),
                    },
                })
            } else {
                // Different messages - error for sends
                Err(ProjectionError::MergeFailure(format!(
                    "cannot merge sends with different messages: '{}' vs '{}'",
                    msg1.name, msg2.name
                )))
            }
        }

        // Receive with same source - merge into Branch using CHOICE LABELS
        (
            LocalType::Receive {
                from: from1,
                message: msg1,
                continuation: cont1,
            },
            LocalType::Receive {
                from: from2,
                message: msg2,
                continuation: cont2,
            },
        ) if from1 == from2 => {
            if msg1.name == msg2.name {
                // Same message - merge continuations
                let merged_cont = merge_local_types(cont1, cont2)?;
                Ok(LabeledLocalType {
                    label: t1.label.clone(),
                    local_type: LocalType::Receive {
                        from: from1.clone(),
                        message: msg1.clone(),
                        continuation: Box::new(merged_cont),
                    },
                })
            } else {
                // Different messages - create a Branch with CHOICE LABELS (not message names!)
                let mut branches = vec![
                    (t1.label.clone(), *cont1.clone()), // Use choice label
                    (t2.label.clone(), *cont2.clone()), // Use choice label
                ];
                sort_branches_by_label(&mut branches);
                Ok(LabeledLocalType {
                    label: t1.label.clone(), // Arbitrary choice; branch contains both
                    local_type: LocalType::Branch {
                        from: from1.clone(),
                        branches,
                    },
                })
            }
        }

        // Merge Receive into existing Branch from same source
        (
            LocalType::Branch {
                from: from1,
                branches: br1,
            },
            LocalType::Receive {
                from: from2,
                message: _msg2,
                continuation: cont2,
            },
        ) if from1 == from2 => {
            let mut new_branches = br1.clone();
            // Check if label already exists
            if let Some((_, existing_cont)) = new_branches.iter_mut().find(|(l, _)| l == &t2.label)
            {
                *existing_cont = merge_local_types(existing_cont, cont2)?;
            } else {
                new_branches.push((t2.label.clone(), *cont2.clone())); // Use choice label
            }
            sort_branches_by_label(&mut new_branches);
            Ok(LabeledLocalType {
                label: t1.label.clone(),
                local_type: LocalType::Branch {
                    from: from1.clone(),
                    branches: new_branches,
                },
            })
        }

        // Symmetric case: Receive into Branch
        (
            LocalType::Receive {
                from: from1,
                message: _msg1,
                continuation: cont1,
            },
            LocalType::Branch {
                from: from2,
                branches: br2,
            },
        ) if from1 == from2 => {
            let mut new_branches = br2.clone();
            // Check if label already exists
            if let Some((_, existing_cont)) = new_branches.iter_mut().find(|(l, _)| l == &t1.label)
            {
                *existing_cont = merge_local_types(existing_cont, cont1)?;
            } else {
                new_branches.push((t1.label.clone(), *cont1.clone())); // Use choice label
            }
            sort_branches_by_label(&mut new_branches);
            Ok(LabeledLocalType {
                label: t2.label.clone(),
                local_type: LocalType::Branch {
                    from: from2.clone(),
                    branches: new_branches,
                },
            })
        }

        // Merge Branch with Branch from same source
        (
            LocalType::Branch {
                from: from1,
                branches: br1,
            },
            LocalType::Branch {
                from: from2,
                branches: br2,
            },
        ) if from1 == from2 => {
            let merged_branches = merge_branch_branches(br1, br2)?;
            Ok(LabeledLocalType {
                label: t1.label.clone(),
                local_type: LocalType::Branch {
                    from: from1.clone(),
                    branches: merged_branches,
                },
            })
        }

        // All other cases: fall back to unlabeled merge
        _ => {
            let merged = merge_local_types(&t1.local_type, &t2.local_type)?;
            Ok(LabeledLocalType {
                label: t1.label.clone(),
                local_type: merged,
            })
        }
    }
}

/// Merge two LocalTypes for projection.
///
/// This is a simplified merge operation for the extended LocalType.
/// For the full merge algorithm, see the `merge` module which works with `LocalTypeR`.
#[allow(clippy::too_many_lines)]
// RECURSION_SAFE: structural recursion over finite local-type pairs.
pub fn merge_local_types(t1: &LocalType, t2: &LocalType) -> Result<LocalType, ProjectionError> {
    // Fast path: identical types
    if t1 == t2 {
        return Ok(t1.clone());
    }

    match (t1, t2) {
        // End merges with End
        (LocalType::End, LocalType::End) => Ok(LocalType::End),

        // End can merge with any type (End is neutral)
        // This is lenient - strict mode would reject this
        (LocalType::End, other) | (other, LocalType::End) => Ok(other.clone()),

        // Send with same target - must have same message (Lean: mergeSendSorted)
        // A non-participant cannot choose which message to send based on a choice
        // they didn't observe. Different messages cause merge to fail.
        (
            LocalType::Send {
                to: to1,
                message: msg1,
                continuation: cont1,
            },
            LocalType::Send {
                to: to2,
                message: msg2,
                continuation: cont2,
            },
        ) if to1 == to2 => {
            if msg1.name == msg2.name {
                // Same message - merge continuations
                let merged_cont = merge_local_types(cont1, cont2)?;
                Ok(LocalType::Send {
                    to: to1.clone(),
                    message: msg1.clone(),
                    continuation: Box::new(merged_cont),
                })
            } else {
                // Different messages - this is an error for sends
                // Non-participant cannot choose based on unseen choice
                Err(ProjectionError::MergeFailure(format!(
                    "cannot merge sends with different messages: '{}' vs '{}'",
                    msg1.name, msg2.name
                )))
            }
        }

        // Receive with same source - merge into Branch if messages differ
        (
            LocalType::Receive {
                from: from1,
                message: msg1,
                continuation: cont1,
            },
            LocalType::Receive {
                from: from2,
                message: msg2,
                continuation: cont2,
            },
        ) if from1 == from2 => {
            if msg1.name == msg2.name {
                // Same message - merge continuations
                let merged_cont = merge_local_types(cont1, cont2)?;
                Ok(LocalType::Receive {
                    from: from1.clone(),
                    message: msg1.clone(),
                    continuation: Box::new(merged_cont),
                })
            } else {
                // Different messages - ERROR!
                // This function has no label information. If we're merging receives with
                // different messages from a choice, use merge_labeled_local_types instead.
                Err(ProjectionError::MergeFailure(format!(
                    "cannot merge receives with different messages without choice labels: '{}' vs '{}'. \
                     This likely indicates a protocol structure error or requires label-aware merging.",
                    msg1.name, msg2.name
                )))
            }
        }

        // Merge Receive into existing Branch from same source
        (
            LocalType::Branch { from: from1, .. },
            LocalType::Receive {
                from: from2,
                message: msg2,
                ..
            },
        ) if from1 == from2 => {
            // ERROR: Cannot merge Receive into Branch without label information
            // If the Branch has semantic labels, we don't know which branch this Receive belongs to
            Err(ProjectionError::MergeFailure(format!(
                "cannot merge receive of '{}' into branch without label information. \
                 Use merge_labeled_local_types for choice continuations.",
                msg2.name
            )))
        }

        // Merge Branch with Branch from same source (recv semantics - union labels)
        (
            LocalType::Branch {
                from: from1,
                branches: br1,
            },
            LocalType::Branch {
                from: from2,
                branches: br2,
            },
        ) if from1 == from2 => {
            let merged_branches = merge_branch_branches(br1, br2)?;
            Ok(LocalType::Branch {
                from: from1.clone(),
                branches: merged_branches,
            })
        }

        // Symmetric case: Receive into Branch
        (
            LocalType::Receive {
                from: from1,
                message: msg1,
                ..
            },
            LocalType::Branch { from: from2, .. },
        ) if from1 == from2 => {
            // ERROR: Cannot merge Receive into Branch without label information
            Err(ProjectionError::MergeFailure(format!(
                "cannot merge receive of '{}' into branch without label information. \
                 Use merge_labeled_local_types for choice continuations.",
                msg1.name
            )))
        }

        // Select with same target - must have identical label sets (send semantics)
        // A non-participant cannot choose which option to select based on an unseen choice
        (
            LocalType::Select {
                to: to1,
                branches: br1,
            },
            LocalType::Select {
                to: to2,
                branches: br2,
            },
        ) if to1 == to2 => {
            let merged_branches = merge_select_branches(br1, br2)?;
            Ok(LocalType::Select {
                to: to1.clone(),
                branches: merged_branches,
            })
        }

        // Rec with same label
        (
            LocalType::Rec {
                label: l1,
                body: b1,
            },
            LocalType::Rec {
                label: l2,
                body: b2,
            },
        ) if l1 == l2 => {
            let merged_body = merge_local_types(b1, b2)?;
            Ok(LocalType::Rec {
                label: l1.clone(),
                body: Box::new(merged_body),
            })
        }

        // Var with same label
        (LocalType::Var(v1), LocalType::Var(v2)) if v1 == v2 => Ok(LocalType::Var(v1.clone())),

        // Loop with same condition
        (
            LocalType::Loop {
                condition: c1,
                body: b1,
            },
            LocalType::Loop {
                condition: c2,
                body: b2,
            },
        ) if conditions_equal(c1, c2) => {
            let merged_body = merge_local_types(b1, b2)?;
            Ok(LocalType::Loop {
                condition: c1.clone(),
                body: Box::new(merged_body),
            })
        }

        // All other combinations are incompatible
        _ => Err(ProjectionError::MergeFailure(
            "incompatible local types in merge".to_string(),
        )),
    }
}

/// Merge two sets of labeled branches for Select types (send semantics).
///
/// Select merge requires IDENTICAL label sets. This matches Lean's `mergeSendSorted`
/// semantics: a non-participant cannot choose which option to select based on
/// an unseen choice.
fn merge_select_branches(
    branches1: &[(proc_macro2::Ident, LocalType)],
    branches2: &[(proc_macro2::Ident, LocalType)],
) -> Result<Vec<(proc_macro2::Ident, LocalType)>, ProjectionError> {
    // Sort both branch lists for comparison
    let mut sorted1: Vec<_> = branches1.to_vec();
    let mut sorted2: Vec<_> = branches2.to_vec();
    sorted1.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));
    sorted2.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));

    // Must have same number of branches
    if sorted1.len() != sorted2.len() {
        return Err(ProjectionError::MergeFailure(format!(
            "select branch count mismatch: {} vs {}",
            sorted1.len(),
            sorted2.len()
        )));
    }

    // Each branch must have the same label, merge continuations
    let mut result = Vec::with_capacity(sorted1.len());
    for ((label1, cont1), (label2, cont2)) in sorted1.iter().zip(sorted2.iter()) {
        if label1 != label2 {
            return Err(ProjectionError::MergeFailure(format!(
                "select branch label mismatch: '{}' vs '{}'",
                label1, label2
            )));
        }
        let merged_cont = merge_local_types(cont1, cont2)?;
        result.push((label1.clone(), merged_cont));
    }

    Ok(result)
}

/// Merge two sets of labeled branches for Branch types (recv semantics).
///
/// Branch merge UNIONS label sets. This matches Lean's `mergeRecvSorted`
/// semantics: a non-participant can receive any label regardless of which
/// branch was taken.
fn merge_branch_branches(
    branches1: &[(proc_macro2::Ident, LocalType)],
    branches2: &[(proc_macro2::Ident, LocalType)],
) -> Result<Vec<(proc_macro2::Ident, LocalType)>, ProjectionError> {
    use std::collections::HashMap;

    let mut result: HashMap<String, (proc_macro2::Ident, LocalType)> = HashMap::new();

    // Add all branches from the first set
    for (label, cont) in branches1 {
        result.insert(label.to_string(), (label.clone(), cont.clone()));
    }

    // Merge with branches from the second set
    for (label, cont) in branches2 {
        let label_str = label.to_string();
        if let Some((_, existing_cont)) = result.get(&label_str) {
            // Label exists - merge continuations
            let merged_cont = merge_local_types(existing_cont, cont)?;
            result.insert(label_str, (label.clone(), merged_cont));
        } else {
            // New label - add it
            result.insert(label_str, (label.clone(), cont.clone()));
        }
    }

    // Convert back to vector, sorted by label name for determinism
    let mut branches: Vec<_> = result.into_values().collect();
    branches.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));

    Ok(branches)
}

fn sort_branches_by_label(branches: &mut [(proc_macro2::Ident, LocalType)]) {
    branches.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));
}

/// Compare two optional conditions for equality.
///
/// Since `Condition::Custom` contains `TokenStream` which doesn't implement
/// `PartialEq`, we compare Custom conditions conservatively (always different).
fn conditions_equal(
    c1: &Option<crate::ast::protocol::Condition>,
    c2: &Option<crate::ast::protocol::Condition>,
) -> bool {
    use crate::ast::protocol::Condition;

    match (c1, c2) {
        (None, None) => true,
        (Some(Condition::Count(n1)), Some(Condition::Count(n2))) => n1 == n2,
        (Some(Condition::RoleDecides(r1)), Some(Condition::RoleDecides(r2))) => r1 == r2,
        // Custom conditions are incomparable (TokenStream doesn't impl PartialEq)
        (Some(Condition::Custom(_)), Some(Condition::Custom(_))) => false,
        _ => false,
    }
}

// Helper to compare LocalTypes for equality
