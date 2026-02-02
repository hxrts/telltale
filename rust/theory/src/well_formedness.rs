//! Well-Formedness Validation for Session Types
//!
//! This module provides validation predicates for global and local types.
//! Well-formedness ensures that types are syntactically valid and can be
//! used for protocol verification.
//!
//! # Well-Formedness Criteria
//!
//! ## Global Types
//! - All recursion variables are bound
//! - Each communication has at least one branch
//! - Sender and receiver are different in each communication
//! - Types are guarded (no immediate recursion)
//! - Label names are unique within each branch set
//!
//! ## Local Types
//! - All recursion variables are bound
//! - Each choice has at least one branch
//! - Types are guarded
//! - Label names are unique within each branch set
//!
//! # Lean Correspondence
//!
//! - `unique_labels` ↔ Lean's `uniqLabels` inductive
//! - `branches_unique` ↔ Lean's `BranchesUniq`

use telltale_types::{GlobalType, Label, LocalTypeR};
use thiserror::Error;

/// Errors during well-formedness validation
#[derive(Debug, Clone, Error)]
pub enum ValidationError {
    /// Unbound type variable
    #[error("unbound type variable '{0}'")]
    UnboundVariable(String),

    /// Empty branches in communication/choice
    #[error("empty branches not allowed")]
    EmptyBranches,

    /// Self-communication detected
    #[error("self-communication: role '{0}' cannot send to itself")]
    SelfCommunication(String),

    /// Unguarded recursion
    #[error("unguarded recursion: μ-binder must be followed by communication")]
    UnguardedRecursion,

    /// Duplicate label names in branches
    #[error("duplicate label name '{0}' in branches")]
    DuplicateLabel(String),

    /// Multiple errors
    #[error("multiple validation errors: {}", .0.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", "))]
    Multiple(Vec<ValidationError>),
}

/// Result of validation
pub type ValidationResult = Result<(), ValidationError>;

/// Validate a global type for well-formedness.
///
/// Checks all well-formedness criteria and returns the first error found,
/// or Ok(()) if the type is well-formed.
///
/// # Examples
///
/// ```
/// use telltale_theory::validate_global;
/// use telltale_types::{GlobalType, Label};
///
/// // Well-formed protocol
/// let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
/// assert!(validate_global(&g).is_ok());
///
/// // Self-communication is not allowed
/// let bad = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
/// assert!(validate_global(&bad).is_err());
/// ```
pub fn validate_global(g: &GlobalType) -> ValidationResult {
    let mut errors = Vec::new();

    if !g.all_vars_bound() {
        // Find unbound variables
        for var in g.free_vars() {
            errors.push(ValidationError::UnboundVariable(var));
        }
    }

    if !g.all_comms_non_empty() {
        errors.push(ValidationError::EmptyBranches);
    }

    if !g.no_self_comm() {
        if let Some(role) = find_self_comm(g) {
            errors.push(ValidationError::SelfCommunication(role));
        }
    }

    if !g.is_guarded() {
        errors.push(ValidationError::UnguardedRecursion);
    }

    if !unique_labels(g) {
        if let Some(label) = find_duplicate_label(g) {
            errors.push(ValidationError::DuplicateLabel(label));
        }
    }

    match errors.len() {
        0 => Ok(()),
        1 => Err(errors.pop().unwrap()),
        _ => Err(ValidationError::Multiple(errors)),
    }
}

fn find_self_comm(g: &GlobalType) -> Option<String> {
    match g {
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            if sender == receiver {
                Some(sender.clone())
            } else {
                branches.iter().find_map(|(_, cont)| find_self_comm(cont))
            }
        }
        GlobalType::Mu { body, .. } => find_self_comm(body),
        _ => None,
    }
}

/// Check if all branch labels are unique within each choice.
///
/// This corresponds to Lean's `uniqLabels` inductive predicate.
/// For each communication/choice, all branch labels must have distinct names.
///
/// # Examples
///
/// ```
/// use telltale_theory::unique_labels;
/// use telltale_types::{GlobalType, Label};
///
/// // Unique labels
/// let g = GlobalType::comm("A", "B", vec![
///     (Label::new("accept"), GlobalType::End),
///     (Label::new("reject"), GlobalType::End),
/// ]);
/// assert!(unique_labels(&g));
///
/// // Duplicate labels
/// let bad = GlobalType::comm("A", "B", vec![
///     (Label::new("msg"), GlobalType::End),
///     (Label::new("msg"), GlobalType::End),
/// ]);
/// assert!(!unique_labels(&bad));
/// ```
#[must_use]
pub fn unique_labels(g: &GlobalType) -> bool {
    match g {
        GlobalType::End => true,
        GlobalType::Var(_) => true,
        GlobalType::Comm { branches, .. } => {
            // Check that this branch set has unique label names
            if !branches_unique(branches) {
                return false;
            }
            // Recursively check all continuations
            branches.iter().all(|(_, cont)| unique_labels(cont))
        }
        GlobalType::Mu { body, .. } => unique_labels(body),
    }
}

/// Helper: check if all labels in a branch list have unique names.
///
/// Corresponds to Lean's `BranchesUniq`.
fn branches_unique(branches: &[(Label, GlobalType)]) -> bool {
    let mut seen = std::collections::HashSet::new();
    for (label, _) in branches {
        if !seen.insert(&label.name) {
            return false;
        }
    }
    true
}

/// Find duplicate label names in a global type.
fn find_duplicate_label(g: &GlobalType) -> Option<String> {
    match g {
        GlobalType::End | GlobalType::Var(_) => None,
        GlobalType::Comm { branches, .. } => {
            let mut seen = std::collections::HashSet::new();
            for (label, _) in branches {
                if !seen.insert(&label.name) {
                    return Some(label.name.clone());
                }
            }
            branches
                .iter()
                .find_map(|(_, cont)| find_duplicate_label(cont))
        }
        GlobalType::Mu { body, .. } => find_duplicate_label(body),
    }
}

/// Check if all branch labels are unique in a local type.
///
/// Corresponds to Lean's `uniqLabels` for local types.
#[must_use]
pub fn unique_labels_local(lt: &LocalTypeR) -> bool {
    match lt {
        LocalTypeR::End => true,
        LocalTypeR::Var(_) => true,
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            if !branches_unique_local(branches) {
                return false;
            }
            branches.iter().all(|(_l, _vt, cont)| unique_labels_local(cont))
        }
        LocalTypeR::Mu { body, .. } => unique_labels_local(body),
    }
}

/// Helper: check if all labels in a local branch list have unique names.
fn branches_unique_local(branches: &[(Label, Option<telltale_types::ValType>, LocalTypeR)]) -> bool {
    let mut seen = std::collections::HashSet::new();
    for (label, _vt, _) in branches {
        if !seen.insert(&label.name) {
            return false;
        }
    }
    true
}

/// Find duplicate label names in a local type.
fn find_duplicate_label_local(lt: &LocalTypeR) -> Option<String> {
    match lt {
        LocalTypeR::End | LocalTypeR::Var(_) => None,
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            let mut seen = std::collections::HashSet::new();
            for (label, _vt, _) in branches {
                if !seen.insert(&label.name) {
                    return Some(label.name.clone());
                }
            }
            branches
                .iter()
                .find_map(|(_l, _vt, cont)| find_duplicate_label_local(cont))
        }
        LocalTypeR::Mu { body, .. } => find_duplicate_label_local(body),
    }
}

/// Validate a local type for well-formedness.
///
/// # Examples
///
/// ```
/// use telltale_theory::validate_local;
/// use telltale_types::{LocalTypeR, Label};
///
/// // Well-formed local type
/// let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// assert!(validate_local(&lt).is_ok());
///
/// // Unbound variable is not well-formed
/// let bad = LocalTypeR::var("unbound");
/// assert!(validate_local(&bad).is_err());
/// ```
pub fn validate_local(lt: &LocalTypeR) -> ValidationResult {
    let mut errors = Vec::new();

    if !lt.all_vars_bound() {
        for var in lt.free_vars() {
            errors.push(ValidationError::UnboundVariable(var));
        }
    }

    if !lt.all_choices_non_empty() {
        errors.push(ValidationError::EmptyBranches);
    }

    if !lt.is_guarded() {
        errors.push(ValidationError::UnguardedRecursion);
    }

    if !unique_labels_local(lt) {
        if let Some(label) = find_duplicate_label_local(lt) {
            errors.push(ValidationError::DuplicateLabel(label));
        }
    }

    match errors.len() {
        0 => Ok(()),
        1 => Err(errors.pop().unwrap()),
        _ => Err(ValidationError::Multiple(errors)),
    }
}

/// Check if a global type is well-formed (returns bool).
#[must_use]
pub fn is_well_formed_global(g: &GlobalType) -> bool {
    g.well_formed()
}

/// Check if a local type is well-formed (returns bool).
#[must_use]
pub fn is_well_formed_local(lt: &LocalTypeR) -> bool {
    lt.well_formed()
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::Label;

    #[test]
    fn test_validate_global_simple() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        assert!(validate_global(&g).is_ok());
    }

    #[test]
    fn test_validate_global_recursive() {
        let g = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );
        assert!(validate_global(&g).is_ok());
    }

    #[test]
    fn test_validate_global_unbound_var() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("unbound"));
        let result = validate_global(&g);
        assert!(matches!(result, Err(ValidationError::UnboundVariable(_))));
    }

    #[test]
    fn test_validate_global_self_comm() {
        let g = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
        let result = validate_global(&g);
        assert!(matches!(result, Err(ValidationError::SelfCommunication(_))));
    }

    #[test]
    fn test_validate_global_unguarded() {
        let g = GlobalType::mu("t", GlobalType::var("t"));
        let result = validate_global(&g);
        assert!(matches!(result, Err(ValidationError::UnguardedRecursion)));
    }

    #[test]
    fn test_validate_local_simple() {
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        assert!(validate_local(&lt).is_ok());
    }

    #[test]
    fn test_validate_local_recursive() {
        let lt = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        assert!(validate_local(&lt).is_ok());
    }

    #[test]
    fn test_validate_local_unbound_var() {
        let lt = LocalTypeR::var("unbound");
        let result = validate_local(&lt);
        assert!(matches!(result, Err(ValidationError::UnboundVariable(_))));
    }

    #[test]
    fn test_validate_local_unguarded() {
        let lt = LocalTypeR::mu("t", LocalTypeR::var("t"));
        let result = validate_local(&lt);
        assert!(matches!(result, Err(ValidationError::UnguardedRecursion)));
    }

    #[test]
    fn test_is_well_formed() {
        let good = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let bad = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);

        assert!(is_well_formed_global(&good));
        assert!(!is_well_formed_global(&bad));
    }

    #[test]
    fn test_unique_labels_simple() {
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("accept"), GlobalType::End),
                (Label::new("reject"), GlobalType::End),
            ],
        );
        assert!(unique_labels(&g));
    }

    #[test]
    fn test_unique_labels_duplicate() {
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("msg"), GlobalType::End),
                (Label::new("msg"), GlobalType::End),
            ],
        );
        assert!(!unique_labels(&g));
    }

    #[test]
    fn test_unique_labels_nested() {
        // Outer labels unique, inner labels duplicate
        let inner = GlobalType::comm(
            "B",
            "C",
            vec![
                (Label::new("dup"), GlobalType::End),
                (Label::new("dup"), GlobalType::End),
            ],
        );
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("first"), inner),
                (Label::new("second"), GlobalType::End),
            ],
        );
        assert!(!unique_labels(&g));
    }

    #[test]
    fn test_unique_labels_recursive() {
        let g = GlobalType::mu(
            "t",
            GlobalType::comm(
                "A",
                "B",
                vec![
                    (Label::new("cont"), GlobalType::var("t")),
                    (Label::new("stop"), GlobalType::End),
                ],
            ),
        );
        assert!(unique_labels(&g));
    }

    #[test]
    fn test_unique_labels_local() {
        let lt = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("a"), None, LocalTypeR::End),
                (Label::new("b"), None, LocalTypeR::End),
            ],
        );
        assert!(unique_labels_local(&lt));

        let bad = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("x"), None, LocalTypeR::End),
                (Label::new("x"), None, LocalTypeR::End),
            ],
        );
        assert!(!unique_labels_local(&bad));
    }

    #[test]
    fn test_validate_global_duplicate_labels() {
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("msg"), GlobalType::End),
                (Label::new("msg"), GlobalType::End),
            ],
        );
        let result = validate_global(&g);
        assert!(matches!(result, Err(ValidationError::DuplicateLabel(ref s)) if s == "msg"));
    }

    #[test]
    fn test_validate_global_nested_duplicate_labels() {
        let inner = GlobalType::comm(
            "B",
            "C",
            vec![
                (Label::new("dup"), GlobalType::End),
                (Label::new("dup"), GlobalType::End),
            ],
        );
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("first"), inner),
                (Label::new("second"), GlobalType::End),
            ],
        );
        let result = validate_global(&g);
        assert!(matches!(result, Err(ValidationError::DuplicateLabel(ref s)) if s == "dup"));
    }

    #[test]
    fn test_validate_local_duplicate_labels() {
        let lt = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("x"), None, LocalTypeR::End),
                (Label::new("x"), None, LocalTypeR::End),
            ],
        );
        let result = validate_local(&lt);
        assert!(matches!(result, Err(ValidationError::DuplicateLabel(ref s)) if s == "x"));
    }

    #[test]
    fn test_validate_local_nested_duplicate_labels() {
        let inner = LocalTypeR::recv_choice(
            "C",
            vec![
                (Label::new("dup"), None, LocalTypeR::End),
                (Label::new("dup"), None, LocalTypeR::End),
            ],
        );
        let lt = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("first"), None, inner),
                (Label::new("second"), None, LocalTypeR::End),
            ],
        );
        let result = validate_local(&lt);
        assert!(matches!(result, Err(ValidationError::DuplicateLabel(ref s)) if s == "dup"));
    }
}
