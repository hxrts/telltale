//! Synchronous Subtyping for Local Session Types
//!
//! This module implements simple synchronous subtyping based on structural
//! comparison of session types.
//!
//! # Subtyping Rules
//!
//! For synchronous communication, subtyping follows these principles:
//!
//! - **Covariance for outputs (send)**: A subtype can send fewer messages
//! - **Contravariance for inputs (recv)**: A subtype must handle more messages
//!
//! Formally:
//! - `end <: end`
//! - `!p{lᵢ.Sᵢ} <: !p{l'ⱼ.T'ⱼ}` if `{lᵢ} ⊇ {l'ⱼ}` and `Sᵢ <: T'ᵢ` for matching labels
//! - `?p{lᵢ.Sᵢ} <: ?p{l'ⱼ.T'ⱼ}` if `{lᵢ} ⊆ {l'ⱼ}` and `Sᵢ <: T'ᵢ` for matching labels
//! - `μt.S <: μt.T` if `S <: T` (under assumption `t <: t`)

use telltale_types::LocalTypeR;
use std::collections::{HashMap, HashSet};
use thiserror::Error;

/// Errors that can occur during synchronous subtyping check
#[derive(Debug, Clone, Error)]
pub enum SyncSubtypeError {
    /// Partner mismatch
    #[error("partner mismatch: expected {expected}, found {found}")]
    PartnerMismatch { expected: String, found: String },

    /// Direction mismatch (send vs recv)
    #[error("direction mismatch: expected {expected}, found {found}")]
    DirectionMismatch { expected: String, found: String },

    /// Missing required label in subtype
    #[error("missing required label '{label}' in subtype")]
    MissingLabel { label: String },

    /// Extra label not allowed in subtype for recv
    #[error("extra label '{label}' not allowed in subtype (recv must be contravariant)")]
    ExtraLabel { label: String },

    /// Continuation subtyping failed
    #[error("continuation for label '{label}' is not a subtype")]
    ContinuationMismatch { label: String },

    /// Variable mismatch
    #[error("type variable mismatch: expected {expected}, found {found}")]
    VariableMismatch { expected: String, found: String },

    /// Incompatible types
    #[error("incompatible types: cannot compare {sub_type} with {super_type}")]
    IncompatibleTypes {
        sub_type: String,
        super_type: String,
    },
}

/// Check if `sub` is a subtype of `sup` using synchronous subtyping.
///
/// Returns `Ok(true)` if the subtyping holds, `Ok(false)` or `Err` otherwise.
///
/// # Examples
///
/// ```
/// use telltale_theory::sync_subtype;
/// use telltale_types::{LocalTypeR, Label};
///
/// // end <: end
/// assert!(sync_subtype(&LocalTypeR::End, &LocalTypeR::End).is_ok());
///
/// // !B{a.end, b.end} <: !B{a.end} (send can have more options)
/// let sub = LocalTypeR::send_choice("B", vec![
///     (Label::new("a"), LocalTypeR::End),
///     (Label::new("b"), LocalTypeR::End),
/// ]);
/// let sup = LocalTypeR::send("B", Label::new("a"), LocalTypeR::End);
/// assert!(sync_subtype(&sub, &sup).is_ok());
/// ```
pub fn sync_subtype(sub: &LocalTypeR, sup: &LocalTypeR) -> Result<(), SyncSubtypeError> {
    sync_subtype_with_assumptions(sub, sup, &mut HashSet::new())
}

fn sync_subtype_with_assumptions(
    sub: &LocalTypeR,
    sup: &LocalTypeR,
    assumptions: &mut HashSet<(String, String)>,
) -> Result<(), SyncSubtypeError> {
    // Fast path: identical types
    if sub == sup {
        return Ok(());
    }

    match (sub, sup) {
        // end <: end
        (LocalTypeR::End, LocalTypeR::End) => Ok(()),

        // !p{...} <: !p{...} - covariant in labels
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
                return Err(SyncSubtypeError::PartnerMismatch {
                    expected: p2.clone(),
                    found: p1.clone(),
                });
            }

            // Subtype must have all labels of supertype
            let sub_labels: HashMap<_, _> = b1.iter().map(|(l, c)| (&l.name, c)).collect();

            for (label, sup_cont) in b2 {
                match sub_labels.get(&label.name) {
                    Some(sub_cont) => {
                        sync_subtype_with_assumptions(sub_cont, sup_cont, assumptions).map_err(
                            |_| SyncSubtypeError::ContinuationMismatch {
                                label: label.name.clone(),
                            },
                        )?;
                    }
                    None => {
                        return Err(SyncSubtypeError::MissingLabel {
                            label: label.name.clone(),
                        });
                    }
                }
            }

            Ok(())
        }

        // ?p{...} <: ?p{...} - contravariant in labels
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
                return Err(SyncSubtypeError::PartnerMismatch {
                    expected: p2.clone(),
                    found: p1.clone(),
                });
            }

            // Supertype must have all labels of subtype (contravariance)
            let sup_labels: HashMap<_, _> = b2.iter().map(|(l, c)| (&l.name, c)).collect();
            let sub_labels: HashMap<_, _> = b1.iter().map(|(l, c)| (&l.name, c)).collect();

            // Check subtype doesn't have extra labels
            for (label, _) in b1 {
                if !sup_labels.contains_key(&label.name) {
                    return Err(SyncSubtypeError::ExtraLabel {
                        label: label.name.clone(),
                    });
                }
            }

            // Check continuations for matching labels
            for (label, sup_cont) in b2 {
                if let Some(sub_cont) = sub_labels.get(&label.name) {
                    sync_subtype_with_assumptions(sub_cont, sup_cont, assumptions).map_err(
                        |_| SyncSubtypeError::ContinuationMismatch {
                            label: label.name.clone(),
                        },
                    )?;
                }
            }

            Ok(())
        }

        // μt.S <: μt.T
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
            // Add assumption that v1 <: v2
            let assumption = (v1.clone(), v2.clone());
            if assumptions.contains(&assumption) {
                return Ok(()); // Coinductive assumption
            }

            assumptions.insert(assumption.clone());
            let result = sync_subtype_with_assumptions(body1, body2, assumptions);
            assumptions.remove(&assumption);

            result
        }

        // t <: t
        (LocalTypeR::Var(v1), LocalTypeR::Var(v2)) => {
            if v1 == v2 || assumptions.contains(&(v1.clone(), v2.clone())) {
                Ok(())
            } else {
                Err(SyncSubtypeError::VariableMismatch {
                    expected: v2.clone(),
                    found: v1.clone(),
                })
            }
        }

        // Direction mismatch
        (LocalTypeR::Send { .. }, LocalTypeR::Recv { .. }) => {
            Err(SyncSubtypeError::DirectionMismatch {
                expected: "recv".to_string(),
                found: "send".to_string(),
            })
        }
        (LocalTypeR::Recv { .. }, LocalTypeR::Send { .. }) => {
            Err(SyncSubtypeError::DirectionMismatch {
                expected: "send".to_string(),
                found: "recv".to_string(),
            })
        }

        // Incompatible types
        _ => Err(SyncSubtypeError::IncompatibleTypes {
            sub_type: format!("{:?}", sub),
            super_type: format!("{:?}", sup),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::Label;

    #[test]
    fn test_end_subtype() {
        assert!(sync_subtype(&LocalTypeR::End, &LocalTypeR::End).is_ok());
    }

    #[test]
    fn test_send_identical() {
        let t = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        assert!(sync_subtype(&t, &t).is_ok());
    }

    #[test]
    fn test_send_covariant() {
        // !B{a.end, b.end} <: !B{a.end}
        let sub = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("a"), LocalTypeR::End),
                (Label::new("b"), LocalTypeR::End),
            ],
        );
        let sup = LocalTypeR::send("B", Label::new("a"), LocalTypeR::End);
        assert!(sync_subtype(&sub, &sup).is_ok());
    }

    #[test]
    fn test_send_missing_label() {
        // !B{a.end} NOT<: !B{b.end}
        let sub = LocalTypeR::send("B", Label::new("a"), LocalTypeR::End);
        let sup = LocalTypeR::send("B", Label::new("b"), LocalTypeR::End);
        assert!(sync_subtype(&sub, &sup).is_err());
    }

    #[test]
    fn test_recv_contravariant() {
        // ?A{a.end} <: ?A{a.end, b.end}
        let sub = LocalTypeR::recv("A", Label::new("a"), LocalTypeR::End);
        let sup = LocalTypeR::recv_choice(
            "A",
            vec![
                (Label::new("a"), LocalTypeR::End),
                (Label::new("b"), LocalTypeR::End),
            ],
        );
        assert!(sync_subtype(&sub, &sup).is_ok());
    }

    #[test]
    fn test_recv_extra_label_fails() {
        // ?A{a.end, b.end} NOT<: ?A{a.end}
        let sub = LocalTypeR::recv_choice(
            "A",
            vec![
                (Label::new("a"), LocalTypeR::End),
                (Label::new("b"), LocalTypeR::End),
            ],
        );
        let sup = LocalTypeR::recv("A", Label::new("a"), LocalTypeR::End);
        assert!(sync_subtype(&sub, &sup).is_err());
    }

    #[test]
    fn test_partner_mismatch() {
        let sub = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let sup = LocalTypeR::send("C", Label::new("msg"), LocalTypeR::End);
        assert!(matches!(
            sync_subtype(&sub, &sup),
            Err(SyncSubtypeError::PartnerMismatch { .. })
        ));
    }

    #[test]
    fn test_direction_mismatch() {
        let sub = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let sup = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);
        assert!(matches!(
            sync_subtype(&sub, &sup),
            Err(SyncSubtypeError::DirectionMismatch { .. })
        ));
    }

    #[test]
    fn test_recursive_subtype() {
        let sub = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        let sup = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        assert!(sync_subtype(&sub, &sup).is_ok());
    }

    #[test]
    fn test_var_subtype() {
        let sub = LocalTypeR::var("t");
        let sup = LocalTypeR::var("t");
        assert!(sync_subtype(&sub, &sup).is_ok());
    }

    #[test]
    fn test_var_mismatch() {
        let sub = LocalTypeR::var("t");
        let sup = LocalTypeR::var("s");
        assert!(matches!(
            sync_subtype(&sub, &sup),
            Err(SyncSubtypeError::VariableMismatch { .. })
        ));
    }
}
