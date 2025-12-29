//! Projection of Global Types to Local Types
//!
//! This module implements the projection operation that transforms a global type
//! (bird's-eye view of a protocol) into a local type for a specific role.
//!
//! Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//!
//! # Projection Rules
//!
//! For a global type `G` and role `r`, the projection `G↓r` is defined as:
//!
//! - `end↓r = end`
//! - `(p → q : {lᵢ.Gᵢ})↓r`:
//!   - If `r = p`: `!q{lᵢ.(Gᵢ↓r)}` (sender sees internal choice)
//!   - If `r = q`: `?p{lᵢ.(Gᵢ↓r)}` (receiver sees external choice)
//!   - Otherwise: `merge(Gᵢ↓r)` (non-participant merges branches)
//! - `(μt.G)↓r = μt.(G↓r)`
//! - `t↓r = t`

use crate::merge::{merge_all, MergeError};
use rumpsteak_types::{GlobalType, Label, LocalTypeR};
use thiserror::Error;

/// Errors that can occur during projection
#[derive(Debug, Clone, Error)]
pub enum ProjectionError {
    /// Role not found in the protocol
    #[error("role '{0}' not found in protocol")]
    RoleNotFound(String),

    /// Branches could not be merged for a non-participant
    #[error("cannot merge branches for role '{role}': {source}")]
    MergeFailure {
        role: String,
        #[source]
        source: MergeError,
    },

    /// Empty branches in communication
    #[error("empty branches in communication from {sender} to {receiver}")]
    EmptyBranches { sender: String, receiver: String },
}

/// Result type for projection operations
pub type ProjectionResult = Result<LocalTypeR, ProjectionError>;

/// Project a global type onto a specific role.
///
/// This transforms a bird's-eye view protocol description into the local
/// view for a single participant.
///
/// # Examples
///
/// ```
/// use rumpsteak_theory::project;
/// use rumpsteak_types::{GlobalType, LocalTypeR, Label};
///
/// // A -> B: msg. end
/// let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
///
/// // From A's perspective: send msg to B, then end
/// let a_view = project(&g, "A").unwrap();
/// assert!(matches!(a_view, LocalTypeR::Send { partner, .. } if partner == "B"));
///
/// // From B's perspective: receive msg from A, then end
/// let b_view = project(&g, "B").unwrap();
/// assert!(matches!(b_view, LocalTypeR::Recv { partner, .. } if partner == "A"));
/// ```
pub fn project(global: &GlobalType, role: &str) -> ProjectionResult {
    match global {
        GlobalType::End => Ok(LocalTypeR::End),

        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            if branches.is_empty() {
                return Err(ProjectionError::EmptyBranches {
                    sender: sender.clone(),
                    receiver: receiver.clone(),
                });
            }

            if role == sender {
                // Sender sees internal choice (send)
                let local_branches: Vec<(Label, LocalTypeR)> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let local_cont = project(cont, role)?;
                        Ok((label.clone(), local_cont))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(LocalTypeR::Send {
                    partner: receiver.clone(),
                    branches: local_branches,
                })
            } else if role == receiver {
                // Receiver sees external choice (recv)
                let local_branches: Vec<(Label, LocalTypeR)> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let local_cont = project(cont, role)?;
                        Ok((label.clone(), local_cont))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(LocalTypeR::Recv {
                    partner: sender.clone(),
                    branches: local_branches,
                })
            } else {
                // Non-participant: merge all branch projections
                let projections: Vec<LocalTypeR> = branches
                    .iter()
                    .map(|(_, cont)| project(cont, role))
                    .collect::<Result<Vec<_>, _>>()?;

                merge_all(&projections).map_err(|e| ProjectionError::MergeFailure {
                    role: role.to_string(),
                    source: e,
                })
            }
        }

        GlobalType::Mu { var, body } => {
            let local_body = project(body, role)?;

            // Optimization: if the role doesn't appear in the body, return End
            // This handles the case where a role is not involved after a recursion point
            if matches!(local_body, LocalTypeR::End) && !body_mentions_role(body, role) {
                return Ok(LocalTypeR::End);
            }

            Ok(LocalTypeR::Mu {
                var: var.clone(),
                body: Box::new(local_body),
            })
        }

        GlobalType::Var(var) => Ok(LocalTypeR::Var(var.clone())),
    }
}

/// Check if a global type body mentions a specific role
fn body_mentions_role(global: &GlobalType, role: &str) -> bool {
    match global {
        GlobalType::End => false,
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            sender == role
                || receiver == role
                || branches
                    .iter()
                    .any(|(_, cont)| body_mentions_role(cont, role))
        }
        GlobalType::Mu { body, .. } => body_mentions_role(body, role),
        GlobalType::Var(_) => false,
    }
}

/// Project a global type onto all its roles.
///
/// Returns a map from role names to their local types.
pub fn project_all(global: &GlobalType) -> Result<Vec<(String, LocalTypeR)>, ProjectionError> {
    let roles = global.roles();
    roles
        .into_iter()
        .map(|role| {
            let local = project(global, &role)?;
            Ok((role, local))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_project_end() {
        let g = GlobalType::End;
        let local = project(&g, "A").unwrap();
        assert_eq!(local, LocalTypeR::End);
    }

    #[test]
    fn test_project_sender() {
        // A -> B: msg. end
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local = project(&g, "A").unwrap();

        match local {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
                assert_eq!(branches[0].1, LocalTypeR::End);
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_project_receiver() {
        // A -> B: msg. end
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local = project(&g, "B").unwrap();

        match local {
            LocalTypeR::Recv { partner, branches } => {
                assert_eq!(partner, "A");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
            }
            _ => panic!("Expected Recv"),
        }
    }

    #[test]
    fn test_project_non_participant() {
        // A -> B: msg. end
        // C is not involved, should get End
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local = project(&g, "C").unwrap();
        assert_eq!(local, LocalTypeR::End);
    }

    #[test]
    fn test_project_choice() {
        // A -> B: {yes.end, no.end}
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("yes"), GlobalType::End),
                (Label::new("no"), GlobalType::End),
            ],
        );

        // A sees internal choice
        let a_local = project(&g, "A").unwrap();
        match a_local {
            LocalTypeR::Send { branches, .. } => {
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Send"),
        }

        // B sees external choice
        let b_local = project(&g, "B").unwrap();
        match b_local {
            LocalTypeR::Recv { branches, .. } => {
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Recv"),
        }
    }

    #[test]
    fn test_project_recursive() {
        // μt. A -> B: msg. t
        let g = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );

        let a_local = project(&g, "A").unwrap();
        match a_local {
            LocalTypeR::Mu { var, body } => {
                assert_eq!(var, "t");
                match body.as_ref() {
                    LocalTypeR::Send { partner, branches } => {
                        assert_eq!(partner, "B");
                        assert!(matches!(branches[0].1, LocalTypeR::Var(ref v) if v == "t"));
                    }
                    _ => panic!("Expected Send in body"),
                }
            }
            _ => panic!("Expected Mu"),
        }
    }

    #[test]
    fn test_project_all() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let projections = project_all(&g).unwrap();

        assert_eq!(projections.len(), 2);
        let a_proj = projections.iter().find(|(r, _)| r == "A").unwrap();
        let b_proj = projections.iter().find(|(r, _)| r == "B").unwrap();

        assert!(matches!(a_proj.1, LocalTypeR::Send { .. }));
        assert!(matches!(b_proj.1, LocalTypeR::Recv { .. }));
    }

    #[test]
    fn test_project_three_party_merge() {
        // A -> B: {l1. C -> B: x. end, l2. C -> B: y. end}
        // From C's perspective, it should merge the two branches
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (
                    Label::new("l1"),
                    GlobalType::send("C", "B", Label::new("x"), GlobalType::End),
                ),
                (
                    Label::new("l2"),
                    GlobalType::send("C", "B", Label::new("y"), GlobalType::End),
                ),
            ],
        );

        let c_local = project(&g, "C").unwrap();

        // C should see: !B{x.end, y.end} (merged from both branches)
        match c_local {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Send with merged branches"),
        }
    }
}
