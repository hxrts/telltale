//! Asynchronous Subtyping for Local Session Types
//!
//! This module implements precise asynchronous subtyping based on the POPL 2021
//! paper "Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al.)
//!
//! # SISO Decomposition
//!
//! The key insight is that asynchronous subtyping can be characterized by
//! decomposing session types into input and output trees (SISO = Single-Input-Single-Output).
//!
//! An input tree contains only receive operations, and an output tree contains
//! only send operations. A local type is a valid asynchronous type if it can
//! be decomposed into alternating input and output phases.

use crate::limits::{UnfoldSteps, DEFAULT_SISO_UNFOLD_STEPS};
use std::collections::BTreeMap;
use telltale_types::{Label, LocalTypeR};
use thiserror::Error;

/// Errors during asynchronous subtyping
#[derive(Debug, Clone, Error)]
pub enum AsyncSubtypeError {
    /// Type is not SISO decomposable
    #[error("type is not SISO decomposable")]
    NotSisoDecomposable,

    /// Input tree mismatch
    #[error("input trees do not match")]
    InputTreeMismatch,

    /// Output tree mismatch
    #[error("output trees do not match")]
    OutputTreeMismatch,

    /// Segment phase mismatch
    #[error("siso phase mismatch: subtype has {sub} segments, supertype has {sup}")]
    PhaseMismatch { sub: usize, sup: usize },

    /// SISO decomposition exceeded the unfold limit.
    #[error("siso decomposition exceeded the unfold limit")]
    UnfoldLimitExceeded,
}

/// Direction for SISO tree building
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    /// Input direction (receives)
    Input,
    /// Output direction (sends)
    Output,
}

/// An input tree (receives only)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputTree {
    /// No input
    Empty,
    /// Receive from partner
    Recv {
        partner: String,
        branches: Vec<(Label, InputTree)>,
    },
}

/// An output tree (sends only)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OutputTree {
    /// No output
    Empty,
    /// Send to partner
    Send {
        partner: String,
        branches: Vec<(Label, OutputTree)>,
    },
}

/// A SISO segment representing one input-output phase
#[derive(Debug, Clone)]
pub struct SisoSegment {
    /// Input tree for this phase
    pub input: InputTree,
    /// Output tree for this phase
    pub output: OutputTree,
}

/// Decompose a local type into SISO segments.
///
/// This is the core algorithm for asynchronous subtyping.
/// A type is async-subtypable if it can be decomposed into a sequence
/// of SISO segments.
///
/// # Examples
///
/// ```
/// use telltale_theory::siso_decompose;
/// use telltale_types::{LocalTypeR, Label};
///
/// // Simple send then receive
/// let t = LocalTypeR::send(
///     "B",
///     Label::new("req"),
///     LocalTypeR::recv("B", Label::new("resp"), LocalTypeR::End),
/// );
///
/// let segments = siso_decompose(&t).unwrap();
/// assert!(!segments.is_empty());
/// ```
pub fn siso_decompose(lt: &LocalTypeR) -> Result<Vec<SisoSegment>, AsyncSubtypeError> {
    siso_decompose_with_fuel(lt, DEFAULT_SISO_UNFOLD_STEPS)
}

/// Decompose a local type into SISO segments with an explicit unfold limit.
pub fn siso_decompose_with_fuel(
    lt: &LocalTypeR,
    fuel: UnfoldSteps,
) -> Result<Vec<SisoSegment>, AsyncSubtypeError> {
    let mut segments = Vec::new();
    let mut remaining_unfolds = fuel.0;
    siso_decompose_impl(lt, &mut segments, &mut remaining_unfolds)?;
    Ok(segments)
}

fn siso_decompose_impl(
    lt: &LocalTypeR,
    segments: &mut Vec<SisoSegment>,
    remaining_unfolds: &mut u32,
) -> Result<(), AsyncSubtypeError> {
    match lt {
        LocalTypeR::End => {
            // End is valid SISO
            Ok(())
        }

        LocalTypeR::Send {
            partner: _,
            branches: _,
        } => {
            // Start or extend output phase
            let output = build_output_tree(lt)?;
            let continuation = find_output_continuation(lt);

            segments.push(SisoSegment {
                input: InputTree::Empty,
                output,
            });

            if let Some(cont) = continuation {
                siso_decompose_impl(&cont, segments, remaining_unfolds)?;
            }

            Ok(())
        }

        LocalTypeR::Recv {
            partner: _,
            branches: _,
        } => {
            // Start or extend input phase
            let input = build_input_tree(lt)?;
            let continuation = find_input_continuation(lt);

            segments.push(SisoSegment {
                input,
                output: OutputTree::Empty,
            });

            if let Some(cont) = continuation {
                siso_decompose_impl(&cont, segments, remaining_unfolds)?;
            }

            Ok(())
        }

        LocalTypeR::Mu { var, body } => {
            if *remaining_unfolds == 0 {
                return Err(AsyncSubtypeError::UnfoldLimitExceeded);
            }
            *remaining_unfolds -= 1;
            // Handle recursion by unfolding once
            let unfolded = body.substitute(var, lt);
            siso_decompose_impl(&unfolded, segments, remaining_unfolds)
        }

        LocalTypeR::Var(_) => {
            // Variable reference - valid in recursive context
            Ok(())
        }
    }
}

/// Check if a LocalTypeR matches the given direction (Send for Output, Recv for Input)
fn matches_direction(lt: &LocalTypeR, direction: Direction) -> bool {
    matches!(
        (direction, lt),
        (Direction::Output, LocalTypeR::Send { .. }) | (Direction::Input, LocalTypeR::Recv { .. })
    )
}

type LocalBranch = (Label, Option<telltale_types::ValType>, LocalTypeR);
type LocalBranchSlice<'a> = &'a [LocalBranch];

/// Extract partner and branches from a LocalTypeR if it matches the direction
fn extract_components(
    lt: &LocalTypeR,
    direction: Direction,
) -> Option<(&String, LocalBranchSlice<'_>)> {
    match (direction, lt) {
        (Direction::Output, LocalTypeR::Send { partner, branches }) => Some((partner, branches)),
        (Direction::Input, LocalTypeR::Recv { partner, branches }) => Some((partner, branches)),
        _ => None,
    }
}

/// Build a SISO tree in the given direction.
///
/// This is the unified implementation for both input and output tree building.
/// The direction determines whether we extract Send operations (Output) or
/// Recv operations (Input).
fn build_siso_tree<T>(
    lt: &LocalTypeR,
    direction: Direction,
    empty: fn() -> T,
    construct: fn(String, Vec<(Label, T)>) -> T,
) -> Result<T, AsyncSubtypeError>
where
    T: Clone,
{
    // Handle terminal cases
    if matches!(lt, LocalTypeR::End | LocalTypeR::Var(_)) {
        return Ok(empty());
    }

    // Extract components if direction matches
    let Some((partner, branches)) = extract_components(lt, direction) else {
        return Err(AsyncSubtypeError::NotSisoDecomposable);
    };

    let tree_branches: Vec<_> = branches
        .iter()
        .map(|(label, _vt, cont)| {
            let sub_tree = if matches_direction(cont, direction) {
                build_siso_tree(cont, direction, empty, construct)?
            } else {
                empty()
            };
            Ok((label.clone(), sub_tree))
        })
        .collect::<Result<Vec<_>, AsyncSubtypeError>>()?;

    Ok(construct(partner.clone(), tree_branches))
}

fn build_output_tree(lt: &LocalTypeR) -> Result<OutputTree, AsyncSubtypeError> {
    build_siso_tree(
        lt,
        Direction::Output,
        || OutputTree::Empty,
        |partner, branches| OutputTree::Send { partner, branches },
    )
}

fn build_input_tree(lt: &LocalTypeR) -> Result<InputTree, AsyncSubtypeError> {
    build_siso_tree(
        lt,
        Direction::Input,
        || InputTree::Empty,
        |partner, branches| InputTree::Recv { partner, branches },
    )
}

fn find_output_continuation(lt: &LocalTypeR) -> Option<LocalTypeR> {
    match lt {
        LocalTypeR::Send { branches, .. } => {
            // Find first non-send continuation
            for (_l, _vt, cont) in branches {
                if !matches!(cont, LocalTypeR::Send { .. }) {
                    return Some(cont.clone());
                }
                if let Some(inner) = find_output_continuation(cont) {
                    return Some(inner);
                }
            }
            None
        }
        _ => None,
    }
}

fn find_input_continuation(lt: &LocalTypeR) -> Option<LocalTypeR> {
    match lt {
        LocalTypeR::Recv { branches, .. } => {
            // Find first non-recv continuation
            for (_l, _vt, cont) in branches {
                if !matches!(cont, LocalTypeR::Recv { .. }) {
                    return Some(cont.clone());
                }
                if let Some(inner) = find_input_continuation(cont) {
                    return Some(inner);
                }
            }
            None
        }
        _ => None,
    }
}

/// Check if sub is an asynchronous subtype of sup.
///
/// Asynchronous subtyping is more permissive than synchronous subtyping,
/// allowing reordering of independent sends and receives.
///
/// This implementation intentionally enforces a conservative subset of
/// asynchronous subtyping. Two types are considered compatible only when
/// their SISO decomposition has matching phases and each input/output tree
/// is structurally compatible.
///
/// This API is experimental and may be tightened as Lean parity coverage grows.
///
/// # Examples
///
/// ```
/// use telltale_theory::async_subtype;
/// use telltale_types::{LocalTypeR, Label};
///
/// let t1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let t2 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// assert!(async_subtype(&t1, &t2).is_ok());
/// ```
pub fn async_subtype(sub: &LocalTypeR, sup: &LocalTypeR) -> Result<(), AsyncSubtypeError> {
    let sub_segments = siso_decompose(sub)?;
    let sup_segments = siso_decompose(sup)?;

    if sub_segments.len() != sup_segments.len() {
        return Err(AsyncSubtypeError::PhaseMismatch {
            sub: sub_segments.len(),
            sup: sup_segments.len(),
        });
    }

    for (sub_seg, sup_seg) in sub_segments.iter().zip(sup_segments.iter()) {
        if !input_tree_compatible(&sub_seg.input, &sup_seg.input) {
            return Err(AsyncSubtypeError::InputTreeMismatch);
        }
        if !output_tree_compatible(&sub_seg.output, &sup_seg.output) {
            return Err(AsyncSubtypeError::OutputTreeMismatch);
        }
    }

    Ok(())
}

fn input_tree_compatible(sub: &InputTree, sup: &InputTree) -> bool {
    match (sub, sup) {
        (InputTree::Empty, InputTree::Empty) => true,
        (
            InputTree::Recv {
                partner: sub_partner,
                branches: sub_branches,
            },
            InputTree::Recv {
                partner: sup_partner,
                branches: sup_branches,
            },
        ) => {
            if sub_partner != sup_partner || sub_branches.len() != sup_branches.len() {
                return false;
            }

            let sup_by_name: BTreeMap<&str, (&Label, &InputTree)> = sup_branches
                .iter()
                .map(|(label, tree)| (label.name.as_str(), (label, tree)))
                .collect();

            sub_branches.iter().all(|(sub_label, sub_tree)| {
                sup_by_name
                    .get(sub_label.name.as_str())
                    .is_some_and(|(sup_label, sup_tree)| {
                        *sub_label == **sup_label && input_tree_compatible(sub_tree, sup_tree)
                    })
            })
        }
        _ => false,
    }
}

fn output_tree_compatible(sub: &OutputTree, sup: &OutputTree) -> bool {
    match (sub, sup) {
        (OutputTree::Empty, OutputTree::Empty) => true,
        (
            OutputTree::Send {
                partner: sub_partner,
                branches: sub_branches,
            },
            OutputTree::Send {
                partner: sup_partner,
                branches: sup_branches,
            },
        ) => {
            if sub_partner != sup_partner || sub_branches.len() != sup_branches.len() {
                return false;
            }

            let sup_by_name: BTreeMap<&str, (&Label, &OutputTree)> = sup_branches
                .iter()
                .map(|(label, tree)| (label.name.as_str(), (label, tree)))
                .collect();

            sub_branches.iter().all(|(sub_label, sub_tree)| {
                sup_by_name
                    .get(sub_label.name.as_str())
                    .is_some_and(|(sup_label, sup_tree)| {
                        *sub_label == **sup_label && output_tree_compatible(sub_tree, sup_tree)
                    })
            })
        }
        _ => false,
    }
}

/// Check if a local type is orphan-free.
///
/// A type is orphan-free if every message that is sent will eventually be received.
/// This prevents deadlocks caused by orphan messages in async communication.
///
/// Note: This is a conservative approximation. A full orphan-free check requires
/// analyzing the complete protocol composition.
/// This API is experimental.
///
/// # Examples
///
/// ```
/// use telltale_theory::orphan_free;
/// use telltale_types::LocalTypeR;
///
/// // End is always orphan-free
/// assert!(orphan_free(&LocalTypeR::End));
/// ```
pub fn orphan_free(lt: &LocalTypeR) -> bool {
    // Conservative approximation:
    // every send branch must contain a reachable matching receive.
    check_orphan_free(lt, &mut Vec::new())
}

fn check_orphan_free(lt: &LocalTypeR, mu_stack: &mut Vec<String>) -> bool {
    match lt {
        LocalTypeR::End => true,

        LocalTypeR::Send { partner, branches } => {
            for (label, _vt, cont) in branches {
                if !has_reachable_recv(cont, partner, &label.name, &mut Vec::new()) {
                    return false;
                }
                if !check_orphan_free(cont, mu_stack) {
                    return false;
                }
            }
            true
        }

        LocalTypeR::Recv { branches, .. } => {
            for (_label, _vt, cont) in branches {
                if !check_orphan_free(cont, mu_stack) {
                    return false;
                }
            }
            true
        }

        LocalTypeR::Mu { var, body } => {
            if mu_stack.iter().any(|v| v == var) {
                return true;
            }
            mu_stack.push(var.clone());
            let ok = check_orphan_free(body, mu_stack);
            mu_stack.pop();
            ok
        }

        // Conservative handling for open recursion references.
        LocalTypeR::Var(_) => true,
    }
}

fn has_reachable_recv(
    lt: &LocalTypeR,
    partner: &str,
    label_name: &str,
    mu_stack: &mut Vec<String>,
) -> bool {
    match lt {
        LocalTypeR::End => false,
        LocalTypeR::Send { branches, .. } => branches
            .iter()
            .any(|(_label, _vt, cont)| has_reachable_recv(cont, partner, label_name, mu_stack)),
        LocalTypeR::Recv {
            partner: recv_partner,
            branches,
        } => {
            if recv_partner == partner
                && branches
                    .iter()
                    .any(|(recv_label, _vt, _)| recv_label.name == label_name)
            {
                return true;
            }
            branches
                .iter()
                .any(|(_label, _vt, cont)| has_reachable_recv(cont, partner, label_name, mu_stack))
        }
        LocalTypeR::Mu { var, body } => {
            if mu_stack.iter().any(|v| v == var) {
                return false;
            }
            mu_stack.push(var.clone());
            let found = has_reachable_recv(body, partner, label_name, mu_stack);
            mu_stack.pop();
            found
        }
        LocalTypeR::Var(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_siso_decompose_end() {
        let segments = siso_decompose(&LocalTypeR::End).unwrap();
        assert!(segments.is_empty());
    }

    #[test]
    fn test_siso_decompose_send() {
        let t = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let segments = siso_decompose(&t).unwrap();
        assert_eq!(segments.len(), 1);
        assert!(matches!(segments[0].output, OutputTree::Send { .. }));
    }

    #[test]
    fn test_siso_decompose_recv() {
        let t = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
        let segments = siso_decompose(&t).unwrap();
        assert_eq!(segments.len(), 1);
        assert!(matches!(segments[0].input, InputTree::Recv { .. }));
    }

    #[test]
    fn test_async_subtype_identical() {
        let t = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        assert!(async_subtype(&t, &t).is_ok());
    }

    #[test]
    fn test_async_subtype_label_mismatch_fails() {
        let sub = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let sup = LocalTypeR::send("B", Label::new("other"), LocalTypeR::End);
        assert!(matches!(
            async_subtype(&sub, &sup),
            Err(AsyncSubtypeError::OutputTreeMismatch)
        ));
    }

    #[test]
    fn test_async_subtype_phase_mismatch_fails() {
        let sub = LocalTypeR::send(
            "B",
            Label::new("req"),
            LocalTypeR::recv("B", Label::new("resp"), LocalTypeR::End),
        );
        let sup = LocalTypeR::send("B", Label::new("req"), LocalTypeR::End);

        assert!(matches!(
            async_subtype(&sub, &sup),
            Err(AsyncSubtypeError::PhaseMismatch { .. })
        ));
    }

    #[test]
    fn test_async_subtype_partner_mismatch_fails() {
        let sub = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
        let sup = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);
        assert!(matches!(
            async_subtype(&sub, &sup),
            Err(AsyncSubtypeError::InputTreeMismatch)
        ));
    }

    #[test]
    fn test_orphan_free_simple() {
        let t = LocalTypeR::send(
            "B",
            Label::new("req"),
            LocalTypeR::recv("B", Label::new("resp"), LocalTypeR::End),
        );
        assert!(!orphan_free(&t));
    }

    #[test]
    fn test_orphan_free_matching_label() {
        let t = LocalTypeR::send(
            "B",
            Label::new("req"),
            LocalTypeR::recv("B", Label::new("req"), LocalTypeR::End),
        );
        assert!(orphan_free(&t));
    }

    #[test]
    fn test_orphan_free_unmatched_send() {
        let t = LocalTypeR::send("B", Label::new("req"), LocalTypeR::End);
        assert!(!orphan_free(&t));
    }

    #[test]
    fn test_orphan_free_end() {
        assert!(orphan_free(&LocalTypeR::End));
    }

    #[test]
    fn test_input_tree_build() {
        let t = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
        let tree = build_input_tree(&t).unwrap();
        match tree {
            InputTree::Recv { partner, branches } => {
                assert_eq!(partner, "A");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
            }
            _ => panic!("Expected Recv tree"),
        }
    }

    #[test]
    fn test_output_tree_build() {
        let t = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let tree = build_output_tree(&t).unwrap();
        match tree {
            OutputTree::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
            }
            _ => panic!("Expected Send tree"),
        }
    }

    #[test]
    fn test_build_input_tree_not_siso() {
        let t = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        assert!(matches!(
            build_input_tree(&t),
            Err(AsyncSubtypeError::NotSisoDecomposable)
        ));
    }

    #[test]
    fn test_siso_decompose_unfold_limit_exceeded() {
        let t = LocalTypeR::mu(
            "X",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("X")),
        );
        assert!(matches!(
            siso_decompose_with_fuel(&t, UnfoldSteps(0)),
            Err(AsyncSubtypeError::UnfoldLimitExceeded)
        ));
    }
}
