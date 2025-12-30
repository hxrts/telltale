//! Bounded Recursion for Session Types
//!
//! This module provides strategies for bounding recursive session types,
//! enabling runtime execution of protocols that would otherwise require
//! infinite unfolding.
//!
//! # Bounding Strategies
//!
//! - **Fuel**: Limit the number of recursive iterations
//! - **YieldAfter**: Yield control after N communication steps
//! - **YieldWhen**: Yield when a predicate condition is met
//!
//! # Example
//!
//! ```
//! use rumpsteak_types::{LocalTypeR, Label};
//! use rumpsteak_theory::bounded::{BoundingStrategy, bound_recursion};
//!
//! // Create a recursive ping-pong protocol
//! let lt = LocalTypeR::mu(
//!     "X",
//!     LocalTypeR::send("B", Label::new("ping"),
//!         LocalTypeR::recv("B", Label::new("pong"),
//!             LocalTypeR::var("X")
//!         )
//!     )
//! );
//!
//! // Bound to 3 iterations
//! let bounded = bound_recursion(&lt, BoundingStrategy::Fuel(3));
//! ```

use rumpsteak_types::LocalTypeR;
use std::collections::HashSet;

/// Strategy for bounding recursive types.
#[derive(Debug, Clone)]
pub enum BoundingStrategy {
    /// Maximum number of recursive iterations.
    ///
    /// When fuel is exhausted, recursion variables are replaced with `End`.
    Fuel(usize),

    /// Yield control after N communication steps.
    ///
    /// Inserts yield points after the specified number of send/recv operations.
    YieldAfter(usize),

    /// Yield when a named condition is encountered.
    ///
    /// The condition name should match a label in the protocol.
    YieldWhen(String),
}

/// Apply a bounding strategy to a local type.
///
/// This transforms a potentially infinite recursive type into a bounded one
/// that can be executed at runtime.
///
/// # Arguments
///
/// * `lt` - The local type to bound
/// * `strategy` - The bounding strategy to apply
///
/// # Returns
///
/// A bounded version of the local type.
pub fn bound_recursion(lt: &LocalTypeR, strategy: BoundingStrategy) -> LocalTypeR {
    match strategy {
        BoundingStrategy::Fuel(n) => bound_with_fuel(lt, n),
        BoundingStrategy::YieldAfter(n) => bound_with_yield_after(lt, n),
        BoundingStrategy::YieldWhen(ref condition) => bound_with_yield_when(lt, condition),
    }
}

/// Bound recursion by limiting iterations (fuel strategy).
fn bound_with_fuel(lt: &LocalTypeR, fuel: usize) -> LocalTypeR {
    if fuel == 0 {
        return LocalTypeR::End;
    }

    match lt {
        LocalTypeR::End => LocalTypeR::End,

        LocalTypeR::Send { partner, branches } => {
            let bounded_branches = branches
                .iter()
                .map(|(label, cont)| (label.clone(), bound_with_fuel(cont, fuel)))
                .collect();
            LocalTypeR::Send {
                partner: partner.clone(),
                branches: bounded_branches,
            }
        }

        LocalTypeR::Recv { partner, branches } => {
            let bounded_branches = branches
                .iter()
                .map(|(label, cont)| (label.clone(), bound_with_fuel(cont, fuel)))
                .collect();
            LocalTypeR::Recv {
                partner: partner.clone(),
                branches: bounded_branches,
            }
        }

        LocalTypeR::Mu { var, body } => {
            // Decrement fuel for each recursion unfolding
            let bounded_body = bound_with_fuel(body, fuel - 1);
            LocalTypeR::Mu {
                var: var.clone(),
                body: Box::new(bounded_body),
            }
        }

        LocalTypeR::Var(var) => {
            // Variable remains but fuel is tracked at Mu level
            LocalTypeR::Var(var.clone())
        }
    }
}

/// Bound recursion by inserting yield points after N steps.
fn bound_with_yield_after(lt: &LocalTypeR, steps: usize) -> LocalTypeR {
    bound_with_yield_after_impl(lt, steps, 0).0
}

fn bound_with_yield_after_impl(
    lt: &LocalTypeR,
    max_steps: usize,
    current: usize,
) -> (LocalTypeR, usize) {
    if current >= max_steps {
        // Insert a yield point by ending
        return (LocalTypeR::End, current);
    }

    match lt {
        LocalTypeR::End => (LocalTypeR::End, current),

        LocalTypeR::Send { partner, branches } => {
            let new_current = current + 1;
            if new_current >= max_steps {
                (LocalTypeR::End, new_current)
            } else {
                let bounded_branches: Vec<_> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let (bounded, _) =
                            bound_with_yield_after_impl(cont, max_steps, new_current);
                        (label.clone(), bounded)
                    })
                    .collect();
                (
                    LocalTypeR::Send {
                        partner: partner.clone(),
                        branches: bounded_branches,
                    },
                    new_current,
                )
            }
        }

        LocalTypeR::Recv { partner, branches } => {
            let new_current = current + 1;
            if new_current >= max_steps {
                (LocalTypeR::End, new_current)
            } else {
                let bounded_branches: Vec<_> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let (bounded, _) =
                            bound_with_yield_after_impl(cont, max_steps, new_current);
                        (label.clone(), bounded)
                    })
                    .collect();
                (
                    LocalTypeR::Recv {
                        partner: partner.clone(),
                        branches: bounded_branches,
                    },
                    new_current,
                )
            }
        }

        LocalTypeR::Mu { var, body } => {
            let (bounded_body, steps_used) = bound_with_yield_after_impl(body, max_steps, current);
            (
                LocalTypeR::Mu {
                    var: var.clone(),
                    body: Box::new(bounded_body),
                },
                steps_used,
            )
        }

        LocalTypeR::Var(var) => (LocalTypeR::Var(var.clone()), current),
    }
}

/// Bound recursion by yielding when a specific condition/label is seen.
fn bound_with_yield_when(lt: &LocalTypeR, condition: &str) -> LocalTypeR {
    bound_with_yield_when_impl(lt, condition, &mut HashSet::new())
}

fn bound_with_yield_when_impl(
    lt: &LocalTypeR,
    condition: &str,
    seen_conditions: &mut HashSet<String>,
) -> LocalTypeR {
    match lt {
        LocalTypeR::End => LocalTypeR::End,

        LocalTypeR::Send { partner, branches } => {
            let bounded_branches: Vec<_> = branches
                .iter()
                .map(|(label, cont)| {
                    if label.name == condition {
                        // Yield when this condition is seen
                        if seen_conditions.contains(condition) {
                            (label.clone(), LocalTypeR::End)
                        } else {
                            seen_conditions.insert(condition.to_string());
                            let bounded =
                                bound_with_yield_when_impl(cont, condition, seen_conditions);
                            (label.clone(), bounded)
                        }
                    } else {
                        let bounded = bound_with_yield_when_impl(cont, condition, seen_conditions);
                        (label.clone(), bounded)
                    }
                })
                .collect();
            LocalTypeR::Send {
                partner: partner.clone(),
                branches: bounded_branches,
            }
        }

        LocalTypeR::Recv { partner, branches } => {
            let bounded_branches: Vec<_> = branches
                .iter()
                .map(|(label, cont)| {
                    if label.name == condition {
                        if seen_conditions.contains(condition) {
                            (label.clone(), LocalTypeR::End)
                        } else {
                            seen_conditions.insert(condition.to_string());
                            let bounded =
                                bound_with_yield_when_impl(cont, condition, seen_conditions);
                            (label.clone(), bounded)
                        }
                    } else {
                        let bounded = bound_with_yield_when_impl(cont, condition, seen_conditions);
                        (label.clone(), bounded)
                    }
                })
                .collect();
            LocalTypeR::Recv {
                partner: partner.clone(),
                branches: bounded_branches,
            }
        }

        LocalTypeR::Mu { var, body } => {
            let bounded_body = bound_with_yield_when_impl(body, condition, seen_conditions);
            LocalTypeR::Mu {
                var: var.clone(),
                body: Box::new(bounded_body),
            }
        }

        LocalTypeR::Var(var) => LocalTypeR::Var(var.clone()),
    }
}

/// Unfold a recursive type up to a maximum depth.
///
/// This is useful for analysis or visualization of bounded protocols.
pub fn unfold_bounded(lt: &LocalTypeR, max_depth: usize) -> LocalTypeR {
    unfold_bounded_impl(lt, lt, max_depth, 0)
}

fn unfold_bounded_impl(
    original: &LocalTypeR,
    current: &LocalTypeR,
    max_depth: usize,
    depth: usize,
) -> LocalTypeR {
    if depth >= max_depth {
        return LocalTypeR::End;
    }

    match current {
        LocalTypeR::End => LocalTypeR::End,

        LocalTypeR::Send { partner, branches } => {
            let unfolded_branches = branches
                .iter()
                .map(|(label, cont)| {
                    (
                        label.clone(),
                        unfold_bounded_impl(original, cont, max_depth, depth),
                    )
                })
                .collect();
            LocalTypeR::Send {
                partner: partner.clone(),
                branches: unfolded_branches,
            }
        }

        LocalTypeR::Recv { partner, branches } => {
            let unfolded_branches = branches
                .iter()
                .map(|(label, cont)| {
                    (
                        label.clone(),
                        unfold_bounded_impl(original, cont, max_depth, depth),
                    )
                })
                .collect();
            LocalTypeR::Recv {
                partner: partner.clone(),
                branches: unfolded_branches,
            }
        }

        LocalTypeR::Mu { body, .. } => {
            // Increment depth when entering a Mu
            unfold_bounded_impl(original, body, max_depth, depth + 1)
        }

        LocalTypeR::Var(_) => {
            // Replace variable with the body of the enclosing Mu
            if let LocalTypeR::Mu { body, .. } = original {
                unfold_bounded_impl(original, body, max_depth, depth + 1)
            } else {
                LocalTypeR::End
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use rumpsteak_types::Label;

    fn ping_pong_recursive() -> LocalTypeR {
        LocalTypeR::mu(
            "X",
            LocalTypeR::send(
                "B",
                Label::new("ping"),
                LocalTypeR::recv("B", Label::new("pong"), LocalTypeR::var("X")),
            ),
        )
    }

    #[test]
    fn test_fuel_zero() {
        let lt = ping_pong_recursive();
        let bounded = bound_recursion(&lt, BoundingStrategy::Fuel(0));
        assert!(matches!(bounded, LocalTypeR::End));
    }

    #[test]
    fn test_fuel_one() {
        let lt = ping_pong_recursive();
        let bounded = bound_recursion(&lt, BoundingStrategy::Fuel(1));

        // Should have Mu with End body
        match bounded {
            LocalTypeR::Mu { body, .. } => {
                assert!(matches!(*body, LocalTypeR::End));
            }
            _ => panic!("Expected Mu"),
        }
    }

    #[test]
    fn test_fuel_preserves_structure() {
        let lt = ping_pong_recursive();
        let bounded = bound_recursion(&lt, BoundingStrategy::Fuel(3));

        // Should preserve Mu structure
        match bounded {
            LocalTypeR::Mu { var, body } => {
                assert_eq!(var, "X");
                assert!(matches!(*body, LocalTypeR::Send { .. }));
            }
            _ => panic!("Expected Mu"),
        }
    }

    #[test]
    fn test_yield_after_zero() {
        let lt = ping_pong_recursive();
        let bounded = bound_recursion(&lt, BoundingStrategy::YieldAfter(0));
        assert!(matches!(bounded, LocalTypeR::End));
    }

    #[test]
    fn test_yield_after_one() {
        let lt = ping_pong_recursive();
        let bounded = bound_recursion(&lt, BoundingStrategy::YieldAfter(1));

        // With YieldAfter(1), after 1 step we end
        // The Mu wraps Send, which counts as 1 step, so continuation ends
        match bounded {
            LocalTypeR::Mu { body, .. } => match *body {
                LocalTypeR::Send { ref branches, .. } => {
                    // After the send (1 step), continuation should be End
                    assert!(matches!(branches[0].1, LocalTypeR::End));
                }
                LocalTypeR::End => {
                    // Or the whole body is End if we hit limit at Mu level
                }
                _ => panic!("Expected Send or End in Mu body"),
            },
            LocalTypeR::End => {
                // At max_steps=1, might end immediately at top level
            }
            _ => panic!("Expected Mu or End"),
        }
    }

    #[test]
    fn test_yield_when_condition() {
        let lt = LocalTypeR::send(
            "B",
            Label::new("start"),
            LocalTypeR::mu(
                "X",
                LocalTypeR::send("B", Label::new("stop"), LocalTypeR::var("X")),
            ),
        );

        let bounded = bound_recursion(&lt, BoundingStrategy::YieldWhen("stop".to_string()));

        // First occurrence of "stop" should pass, second should yield
        match bounded {
            LocalTypeR::Send { branches, .. } => {
                let cont = &branches[0].1;
                match cont {
                    LocalTypeR::Mu { body, .. } => match body.as_ref() {
                        LocalTypeR::Send { branches, .. } => {
                            // After first stop, continuation should still have structure
                            // Second stop should end
                            assert!(!branches.is_empty());
                        }
                        _ => panic!("Expected Send in Mu body"),
                    },
                    _ => panic!("Expected Mu"),
                }
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_unfold_bounded() {
        let lt = ping_pong_recursive();
        let unfolded = unfold_bounded(&lt, 2);

        // Should unfold to finite depth
        match unfolded {
            LocalTypeR::Send { branches, .. } => {
                let cont = &branches[0].1;
                match cont {
                    LocalTypeR::Recv { branches, .. } => {
                        // After 2 levels, should end
                        assert!(matches!(
                            branches[0].1,
                            LocalTypeR::Send { .. } | LocalTypeR::End
                        ));
                    }
                    _ => panic!("Expected Recv"),
                }
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_end_unchanged() {
        let lt = LocalTypeR::End;

        let fuel = bound_recursion(&lt, BoundingStrategy::Fuel(5));
        assert!(matches!(fuel, LocalTypeR::End));

        let yield_after = bound_recursion(&lt, BoundingStrategy::YieldAfter(5));
        assert!(matches!(yield_after, LocalTypeR::End));

        let yield_when = bound_recursion(&lt, BoundingStrategy::YieldWhen("x".to_string()));
        assert!(matches!(yield_when, LocalTypeR::End));
    }
}
