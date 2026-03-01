//! Async Step Semantics for Session Types
//!
//! This module implements the operational semantics for global and local types
//! from the ECOOP 2025 paper "Mechanised Subject Reduction for Multiparty
//! Asynchronous Session Types".
//!
//! # Key Concepts
//!
//! - **Async Semantics**: Messages can be reordered as long as they don't involve
//!   the same receiver. This models asynchronous communication channels.
//! - **Enabledness (`can_step`)**: Whether an action is available in a type
//! - **Step Relation (`step`)**: How types evolve after performing actions
//! - **Consume**: Extract continuation after a communication
//!
//! # Lean Correspondence
//!
//! This module mirrors `lean/SessionTypes/GlobalType.lean`:
//! - `GlobalAction` ↔ Lean's `GlobalActionR`
//! - `LocalAction` ↔ Lean's `LocalActionR`
//! - `can_step` ↔ Lean's `canStep` inductive
//! - `step` ↔ Lean's `step` inductive
//! - `ConsumeResult` ↔ Lean's `ConsumeResult` inductive

use crate::limits::{TraversalFuel, DEFAULT_TRAVERSAL_FUEL};
use telltale_types::{GlobalType, Label, LocalTypeR};

#[path = "semantics_reduction.rs"]
mod reduction;
#[cfg(test)]
mod tests {
    include!("../tests/unit/semantics_tests.rs");
}

pub use reduction::{
    good_g, good_g_with_fuel, reduces, reduces_star, reduces_star_with_fuel, reduces_with_fuel,
};

/// Direction of a local action (send or receive).
///
/// Corresponds to Lean's `LocalKind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocalKind {
    /// Sending a message
    Send,
    /// Receiving a message
    Recv,
}

/// A global action representing a communication between two roles.
///
/// Corresponds to Lean's `GlobalActionR`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GlobalAction {
    /// The role sending the message
    pub sender: String,
    /// The role receiving the message
    pub receiver: String,
    /// The message label
    pub label: Label,
}

impl GlobalAction {
    /// Create a new global action
    #[must_use]
    pub fn new(sender: impl Into<String>, receiver: impl Into<String>, label: Label) -> Self {
        GlobalAction {
            sender: sender.into(),
            receiver: receiver.into(),
            label,
        }
    }
}

/// A local action from a single role's perspective.
///
/// Corresponds to Lean's `LocalActionR`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LocalAction {
    /// Whether this is a send or receive
    pub kind: LocalKind,
    /// The communication partner
    pub partner: String,
    /// The message label
    pub label: Label,
}

impl LocalAction {
    /// Create a send action
    #[must_use]
    pub fn send(partner: impl Into<String>, label: Label) -> Self {
        LocalAction {
            kind: LocalKind::Send,
            partner: partner.into(),
            label,
        }
    }

    /// Create a receive action
    #[must_use]
    pub fn recv(partner: impl Into<String>, label: Label) -> Self {
        LocalAction {
            kind: LocalKind::Recv,
            partner: partner.into(),
            label,
        }
    }

    /// Convert a local action to a global action given the acting role.
    #[must_use]
    pub fn to_global(&self, role: &str) -> GlobalAction {
        match self.kind {
            LocalKind::Send => GlobalAction::new(role, &self.partner, self.label.clone()),
            LocalKind::Recv => GlobalAction::new(&self.partner, role, self.label.clone()),
        }
    }
}

/// Check if an action is enabled in a global type (async semantics).
///
/// This implements the `canStep` predicate from the Lean specification.
/// An action is enabled if:
/// - It matches the head communication directly (`comm_head`)
/// - It can be performed after skipping an unrelated head (`comm_async`)
/// - The type is a μ and the action is enabled after unfolding (`mu`)
///
/// # Async Semantics
///
/// The key insight is `comm_async`: action `act` can skip communication
/// `sender → receiver` if:
/// - `act.sender ≠ receiver` (act's sender is not the receiver of the head)
/// - `act.receiver ≠ receiver` (act's receiver is not the receiver of the head)
///
/// This models asynchronous message passing where messages to different
/// receivers can be reordered.
///
/// # Examples
///
/// ```
/// use telltale_theory::semantics::{can_step, GlobalAction};
/// use telltale_types::{GlobalType, Label};
///
/// // A -> B: msg. end
/// let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
/// let act = GlobalAction::new("A", "B", Label::new("msg"));
/// assert!(can_step(&g, &act));
///
/// // Different action is not enabled
/// let wrong = GlobalAction::new("B", "A", Label::new("msg"));
/// assert!(!can_step(&g, &wrong));
/// ```
#[must_use]
pub fn can_step(global: &GlobalType, action: &GlobalAction) -> bool {
    can_step_with_fuel(global, action, DEFAULT_TRAVERSAL_FUEL)
}

/// Fuel-bounded can-step check for deep recursive protocols.
#[must_use]
pub fn can_step_with_fuel(global: &GlobalType, action: &GlobalAction, fuel: TraversalFuel) -> bool {
    can_step_fuel(global, action, fuel.as_usize())
}

/// Fuel-bounded version of can_step for termination.
fn can_step_fuel(g: &GlobalType, act: &GlobalAction, fuel: usize) -> bool {
    if fuel == 0 {
        return false;
    }

    match g {
        GlobalType::End => false,
        GlobalType::Var(_) => false,
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            // comm_head: direct match at head position
            if sender == &act.sender
                && receiver == &act.receiver
                && branches.iter().any(|(l, _)| l == &act.label)
            {
                return true;
            }

            // comm_async: skip this communication if unrelated to receiver
            // act.sender ≠ receiver AND act.receiver ≠ receiver
            if act.sender != *receiver && act.receiver != *receiver {
                // Check if any branch continuation enables the action
                for (_, cont) in branches {
                    if can_step_fuel(cont, act, fuel - 1) {
                        return true;
                    }
                }
            }

            false
        }
        GlobalType::Mu { var, body } => {
            // Unfold and check
            let unfolded = body.substitute(var, g);
            can_step_fuel(&unfolded, act, fuel - 1)
        }
    }
}

/// Perform an async step on a global type.
///
/// This implements the `step` relation from the Lean specification.
/// Returns the resulting global type after the action is performed.
///
/// # Rules
///
/// - `comm_head`: If action matches head, return the continuation
/// - `comm_async`: If action can skip head, step all branches and wrap
/// - `mu`: Unfold and step
///
/// # Examples
///
/// ```
/// use telltale_theory::semantics::{step, GlobalAction};
/// use telltale_types::{GlobalType, Label};
///
/// // A -> B: msg. end  --[A,B,msg]--> end
/// let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
/// let act = GlobalAction::new("A", "B", Label::new("msg"));
/// assert_eq!(step(&g, &act), Some(GlobalType::End));
/// ```
#[must_use]
pub fn step(global: &GlobalType, action: &GlobalAction) -> Option<GlobalType> {
    step_with_fuel(global, action, DEFAULT_TRAVERSAL_FUEL)
}

/// Fuel-bounded step for deep recursive protocols.
#[must_use]
pub fn step_with_fuel(
    global: &GlobalType,
    action: &GlobalAction,
    fuel: TraversalFuel,
) -> Option<GlobalType> {
    step_fuel(global, action, fuel.as_usize())
}

/// Fuel-bounded version of step for termination.
fn step_fuel(g: &GlobalType, act: &GlobalAction, fuel: usize) -> Option<GlobalType> {
    if fuel == 0 {
        return None;
    }

    match g {
        GlobalType::End => None,
        GlobalType::Var(_) => None,
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            // comm_head: direct match at head position
            if sender == &act.sender && receiver == &act.receiver {
                for (l, cont) in branches {
                    if l == &act.label {
                        return Some(cont.clone());
                    }
                }
            }

            // comm_async: skip this communication if unrelated to receiver
            if act.sender != *receiver && act.receiver != *receiver {
                // First check if action is enabled in some continuation
                let enabled = branches
                    .iter()
                    .any(|(_, cont)| can_step_fuel(cont, act, fuel - 1));

                if enabled {
                    // Step all branches
                    let mut new_branches = Vec::with_capacity(branches.len());
                    for (l, cont) in branches {
                        if let Some(stepped) = step_fuel(cont, act, fuel - 1) {
                            new_branches.push((l.clone(), stepped));
                        } else {
                            // If any branch can't step, the whole step fails
                            return None;
                        }
                    }
                    return Some(GlobalType::Comm {
                        sender: sender.clone(),
                        receiver: receiver.clone(),
                        branches: new_branches,
                    });
                }
            }

            None
        }
        GlobalType::Mu { var, body } => {
            // Unfold and step
            let unfolded = body.substitute(var, g);
            step_fuel(&unfolded, act, fuel - 1)
        }
    }
}

/// Check if a local type can perform an action (async semantics).
///
/// This implements local enabledness from the Lean specification.
/// Corresponds to Lean's `canStep` for `LocalTypeR`.
///
/// # Rules
///
/// - `send_head`: Direct send at head
/// - `recv_head`: Direct recv at head
/// - `send_async`: Skip send if partner differs (async reordering)
/// - `mu`: Unfold and check
///
/// # Examples
///
/// ```
/// use telltale_theory::semantics::{local_can_step, LocalAction};
/// use telltale_types::{LocalTypeR, Label};
///
/// // !B{msg.end}
/// let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let act = LocalAction::send("B", Label::new("msg"));
/// assert!(local_can_step(&lt, &act));
/// ```
#[must_use]
pub fn local_can_step(local: &LocalTypeR, action: &LocalAction) -> bool {
    local_can_step_with_fuel(local, action, DEFAULT_TRAVERSAL_FUEL)
}

/// Fuel-bounded local can-step check.
#[must_use]
pub fn local_can_step_with_fuel(
    local: &LocalTypeR,
    action: &LocalAction,
    fuel: TraversalFuel,
) -> bool {
    local_can_step_fuel(local, action, fuel.as_usize())
}

/// Fuel-bounded version of local_can_step for termination.
fn local_can_step_fuel(lt: &LocalTypeR, act: &LocalAction, fuel: usize) -> bool {
    if fuel == 0 {
        return false;
    }

    match lt {
        LocalTypeR::End => false,
        LocalTypeR::Var(_) => false,
        LocalTypeR::Send { partner, branches } => {
            if act.kind == LocalKind::Send {
                // send_head: direct match
                if partner == &act.partner && branches.iter().any(|(l, _vt, _)| l == &act.label) {
                    return true;
                }

                // send_async: skip if different partner
                if act.partner != *partner {
                    for (_l, _vt, cont) in branches {
                        if local_can_step_fuel(cont, act, fuel - 1) {
                            return true;
                        }
                    }
                }
            }
            false
        }
        LocalTypeR::Recv { partner, branches } => {
            // recv_head: direct match
            if act.kind == LocalKind::Recv
                && partner == &act.partner
                && branches.iter().any(|(l, _vt, _)| l == &act.label)
            {
                return true;
            }
            // Note: recv blocks - no async skip through recv
            false
        }
        LocalTypeR::Mu { var, body } => {
            // Unfold and check
            let unfolded = body.substitute(var, lt);
            local_can_step_fuel(&unfolded, act, fuel - 1)
        }
    }
}

/// Perform an async step on a local type.
///
/// Returns the resulting local type after the action is performed.
#[must_use]
pub fn local_step(local: &LocalTypeR, action: &LocalAction) -> Option<LocalTypeR> {
    local_step_with_fuel(local, action, DEFAULT_TRAVERSAL_FUEL)
}

/// Fuel-bounded local step.
#[must_use]
pub fn local_step_with_fuel(
    local: &LocalTypeR,
    action: &LocalAction,
    fuel: TraversalFuel,
) -> Option<LocalTypeR> {
    local_step_fuel(local, action, fuel.as_usize())
}

/// Fuel-bounded version of local_step for termination.
fn local_step_fuel(lt: &LocalTypeR, act: &LocalAction, fuel: usize) -> Option<LocalTypeR> {
    if fuel == 0 {
        return None;
    }

    match lt {
        LocalTypeR::End | LocalTypeR::Var(_) => None,
        LocalTypeR::Send { partner, branches } => {
            if act.kind == LocalKind::Send {
                if partner == &act.partner {
                    for (l, _vt, cont) in branches {
                        if l == &act.label {
                            return Some(cont.clone());
                        }
                    }
                }

                if act.partner != *partner {
                    let enabled = branches
                        .iter()
                        .any(|(_l, _vt, cont)| local_can_step_fuel(cont, act, fuel - 1));

                    if enabled {
                        let mut new_branches = Vec::with_capacity(branches.len());
                        for (l, vt, cont) in branches {
                            if let Some(stepped) = local_step_fuel(cont, act, fuel - 1) {
                                new_branches.push((l.clone(), vt.clone(), stepped));
                            } else {
                                return None;
                            }
                        }
                        return Some(LocalTypeR::Send {
                            partner: partner.clone(),
                            branches: new_branches,
                        });
                    }
                }
            }
            None
        }
        LocalTypeR::Recv { partner, branches } => {
            if act.kind == LocalKind::Recv && partner == &act.partner {
                for (l, _vt, cont) in branches {
                    if l == &act.label {
                        return Some(cont.clone());
                    }
                }
            }
            None
        }
        LocalTypeR::Mu { var, body } => {
            let unfolded = body.substitute(var, lt);
            local_step_fuel(&unfolded, act, fuel - 1)
        }
    }
}

/// Result of consuming a communication from a global type.
///
/// This corresponds to Lean's `ConsumeResult` inductive relation.
/// It represents the well-founded proof that consumption succeeds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConsumeResult {
    /// Direct consumption: communication at head matched
    Comm {
        sender: String,
        receiver: String,
        label: Label,
        continuation: GlobalType,
    },
    /// Consumption after μ-unfolding
    Mu {
        var: String,
        body: Box<GlobalType>,
        inner: Box<ConsumeResult>,
    },
}

impl ConsumeResult {
    /// Extract the final continuation from a consume result
    #[must_use]
    pub fn continuation(&self) -> &GlobalType {
        match self {
            ConsumeResult::Comm { continuation, .. } => continuation,
            ConsumeResult::Mu { inner, .. } => inner.continuation(),
        }
    }
}

/// Consume a communication from a global type, returning a proof.
///
/// This is the constructive version of `GlobalType::consume` that returns
/// a `ConsumeResult` proof structure.
///
/// Corresponds to Lean's `ConsumeResult` relation.
#[must_use]
pub fn consume_with_proof(
    global: &GlobalType,
    sender: &str,
    receiver: &str,
    label: &Label,
) -> Option<ConsumeResult> {
    consume_with_proof_with_fuel(global, sender, receiver, label, DEFAULT_TRAVERSAL_FUEL)
}

/// Fuel-bounded constructive consume relation.
#[must_use]
pub fn consume_with_proof_with_fuel(
    global: &GlobalType,
    sender: &str,
    receiver: &str,
    label: &Label,
    fuel: TraversalFuel,
) -> Option<ConsumeResult> {
    consume_with_proof_fuel(global, sender, receiver, label, fuel.as_usize())
}

fn consume_with_proof_fuel(
    g: &GlobalType,
    sender: &str,
    receiver: &str,
    label: &Label,
    fuel: usize,
) -> Option<ConsumeResult> {
    if fuel == 0 {
        return None;
    }

    match g {
        GlobalType::Comm {
            sender: s,
            receiver: r,
            branches,
        } => {
            if s == sender && r == receiver {
                for (l, cont) in branches {
                    if l == label {
                        return Some(ConsumeResult::Comm {
                            sender: sender.to_string(),
                            receiver: receiver.to_string(),
                            label: label.clone(),
                            continuation: cont.clone(),
                        });
                    }
                }
            }
            None
        }
        GlobalType::Mu { var, body } => {
            let unfolded = body.substitute(var, g);
            let inner = consume_with_proof_fuel(&unfolded, sender, receiver, label, fuel - 1)?;
            Some(ConsumeResult::Mu {
                var: var.clone(),
                body: body.clone(),
                inner: Box::new(inner),
            })
        }
        _ => None,
    }
}
