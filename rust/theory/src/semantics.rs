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
//! This module mirrors `lean/Rumpsteak/Protocol/GlobalType.lean`:
//! - `GlobalAction` ↔ Lean's `GlobalActionR`
//! - `LocalAction` ↔ Lean's `LocalActionR`
//! - `can_step` ↔ Lean's `canStep` inductive
//! - `step` ↔ Lean's `step` inductive
//! - `ConsumeResult` ↔ Lean's `ConsumeResult` inductive

use rumpsteak_types::{GlobalType, Label, LocalTypeR};
use std::collections::HashSet;

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
/// use rumpsteak_theory::semantics::{can_step, GlobalAction};
/// use rumpsteak_types::{GlobalType, Label};
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
pub fn can_step(g: &GlobalType, act: &GlobalAction) -> bool {
    can_step_fuel(g, act, 100)
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
            if sender == &act.sender && receiver == &act.receiver {
                if branches
                    .iter()
                    .any(|(l, _)| l.name == act.label.name)
                {
                    return true;
                }
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
/// use rumpsteak_theory::semantics::{step, GlobalAction};
/// use rumpsteak_types::{GlobalType, Label};
///
/// // A -> B: msg. end  --[A,B,msg]--> end
/// let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
/// let act = GlobalAction::new("A", "B", Label::new("msg"));
/// assert_eq!(step(&g, &act), Some(GlobalType::End));
/// ```
#[must_use]
pub fn step(g: &GlobalType, act: &GlobalAction) -> Option<GlobalType> {
    step_fuel(g, act, 100)
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
                    if l.name == act.label.name {
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
/// use rumpsteak_theory::semantics::{local_can_step, LocalAction};
/// use rumpsteak_types::{LocalTypeR, Label};
///
/// // !B{msg.end}
/// let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let act = LocalAction::send("B", Label::new("msg"));
/// assert!(local_can_step(&lt, &act));
/// ```
#[must_use]
pub fn local_can_step(lt: &LocalTypeR, act: &LocalAction) -> bool {
    local_can_step_fuel(lt, act, 100)
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
                if partner == &act.partner {
                    if branches
                        .iter()
                        .any(|(l, _)| l.name == act.label.name)
                    {
                        return true;
                    }
                }

                // send_async: skip if different partner
                if act.partner != *partner {
                    for (_, cont) in branches {
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
            if act.kind == LocalKind::Recv && partner == &act.partner {
                if branches
                    .iter()
                    .any(|(l, _)| l.name == act.label.name)
                {
                    return true;
                }
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
pub fn local_step(lt: &LocalTypeR, act: &LocalAction) -> Option<LocalTypeR> {
    local_step_fuel(lt, act, 100)
}

/// Fuel-bounded version of local_step for termination.
fn local_step_fuel(lt: &LocalTypeR, act: &LocalAction, fuel: usize) -> Option<LocalTypeR> {
    if fuel == 0 {
        return None;
    }

    match lt {
        LocalTypeR::End => None,
        LocalTypeR::Var(_) => None,
        LocalTypeR::Send { partner, branches } => {
            if act.kind == LocalKind::Send {
                // send_head: direct match
                if partner == &act.partner {
                    for (l, cont) in branches {
                        if l.name == act.label.name {
                            return Some(cont.clone());
                        }
                    }
                }

                // send_async: skip if different partner
                if act.partner != *partner {
                    let enabled = branches
                        .iter()
                        .any(|(_, cont)| local_can_step_fuel(cont, act, fuel - 1));

                    if enabled {
                        let mut new_branches = Vec::with_capacity(branches.len());
                        for (l, cont) in branches {
                            if let Some(stepped) = local_step_fuel(cont, act, fuel - 1) {
                                new_branches.push((l.clone(), stepped));
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
            // recv_head: direct match only (recv blocks)
            if act.kind == LocalKind::Recv && partner == &act.partner {
                for (l, cont) in branches {
                    if l.name == act.label.name {
                        return Some(cont.clone());
                    }
                }
            }
            None
        }
        LocalTypeR::Mu { var, body } => {
            // Unfold and step
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
    g: &GlobalType,
    sender: &str,
    receiver: &str,
    label: &Label,
) -> Option<ConsumeResult> {
    consume_with_proof_fuel(g, sender, receiver, label, 100)
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
                    if l.name == label.name {
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

/// Check if a global type reduces to another via one communication.
///
/// Corresponds to Lean's `GlobalTypeReduces` relation.
/// G ⟹ G' means G can reduce to G' by performing one communication.
#[must_use]
pub fn reduces(g: &GlobalType, g_prime: &GlobalType) -> bool {
    reduces_fuel(g, g_prime, 100)
}

fn reduces_fuel(g: &GlobalType, g_prime: &GlobalType, fuel: usize) -> bool {
    if fuel == 0 {
        return false;
    }

    match g {
        GlobalType::Comm { branches, .. } => {
            // Direct reduction: g_prime is one of the continuations
            for (_, cont) in branches {
                if cont == g_prime {
                    return true;
                }
            }
            false
        }
        GlobalType::Mu { var, body } => {
            // Reduce under μ-unfolding
            let unfolded = body.substitute(var, g);
            reduces_fuel(&unfolded, g_prime, fuel - 1)
        }
        _ => false,
    }
}

/// Check if g reduces to g_prime in zero or more steps.
///
/// Corresponds to Lean's `GlobalTypeReducesStar`.
#[must_use]
pub fn reduces_star(g: &GlobalType, g_prime: &GlobalType) -> bool {
    reduces_star_fuel(g, g_prime, 100, &mut HashSet::new())
}

fn reduces_star_fuel(
    g: &GlobalType,
    g_prime: &GlobalType,
    fuel: usize,
    visited: &mut HashSet<GlobalType>,
) -> bool {
    if fuel == 0 {
        return false;
    }

    // Reflexive case
    if g == g_prime {
        return true;
    }

    // Avoid cycles
    if visited.contains(g) {
        return false;
    }
    visited.insert(g.clone());

    // Try all possible one-step reductions
    match g {
        GlobalType::Comm { branches, .. } => {
            for (_, cont) in branches {
                if reduces_star_fuel(cont, g_prime, fuel - 1, visited) {
                    return true;
                }
            }
            false
        }
        GlobalType::Mu { var, body } => {
            let unfolded = body.substitute(var, g);
            reduces_star_fuel(&unfolded, g_prime, fuel - 1, visited)
        }
        _ => false,
    }
}

/// Check if an action is enabled implies a step exists.
///
/// This is the "good global" condition from the ECOOP 2025 paper.
/// For well-formed types, if `can_step(g, act)` then `step(g, act).is_some()`.
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
        GlobalType::Mu { var, body } => {
            // Check the unfolded type
            let unfolded = body.substitute(var, g);
            good_g_fuel(&unfolded, fuel - 1, visited)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_can_step_head() {
        // A -> B: msg. end
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let act = GlobalAction::new("A", "B", Label::new("msg"));
        assert!(can_step(&g, &act));
    }

    #[test]
    fn test_can_step_wrong_action() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let wrong = GlobalAction::new("B", "A", Label::new("msg"));
        assert!(!can_step(&g, &wrong));
    }

    #[test]
    fn test_can_step_wrong_label() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let wrong = GlobalAction::new("A", "B", Label::new("other"));
        assert!(!can_step(&g, &wrong));
    }

    #[test]
    fn test_can_step_async() {
        // A -> B: m1. (C -> D: m2. end)
        // Action C -> D can skip A -> B since D ≠ B
        let inner = GlobalType::send("C", "D", Label::new("m2"), GlobalType::End);
        let g = GlobalType::send("A", "B", Label::new("m1"), inner);

        let act = GlobalAction::new("C", "D", Label::new("m2"));
        assert!(can_step(&g, &act));
    }

    #[test]
    fn test_can_step_async_blocked() {
        // A -> B: m1. (C -> B: m2. end)
        // Action C -> B CANNOT skip A -> B since B == B (receiver conflict)
        let inner = GlobalType::send("C", "B", Label::new("m2"), GlobalType::End);
        let g = GlobalType::send("A", "B", Label::new("m1"), inner);

        let act = GlobalAction::new("C", "B", Label::new("m2"));
        assert!(!can_step(&g, &act));
    }

    #[test]
    fn test_can_step_mu() {
        // μt. A -> B: msg. t
        let g = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );
        let act = GlobalAction::new("A", "B", Label::new("msg"));
        assert!(can_step(&g, &act));
    }

    #[test]
    fn test_step_head() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let act = GlobalAction::new("A", "B", Label::new("msg"));
        assert_eq!(step(&g, &act), Some(GlobalType::End));
    }

    #[test]
    fn test_step_async() {
        // A -> B: m1. (C -> D: m2. end)
        // Step C -> D results in: A -> B: m1. end
        let inner = GlobalType::send("C", "D", Label::new("m2"), GlobalType::End);
        let g = GlobalType::send("A", "B", Label::new("m1"), inner);

        let act = GlobalAction::new("C", "D", Label::new("m2"));
        let result = step(&g, &act);

        let expected = GlobalType::send("A", "B", Label::new("m1"), GlobalType::End);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn test_step_mu() {
        let g = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );
        let act = GlobalAction::new("A", "B", Label::new("msg"));
        let result = step(&g, &act);

        // Result should be the recursive type again
        assert_eq!(result, Some(g));
    }

    #[test]
    fn test_local_can_step_send() {
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let act = LocalAction::send("B", Label::new("msg"));
        assert!(local_can_step(&lt, &act));
    }

    #[test]
    fn test_local_can_step_recv() {
        let lt = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);
        let act = LocalAction::recv("A", Label::new("msg"));
        assert!(local_can_step(&lt, &act));
    }

    #[test]
    fn test_local_can_step_async() {
        // !B{m1. !C{m2. end}}
        // Action !C{m2} can skip !B{m1} since C ≠ B
        let inner = LocalTypeR::send("C", Label::new("m2"), LocalTypeR::End);
        let lt = LocalTypeR::send("B", Label::new("m1"), inner);

        let act = LocalAction::send("C", Label::new("m2"));
        assert!(local_can_step(&lt, &act));
    }

    #[test]
    fn test_local_step_send() {
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let act = LocalAction::send("B", Label::new("msg"));
        assert_eq!(local_step(&lt, &act), Some(LocalTypeR::End));
    }

    #[test]
    fn test_consume_with_proof() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let result = consume_with_proof(&g, "A", "B", &Label::new("msg"));

        assert!(result.is_some());
        let proof = result.unwrap();
        assert_eq!(proof.continuation(), &GlobalType::End);
    }

    #[test]
    fn test_reduces() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        assert!(reduces(&g, &GlobalType::End));
    }

    #[test]
    fn test_reduces_star() {
        let g1 = GlobalType::send(
            "A",
            "B",
            Label::new("m1"),
            GlobalType::send("B", "C", Label::new("m2"), GlobalType::End),
        );
        assert!(reduces_star(&g1, &GlobalType::End));
    }

    #[test]
    fn test_good_g() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        assert!(good_g(&g));
    }

    #[test]
    fn test_local_action_to_global() {
        let act = LocalAction::send("B", Label::new("msg"));
        let global = act.to_global("A");
        assert_eq!(global.sender, "A");
        assert_eq!(global.receiver, "B");
    }
}
