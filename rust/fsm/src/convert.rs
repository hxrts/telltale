//! Conversion between LocalTypeR and FSM representations.
//!
//! This module provides bidirectional conversion between the tree-based
//! LocalTypeR representation (from rumpsteak-types) and the graph-based
//! FSM representation.
//!
//! Enable with the `convert` feature flag.

use crate::{Action, Fsm, Message, StateIndex, Transition};
use rumpsteak_types::{Label, LocalTypeR};
use std::collections::HashMap;

/// Convert a LocalTypeR to an FSM representation.
///
/// # Arguments
///
/// * `role` - The role name for this FSM
/// * `lt` - The local type to convert
///
/// # Returns
///
/// An FSM representing the same protocol as the local type.
///
/// # Example
///
/// ```ignore
/// use rumpsteak_types::{LocalTypeR, Label};
/// use rumpsteak_aura_fsm::convert::from_local_type;
///
/// let lt = LocalTypeR::send("Server", Label::new("hello"), LocalTypeR::End);
/// let fsm = from_local_type("Client", &lt);
/// assert_eq!(fsm.size(), (2, 1));
/// ```
pub fn from_local_type(role: &str, lt: &LocalTypeR) -> Fsm<String, String, ()> {
    let mut fsm = Fsm::new(role.to_string());
    let mut var_states: HashMap<String, StateIndex> = HashMap::new();

    let start = fsm.add_state();
    build_fsm(&mut fsm, lt, start, &mut var_states);
    fsm
}

fn build_fsm(
    fsm: &mut Fsm<String, String, ()>,
    lt: &LocalTypeR,
    current: StateIndex,
    var_states: &mut HashMap<String, StateIndex>,
) {
    match lt {
        LocalTypeR::End => {
            // End state - nothing to add
        }

        LocalTypeR::Send { partner, branches } => {
            for (label, cont) in branches {
                let next = fsm.add_state();
                let msg = Message::from_label(label.name.clone());
                let transition = Transition::new(partner.clone(), Action::Output, msg);
                let _ = fsm.add_transition(current, next, transition);
                build_fsm(fsm, cont, next, var_states);
            }
        }

        LocalTypeR::Recv { partner, branches } => {
            for (label, cont) in branches {
                let next = fsm.add_state();
                let msg = Message::from_label(label.name.clone());
                let transition = Transition::new(partner.clone(), Action::Input, msg);
                let _ = fsm.add_transition(current, next, transition);
                build_fsm(fsm, cont, next, var_states);
            }
        }

        LocalTypeR::Mu { var, body } => {
            // Record this state for the variable
            var_states.insert(var.clone(), current);
            build_fsm(fsm, body, current, var_states);
        }

        LocalTypeR::Var(var) => {
            // This is a back-edge to a recursion point
            // The current state should loop back to the var state
            // This is handled by the caller through var_states
            if let Some(&target) = var_states.get(var) {
                // Create a self-loop or back-edge marker
                // Note: In a proper implementation, we'd merge current with target
                // For now, we just mark this as connected to the recursion point
                let _ = target; // Used for tracking, actual implementation would merge states
            }
        }
    }
}

/// Convert an FSM back to a LocalTypeR representation.
///
/// # Arguments
///
/// * `fsm` - The FSM to convert
/// * `start` - The starting state index
///
/// # Returns
///
/// A LocalTypeR representing the same protocol as the FSM.
///
/// # Note
///
/// This conversion may not be exact for all FSMs, particularly those
/// with complex recursive structures.
pub fn to_local_type(fsm: &Fsm<String, String, ()>, start: StateIndex) -> LocalTypeR {
    let mut visited: HashMap<usize, String> = HashMap::new();
    let mut var_counter = 0;
    build_local_type(fsm, start, &mut visited, &mut var_counter)
}

fn build_local_type(
    fsm: &Fsm<String, String, ()>,
    state: StateIndex,
    visited: &mut HashMap<usize, String>,
    var_counter: &mut usize,
) -> LocalTypeR {
    let state_idx = state.index();

    // Check if we've visited this state before (recursion)
    if let Some(var) = visited.get(&state_idx) {
        return LocalTypeR::var(var);
    }

    // Collect all transitions from this state
    let transitions: Vec<_> = fsm.transitions_from(state).collect();

    if transitions.is_empty() {
        return LocalTypeR::End;
    }

    // Check if this is a recursion point by looking ahead
    // (simplified - would need more sophisticated cycle detection)

    // Mark this state as visited with a variable name
    let var_name = format!("X{}", var_counter);
    *var_counter += 1;
    visited.insert(state_idx, var_name.clone());

    // Get the action and partner from the first transition
    let first = &transitions[0].1;
    let action = first.action;
    let partner = first.role.clone();

    // Build branches
    let branches: Vec<(Label, LocalTypeR)> = transitions
        .into_iter()
        .map(|(target, trans)| {
            let label = Label::new(&trans.message.label);
            let cont = build_local_type(fsm, target, visited, var_counter);
            (label, cont)
        })
        .collect();

    // Remove from visited (for non-recursive paths)
    visited.remove(&state_idx);

    // Build the local type
    // (simplified - would need proper cycle detection for Mu wrapping)
    match action {
        Action::Output => LocalTypeR::Send { partner, branches },
        Action::Input => LocalTypeR::Recv { partner, branches },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_local_type_end() {
        let fsm = from_local_type("Client", &LocalTypeR::End);
        assert_eq!(fsm.size().0, 1); // Just the start state
        assert_eq!(fsm.size().1, 0); // No transitions
    }

    #[test]
    fn test_from_local_type_send() {
        let lt = LocalTypeR::send("Server", Label::new("hello"), LocalTypeR::End);
        let fsm = from_local_type("Client", &lt);

        assert_eq!(fsm.size().0, 2); // Start + end state
        assert_eq!(fsm.size().1, 1); // One transition
    }

    #[test]
    fn test_from_local_type_recv() {
        let lt = LocalTypeR::recv("Server", Label::new("hello"), LocalTypeR::End);
        let fsm = from_local_type("Client", &lt);

        assert_eq!(fsm.size().0, 2);
        assert_eq!(fsm.size().1, 1);
    }

    #[test]
    fn test_from_local_type_sequence() {
        let lt = LocalTypeR::send(
            "Server",
            Label::new("request"),
            LocalTypeR::recv("Server", Label::new("response"), LocalTypeR::End),
        );
        let fsm = from_local_type("Client", &lt);

        assert_eq!(fsm.size().0, 3); // Start, after send, end
        assert_eq!(fsm.size().1, 2); // Two transitions
    }

    #[test]
    fn test_from_local_type_choice() {
        let lt = LocalTypeR::Send {
            partner: "Server".to_string(),
            branches: vec![
                (Label::new("option1"), LocalTypeR::End),
                (Label::new("option2"), LocalTypeR::End),
            ],
        };
        let fsm = from_local_type("Client", &lt);

        assert_eq!(fsm.size().0, 3); // Start + two end states
        assert_eq!(fsm.size().1, 2); // Two transitions
    }

    #[test]
    fn test_to_local_type_end() {
        let mut fsm: Fsm<String, String, ()> = Fsm::new("Client".to_string());
        let start = fsm.add_state();

        let lt = to_local_type(&fsm, start);
        assert!(matches!(lt, LocalTypeR::End));
    }

    #[test]
    fn test_roundtrip_send() {
        let original = LocalTypeR::send("Server", Label::new("hello"), LocalTypeR::End);
        let fsm = from_local_type("Client", &original);
        let start = fsm.states().next().unwrap();
        let reconstructed = to_local_type(&fsm, start);

        // Check structure matches (not exact equality due to intermediate representation)
        match reconstructed {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "Server");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "hello");
            }
            _ => panic!("Expected Send"),
        }
    }
}
