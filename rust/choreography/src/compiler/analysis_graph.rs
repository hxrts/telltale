use crate::ast::{Protocol, Role};
use std::collections::{HashMap, HashSet};

pub(super) fn has_cycle(graph: &HashMap<Role, HashSet<Role>>) -> bool {
    let mut visited = HashSet::new();
    let mut rec_stack = HashSet::new();

    for node in graph.keys() {
        if !visited.contains(node) && dfs_cycle(node, graph, &mut visited, &mut rec_stack) {
            return true;
        }
    }

    false
}

fn dfs_cycle(
    node: &Role,
    graph: &HashMap<Role, HashSet<Role>>,
    visited: &mut HashSet<Role>,
    rec_stack: &mut HashSet<Role>,
) -> bool {
    visited.insert(node.clone());
    rec_stack.insert(node.clone());

    if let Some(neighbors) = graph.get(node) {
        for neighbor in neighbors {
            if !visited.contains(neighbor) {
                if dfs_cycle(neighbor, graph, visited, rec_stack) {
                    return true;
                }
            } else if rec_stack.contains(neighbor) {
                return true;
            }
        }
    }

    rec_stack.remove(node);
    false
}

// RECURSION_SAFE: structural recursion over finite protocol AST depth.
pub(super) fn has_communication(protocol: &Protocol) -> bool {
    match protocol {
        Protocol::Send { .. } | Protocol::Broadcast { .. } => true,
        Protocol::Choice { branches, .. } => {
            branches.iter().any(|b| has_communication(&b.protocol))
        }
        Protocol::Loop { body, .. } => has_communication(body),
        Protocol::Parallel { protocols } => protocols.iter().any(has_communication),
        Protocol::Rec { body, .. } => has_communication(body),
        Protocol::Var(_) | Protocol::End => false,
        Protocol::Extension { continuation, .. } => has_communication(continuation),
    }
}
