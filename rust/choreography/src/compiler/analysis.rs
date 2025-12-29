// Static analysis for choreographic protocols

use crate::ast::{Choreography, Protocol, Role};
use std::collections::{HashMap, HashSet};

/// Analysis results for a choreography
#[derive(Debug)]
pub struct AnalysisResult {
    pub is_deadlock_free: bool,
    pub has_progress: bool,
    pub role_participation: HashMap<Role, ParticipationInfo>,
    pub warnings: Vec<AnalysisWarning>,
    pub communication_graph: CommunicationGraph,
}

/// Information about a role's participation
#[derive(Debug)]
pub struct ParticipationInfo {
    pub sends: usize,
    pub receives: usize,
    pub choices: usize,
    pub is_active: bool,
}

/// Warning generated during analysis
#[derive(Debug, Clone)]
pub enum AnalysisWarning {
    UnusedRole(Role),
    PotentialDeadlock(String),
    NoProgress(String),
    AsymmetricChoice(Role),
    UnreachableCode(String),
}

/// Communication graph for visualization
#[derive(Debug, Clone)]
pub struct CommunicationGraph {
    pub nodes: Vec<Role>,
    pub edges: Vec<(Role, Role, String)>, // (from, to, message)
}

/// Analyze a choreography for correctness properties
#[must_use]
pub fn analyze(choreography: &Choreography) -> AnalysisResult {
    let mut analyzer = Analyzer::new(choreography);
    analyzer.analyze()
}

struct Analyzer<'a> {
    choreography: &'a Choreography,
    warnings: Vec<AnalysisWarning>,
    role_stats: HashMap<Role, RoleStats>,
    comm_graph: CommunicationGraph,
}

#[derive(Default)]
struct RoleStats {
    sends: usize,
    receives: usize,
    choices: usize,
}

impl<'a> Analyzer<'a> {
    fn new(choreography: &'a Choreography) -> Self {
        let mut role_stats = HashMap::new();
        for role in &choreography.roles {
            role_stats.insert(role.clone(), RoleStats::default());
        }

        Analyzer {
            choreography,
            warnings: Vec::new(),
            role_stats,
            comm_graph: CommunicationGraph {
                nodes: choreography.roles.clone(),
                edges: Vec::new(),
            },
        }
    }

    fn analyze(&mut self) -> AnalysisResult {
        // Collect statistics
        self.analyze_protocol(&self.choreography.protocol);

        // Check for deadlocks
        let is_deadlock_free = self.check_deadlock_freedom();

        // Check for progress
        let has_progress = self.check_progress();

        // Check role participation
        let role_participation = self.compute_participation_info();

        // Check for unused roles
        for role in &self.choreography.roles {
            if let Some(info) = role_participation.get(role) {
                if !info.is_active {
                    self.warnings
                        .push(AnalysisWarning::UnusedRole(role.clone()));
                }
            }
        }

        AnalysisResult {
            is_deadlock_free,
            has_progress,
            role_participation,
            warnings: self.warnings.clone(),
            communication_graph: self.comm_graph.clone(),
        }
    }

    fn analyze_protocol(&mut self, protocol: &Protocol) {
        match protocol {
            Protocol::Send {
                from,
                to,
                message,
                continuation,
                ..
            } => {
                if let Some(stats) = self.role_stats.get_mut(from) {
                    stats.sends += 1;
                }
                if let Some(stats) = self.role_stats.get_mut(to) {
                    stats.receives += 1;
                }
                self.comm_graph
                    .edges
                    .push((from.clone(), to.clone(), message.name.to_string()));
                self.analyze_protocol(continuation);
            }

            Protocol::Broadcast {
                from,
                to_all,
                message,
                continuation,
                ..
            } => {
                if let Some(stats) = self.role_stats.get_mut(from) {
                    stats.sends += to_all.len();
                }
                for to in to_all {
                    if let Some(stats) = self.role_stats.get_mut(to) {
                        stats.receives += 1;
                    }
                    self.comm_graph.edges.push((
                        from.clone(),
                        to.clone(),
                        format!("{} (broadcast)", message.name),
                    ));
                }
                self.analyze_protocol(continuation);
            }

            Protocol::Choice { role, branches, .. } => {
                if let Some(stats) = self.role_stats.get_mut(role) {
                    stats.choices += 1;
                }

                // Check for asymmetric choices
                let recipients: HashSet<_> = branches
                    .iter()
                    .filter_map(|branch| {
                        if let Protocol::Send { to, .. } = &branch.protocol {
                            Some(to.clone())
                        } else {
                            None
                        }
                    })
                    .collect();

                if recipients.len() > 1 {
                    self.warnings
                        .push(AnalysisWarning::AsymmetricChoice(role.clone()));
                }

                for branch in branches {
                    self.analyze_protocol(&branch.protocol);
                }
            }

            Protocol::Loop { body, .. } => {
                self.analyze_protocol(body);
            }

            Protocol::Parallel { protocols } => {
                for p in protocols {
                    self.analyze_protocol(p);
                }
            }

            Protocol::Rec { body, .. } => {
                self.analyze_protocol(body);
            }

            Protocol::Var(_) | Protocol::End => {}

            Protocol::Extension { continuation, .. } => {
                self.analyze_protocol(continuation);
            }
        }
    }

    fn check_deadlock_freedom(&self) -> bool {
        // Simple check: ensure no circular waiting patterns
        // More sophisticated analysis would use session type techniques

        // Build dependency graph
        let mut dependencies: HashMap<Role, HashSet<Role>> = HashMap::new();
        for role in &self.choreography.roles {
            dependencies.insert(role.clone(), HashSet::new());
        }

        // Analyze protocol for dependencies
        Self::extract_dependencies(&self.choreography.protocol, &mut dependencies);

        // Check for cycles using DFS
        !has_cycle(&dependencies)
    }

    fn extract_dependencies(protocol: &Protocol, deps: &mut HashMap<Role, HashSet<Role>>) {
        match protocol {
            Protocol::Send {
                from,
                to,
                continuation,
                ..
            } => {
                if let Some(to_deps) = deps.get_mut(to) {
                    to_deps.insert(from.clone());
                }
                Self::extract_dependencies(continuation, deps);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    Self::extract_dependencies(&branch.protocol, deps);
                }
            }
            Protocol::Loop { body, .. } => {
                Self::extract_dependencies(body, deps);
            }
            Protocol::Parallel { protocols } => {
                // Parallel branches don't create dependencies between them
                for p in protocols {
                    Self::extract_dependencies(p, deps);
                }
            }
            Protocol::Rec { body, .. } => {
                Self::extract_dependencies(body, deps);
            }
            Protocol::Broadcast { continuation, .. } => {
                Self::extract_dependencies(continuation, deps);
            }
            Protocol::Var(_) | Protocol::End => {}

            Protocol::Extension { continuation, .. } => {
                Self::extract_dependencies(continuation, deps);
            }
        }
    }

    fn check_progress(&self) -> bool {
        // Check that the protocol eventually terminates or makes progress
        Self::check_protocol_progress(&self.choreography.protocol)
    }

    fn check_protocol_progress(protocol: &Protocol) -> bool {
        match protocol {
            Protocol::End => true,
            Protocol::Send { continuation, .. } => {
                // Send is progress
                Self::check_protocol_progress(continuation)
            }
            Protocol::Choice { branches, .. } => {
                // All branches must have progress
                branches
                    .iter()
                    .all(|b| Self::check_protocol_progress(&b.protocol))
            }
            Protocol::Loop { body, .. } => {
                // Check that loop body has communication (progress)
                has_communication(body)
            }
            Protocol::Parallel { protocols } => protocols.iter().all(Self::check_protocol_progress),
            Protocol::Rec { body, .. } => {
                // Recursive protocols must have communication
                has_communication(body)
            }
            Protocol::Var(_) => true, // Assume recursive calls are okay
            Protocol::Broadcast { continuation, .. } => Self::check_protocol_progress(continuation),

            Protocol::Extension { continuation, .. } => Self::check_protocol_progress(continuation),
        }
    }

    fn compute_participation_info(&self) -> HashMap<Role, ParticipationInfo> {
        let mut result = HashMap::new();

        for (role, stats) in &self.role_stats {
            result.insert(
                role.clone(),
                ParticipationInfo {
                    sends: stats.sends,
                    receives: stats.receives,
                    choices: stats.choices,
                    is_active: stats.sends > 0 || stats.receives > 0 || stats.choices > 0,
                },
            );
        }

        result
    }
}

// Helper functions

fn has_cycle(graph: &HashMap<Role, HashSet<Role>>) -> bool {
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

fn has_communication(protocol: &Protocol) -> bool {
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

/// Generate a DOT graph visualization of the communication pattern
#[must_use]
pub fn generate_dot_graph(comm_graph: &CommunicationGraph) -> String {
    let mut dot = String::from("digraph G {\n");
    dot.push_str("  rankdir=LR;\n");
    dot.push_str("  node [shape=circle];\n");

    // Add nodes
    for node in &comm_graph.nodes {
        dot.push_str(&format!("  {};\n", node.name));
    }

    // Add edges
    for (from, to, label) in &comm_graph.edges {
        dot.push_str(&format!(
            "  {} -> {} [label=\"{}\"];\n",
            from.name, to.name, label
        ));
    }

    dot.push_str("}\n");
    dot
}
