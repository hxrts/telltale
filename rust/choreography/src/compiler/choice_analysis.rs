//! Choice Propagation Analysis
//!
//! This module implements compile-time verification that all roles
//! learn which branch was selected in choice blocks.
//!
//! # Choice Knowledge Rules
//!
//! 1. The choosing role automatically knows the branch
//! 2. A role learns the branch when it receives a message from a role that knows
//! 3. Knowledge propagates transitively through message passing
//! 4. If a role participates in a branch but never learns which branch,
//!    that's a compile-time error
//!
//! # Example
//!
//! ```text
//! case choose Seller of
//!     Accept => {
//!         Seller -> Buyer: Accepted;  // Buyer learns: Accept
//!     }
//!     Reject => {
//!         Seller -> Buyer: Rejected;  // Buyer learns: Reject
//!     }
//! }
//! ```
//!
//! Here, both branches start with Seller sending to Buyer, so Buyer learns
//! the outcome. If Observer was involved but never received a message,
//! we'd emit an error.

use crate::ast::{Branch, Protocol, Role};
use crate::compiler::diagnostics::{
    Diagnostic, DiagnosticCode, DiagnosticCollector, Severity, SourceLocation,
};
use std::collections::{HashMap, HashSet};

/// Unique identifier for a choice point in the protocol
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ChoiceId {
    /// Protocol path to this choice (for nested choices)
    pub path: Vec<String>,
    /// The choosing role
    pub chooser: String,
    /// Index of this choice (for multiple choices by same role)
    pub index: usize,
}

impl ChoiceId {
    /// Create a new choice ID
    pub fn new(chooser: &str, index: usize) -> Self {
        Self {
            path: Vec::new(),
            chooser: chooser.to_string(),
            index,
        }
    }

    /// Create a nested choice ID
    pub fn nested(parent: &ChoiceId, chooser: &str, index: usize) -> Self {
        let mut path = parent.path.clone();
        path.push(format!("{}:{}", parent.chooser, parent.index));
        Self {
            path,
            chooser: chooser.to_string(),
            index,
        }
    }

    /// Get a display string for this choice
    #[must_use]
    pub fn display(&self) -> String {
        if self.path.is_empty() {
            format!("choice {} #{}", self.chooser, self.index)
        } else {
            format!(
                "choice {} #{} (in {})",
                self.chooser,
                self.index,
                self.path.join("/")
            )
        }
    }
}

/// Knowledge state for a single choice point
#[derive(Debug, Clone)]
pub struct ChoiceKnowledge {
    /// The choice identifier
    pub choice_id: ChoiceId,
    /// Branch labels
    pub branches: Vec<String>,
    /// Which roles know the choice outcome (role name -> how they learned)
    pub informed_roles: HashMap<String, KnowledgeSource>,
    /// Roles that participate but don't know the outcome
    pub uninformed_roles: HashSet<String>,
    /// Source location of the choice block
    pub location: Option<SourceLocation>,
    /// Per-branch participation info (branch label -> roles that participate)
    pub branch_participation: HashMap<String, HashSet<String>>,
}

/// How a role learned about a choice
#[derive(Debug, Clone)]
pub enum KnowledgeSource {
    /// The role made the choice
    Chooser,
    /// Learned via message from another role
    MessageFrom {
        sender: String,
        /// The message types that informed this role (one per branch)
        messages: Vec<String>,
    },
    /// Learned transitively (A told B, B told this role)
    Transitive {
        via: String,
        original_source: Box<KnowledgeSource>,
    },
}

impl KnowledgeSource {
    /// Get a human-readable description
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            KnowledgeSource::Chooser => "is the chooser".to_string(),
            KnowledgeSource::MessageFrom { sender, messages } => {
                format!("learns from {} via messages: {:?}", sender, messages)
            }
            KnowledgeSource::Transitive { via, .. } => {
                format!("learns transitively via {}", via)
            }
        }
    }
}

/// Result of choice propagation analysis
#[derive(Debug)]
pub struct ChoiceAnalysisResult {
    /// All choice points found
    pub choices: Vec<ChoiceKnowledge>,
    /// Diagnostics generated during analysis
    pub diagnostics: Vec<Diagnostic>,
}

impl ChoiceAnalysisResult {
    /// Check if all roles are informed for all choices
    #[must_use]
    pub fn all_roles_informed(&self) -> bool {
        self.choices.iter().all(|c| c.uninformed_roles.is_empty())
    }

    /// Get choices where some roles are uninformed
    pub fn problematic_choices(&self) -> Vec<&ChoiceKnowledge> {
        self.choices
            .iter()
            .filter(|c| !c.uninformed_roles.is_empty())
            .collect()
    }

    /// Get diagnostic count by severity
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .count()
    }

    /// Check if analysis passed (no errors)
    #[must_use]
    pub fn passed(&self) -> bool {
        self.error_count() == 0
    }
}

/// Analyzer for choice propagation
#[derive(Debug)]
pub struct ChoiceAnalyzer {
    /// All declared roles in the choreography
    roles: Vec<String>,
    /// Diagnostic collector
    diagnostics: DiagnosticCollector,
    /// Choice index counter (per chooser)
    choice_counts: HashMap<String, usize>,
}

impl ChoiceAnalyzer {
    /// Create a new choice analyzer
    pub fn new(roles: &[Role]) -> Self {
        Self {
            roles: roles.iter().map(|r| r.name.to_string()).collect(),
            diagnostics: DiagnosticCollector::new(),
            choice_counts: HashMap::new(),
        }
    }

    /// Analyze choice propagation in a protocol
    pub fn analyze(&mut self, protocol: &Protocol) -> ChoiceAnalysisResult {
        let mut choices = Vec::new();
        self.analyze_protocol(protocol, &mut choices, None);

        // Generate diagnostics for uninformed roles
        for choice in &choices {
            for uninformed in &choice.uninformed_roles {
                self.emit_uninformed_role_error(choice, uninformed);
            }
        }

        ChoiceAnalysisResult {
            choices,
            diagnostics: self.diagnostics.take_diagnostics(),
        }
    }

    /// Recursively analyze a protocol for choice points
    fn analyze_protocol(
        &mut self,
        protocol: &Protocol,
        choices: &mut Vec<ChoiceKnowledge>,
        parent_choice: Option<&ChoiceId>,
    ) {
        match protocol {
            Protocol::Choice { role, branches, .. } => {
                let choice_knowledge = self.analyze_choice(role, branches, parent_choice);
                let choice_id = choice_knowledge.choice_id.clone();
                choices.push(choice_knowledge);

                // Recursively analyze branch protocols
                for branch in branches {
                    self.analyze_protocol(&branch.protocol, choices, Some(&choice_id));
                }
            }
            Protocol::Send { continuation, .. } => {
                self.analyze_protocol(continuation, choices, parent_choice);
            }
            Protocol::Broadcast { continuation, .. } => {
                self.analyze_protocol(continuation, choices, parent_choice);
            }
            Protocol::Loop { body, .. } => {
                self.analyze_protocol(body, choices, parent_choice);
            }
            Protocol::Parallel { protocols } => {
                for p in protocols {
                    self.analyze_protocol(p, choices, parent_choice);
                }
            }
            Protocol::Rec { body, .. } => {
                self.analyze_protocol(body, choices, parent_choice);
            }
            Protocol::Extension { continuation, .. } => {
                self.analyze_protocol(continuation, choices, parent_choice);
            }
            Protocol::Var(_) | Protocol::End => {}
        }
    }

    /// Analyze a single choice point
    fn analyze_choice(
        &mut self,
        chooser: &Role,
        branches: &[Branch],
        parent_choice: Option<&ChoiceId>,
    ) -> ChoiceKnowledge {
        let chooser_name = chooser.name.to_string();

        // Get unique choice ID
        let index = *self.choice_counts.get(&chooser_name).unwrap_or(&0);
        self.choice_counts.insert(chooser_name.clone(), index + 1);

        let choice_id = match parent_choice {
            Some(parent) => ChoiceId::nested(parent, &chooser_name, index),
            None => ChoiceId::new(&chooser_name, index),
        };

        // Collect branch labels
        let branch_labels: Vec<String> = branches.iter().map(|b| b.label.to_string()).collect();

        // Initialize knowledge: chooser always knows
        let mut informed_roles: HashMap<String, KnowledgeSource> = HashMap::new();
        informed_roles.insert(chooser_name.clone(), KnowledgeSource::Chooser);

        // Analyze each branch to find message patterns
        let branch_messages = self.collect_branch_messages(branches);

        // Find roles that receive messages in all branches
        let roles_receiving_in_all = self.find_roles_receiving_in_all_branches(&branch_messages);

        // For each such role, they learn the choice
        for (role, messages_per_branch) in roles_receiving_in_all {
            if !informed_roles.contains_key(&role) {
                // Find the sender (typically the chooser or someone informed)
                if let Some(sender) = self.find_message_sender(&branch_messages, &role) {
                    informed_roles.insert(
                        role.clone(),
                        KnowledgeSource::MessageFrom {
                            sender,
                            messages: messages_per_branch,
                        },
                    );
                }
            }
        }

        // Propagate knowledge transitively through remaining messages
        self.propagate_knowledge(&mut informed_roles, &branch_messages, &branch_labels);

        // Find roles that participate but are uninformed
        let participating_roles = self.find_participating_roles(branches);
        let uninformed_roles: HashSet<String> = participating_roles
            .into_iter()
            .filter(|r| !informed_roles.contains_key(r))
            .collect();

        // Build branch participation map
        let branch_participation = self.build_branch_participation(&branch_messages);

        ChoiceKnowledge {
            choice_id,
            branches: branch_labels,
            informed_roles,
            uninformed_roles,
            location: None, // Could be populated from span info
            branch_participation,
        }
    }

    /// Build a map of which roles participate in each branch
    fn build_branch_participation(
        &self,
        branch_messages: &[BranchMessages],
    ) -> HashMap<String, HashSet<String>> {
        branch_messages
            .iter()
            .map(|branch| {
                let mut roles = HashSet::new();
                for msg in &branch.messages {
                    roles.insert(msg.from.clone());
                    roles.insert(msg.to.clone());
                }
                (branch.label.clone(), roles)
            })
            .collect()
    }

    /// Collect message patterns from each branch
    fn collect_branch_messages(&self, branches: &[Branch]) -> Vec<BranchMessages> {
        branches
            .iter()
            .map(|branch| {
                let mut messages = Vec::new();
                self.collect_messages_from_protocol(&branch.protocol, &mut messages);
                BranchMessages {
                    label: branch.label.to_string(),
                    messages,
                }
            })
            .collect()
    }

    /// Recursively collect messages from a protocol
    #[allow(clippy::only_used_in_recursion)]
    fn collect_messages_from_protocol(&self, protocol: &Protocol, messages: &mut Vec<MessageInfo>) {
        match protocol {
            Protocol::Send {
                from,
                to,
                message,
                continuation,
                ..
            } => {
                messages.push(MessageInfo {
                    from: from.name.to_string(),
                    to: to.name.to_string(),
                    message_type: message.name.to_string(),
                });
                self.collect_messages_from_protocol(continuation, messages);
            }
            Protocol::Broadcast {
                from,
                to_all,
                message,
                continuation,
                ..
            } => {
                for to in to_all {
                    messages.push(MessageInfo {
                        from: from.name.to_string(),
                        to: to.name.to_string(),
                        message_type: message.name.to_string(),
                    });
                }
                self.collect_messages_from_protocol(continuation, messages);
            }
            Protocol::Choice { branches, .. } => {
                // Don't descend into nested choices - they're analyzed separately
                // But we do need to track messages before the nested choice
                for branch in branches {
                    // Only take the first message from each branch for initial analysis
                    if let Protocol::Send {
                        from, to, message, ..
                    } = &branch.protocol
                    {
                        messages.push(MessageInfo {
                            from: from.name.to_string(),
                            to: to.name.to_string(),
                            message_type: message.name.to_string(),
                        });
                    }
                }
            }
            Protocol::Loop { body, .. } => {
                self.collect_messages_from_protocol(body, messages);
            }
            Protocol::Parallel { protocols } => {
                for p in protocols {
                    self.collect_messages_from_protocol(p, messages);
                }
            }
            Protocol::Rec { body, .. } => {
                self.collect_messages_from_protocol(body, messages);
            }
            Protocol::Extension { continuation, .. } => {
                self.collect_messages_from_protocol(continuation, messages);
            }
            Protocol::Var(_) | Protocol::End => {}
        }
    }

    /// Find roles that receive messages in ALL branches
    fn find_roles_receiving_in_all_branches(
        &self,
        branch_messages: &[BranchMessages],
    ) -> HashMap<String, Vec<String>> {
        if branch_messages.is_empty() {
            return HashMap::new();
        }

        // For each role, collect the message types they receive in each branch
        let mut role_messages: HashMap<String, Vec<Option<String>>> = HashMap::new();

        for (branch_idx, branch) in branch_messages.iter().enumerate() {
            // Find first message to each role in this branch
            let mut seen_roles: HashSet<String> = HashSet::new();
            for msg in &branch.messages {
                if !seen_roles.contains(&msg.to) {
                    seen_roles.insert(msg.to.clone());
                    role_messages
                        .entry(msg.to.clone())
                        .or_insert_with(|| vec![None; branch_messages.len()])[branch_idx] =
                        Some(msg.message_type.clone());
                }
            }
        }

        // Filter to roles that receive in ALL branches
        role_messages
            .into_iter()
            .filter_map(|(role, messages)| {
                if messages.iter().all(|m| m.is_some()) {
                    let msg_types: Vec<String> = messages.into_iter().map(|m| m.unwrap()).collect();
                    Some((role, msg_types))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Find who sends to a role in a branch
    fn find_message_sender(
        &self,
        branch_messages: &[BranchMessages],
        receiver: &str,
    ) -> Option<String> {
        for branch in branch_messages {
            for msg in &branch.messages {
                if msg.to == receiver {
                    return Some(msg.from.clone());
                }
            }
        }
        None
    }

    /// Propagate knowledge transitively through message chains
    ///
    /// A role only becomes informed if they receive from an informed sender
    /// in ALL branches (not just some).
    fn propagate_knowledge(
        &self,
        informed: &mut HashMap<String, KnowledgeSource>,
        branch_messages: &[BranchMessages],
        _branch_labels: &[String],
    ) {
        if branch_messages.is_empty() {
            return;
        }

        // Fixed-point iteration: keep propagating until no changes
        let mut changed = true;
        while changed {
            changed = false;

            // Find roles that receive from an informed sender in ALL branches
            // First, collect senders per receiver per branch
            let mut receiver_senders_per_branch: HashMap<String, Vec<Option<String>>> =
                HashMap::new();

            for (branch_idx, branch) in branch_messages.iter().enumerate() {
                // Track first informed sender to each role in this branch
                let mut seen_receivers: HashSet<String> = HashSet::new();
                for msg in &branch.messages {
                    if informed.contains_key(&msg.from) && !seen_receivers.contains(&msg.to) {
                        seen_receivers.insert(msg.to.clone());
                        receiver_senders_per_branch
                            .entry(msg.to.clone())
                            .or_insert_with(|| vec![None; branch_messages.len()])[branch_idx] =
                            Some(msg.from.clone());
                    }
                }
            }

            // Only mark roles as informed if they receive in ALL branches
            for (receiver, senders) in &receiver_senders_per_branch {
                if !informed.contains_key(receiver) && senders.iter().all(|s| s.is_some()) {
                    // Find a consistent sender (use first branch's sender)
                    if let Some(sender) = &senders[0] {
                        let source = informed.get(sender).unwrap().clone();
                        informed.insert(
                            receiver.clone(),
                            KnowledgeSource::Transitive {
                                via: sender.clone(),
                                original_source: Box::new(source),
                            },
                        );
                        changed = true;
                    }
                }
            }
        }
    }

    /// Find all roles that participate in any branch
    fn find_participating_roles(&self, branches: &[Branch]) -> HashSet<String> {
        let mut roles = HashSet::new();
        for branch in branches {
            self.collect_roles_from_protocol(&branch.protocol, &mut roles);
        }
        roles
    }

    /// Recursively collect roles from a protocol
    #[allow(clippy::only_used_in_recursion)]
    fn collect_roles_from_protocol(&self, protocol: &Protocol, roles: &mut HashSet<String>) {
        match protocol {
            Protocol::Send {
                from,
                to,
                continuation,
                ..
            } => {
                roles.insert(from.name.to_string());
                roles.insert(to.name.to_string());
                self.collect_roles_from_protocol(continuation, roles);
            }
            Protocol::Broadcast {
                from,
                to_all,
                continuation,
                ..
            } => {
                roles.insert(from.name.to_string());
                for to in to_all {
                    roles.insert(to.name.to_string());
                }
                self.collect_roles_from_protocol(continuation, roles);
            }
            Protocol::Choice { role, branches, .. } => {
                roles.insert(role.name.to_string());
                for branch in branches {
                    self.collect_roles_from_protocol(&branch.protocol, roles);
                }
            }
            Protocol::Loop { body, .. } => {
                self.collect_roles_from_protocol(body, roles);
            }
            Protocol::Parallel { protocols } => {
                for p in protocols {
                    self.collect_roles_from_protocol(p, roles);
                }
            }
            Protocol::Rec { body, .. } => {
                self.collect_roles_from_protocol(body, roles);
            }
            Protocol::Extension { continuation, .. } => {
                self.collect_roles_from_protocol(continuation, roles);
            }
            Protocol::Var(_) | Protocol::End => {}
        }
    }

    /// Emit error for uninformed role
    fn emit_uninformed_role_error(&mut self, choice: &ChoiceKnowledge, role: &str) {
        let mut diagnostic = Diagnostic::error(
            DiagnosticCode::ChoicePropagationError,
            format!(
                "Role '{}' cannot determine which branch was selected in {}",
                role,
                choice.choice_id.display()
            ),
        );

        // Add helpful suggestion
        diagnostic.suggestions.push(format!(
            "Add a message from '{}' to '{}' in each branch to inform about the choice",
            choice.choice_id.chooser, role
        ));

        // Show which branches the role participates in using branch_participation
        let present_branches: Vec<&String> = choice
            .branch_participation
            .iter()
            .filter(|(_label, roles)| roles.contains(role))
            .map(|(label, _)| label)
            .collect();
        let absent_branches: Vec<&String> = choice
            .branch_participation
            .iter()
            .filter(|(_label, roles)| !roles.contains(role))
            .map(|(label, _)| label)
            .collect();

        if !present_branches.is_empty() && !absent_branches.is_empty() {
            diagnostic.notes.push(format!(
                "'{}' participates in branch(es): {} but NOT in: {}",
                role,
                present_branches
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(", "),
                absent_branches
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        } else if !present_branches.is_empty() {
            diagnostic.notes.push(format!(
                "'{}' participates in: {}",
                role,
                present_branches
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }

        // Add note about which roles are informed
        if !choice.informed_roles.is_empty() {
            let informed_list: Vec<String> = choice
                .informed_roles
                .iter()
                .map(|(r, src)| format!("{} ({})", r, src.description()))
                .collect();
            diagnostic
                .notes
                .push(format!("Informed roles: {}", informed_list.join(", ")));
        }

        // Check if role might be a typo
        if let Some(suggestion) = self.find_similar_role(role) {
            diagnostic
                .suggestions
                .push(format!("Did you mean '{}'?", suggestion));
        }

        // Add note about branches
        diagnostic
            .notes
            .push(format!("Choice branches: {:?}", choice.branches));

        if let Some(ref loc) = choice.location {
            diagnostic.location = Some(loc.clone());
        }

        self.diagnostics.add(diagnostic);
    }

    /// Find a similar role name (for typo suggestions)
    fn find_similar_role(&self, role: &str) -> Option<&String> {
        // Use Levenshtein distance to find similar names
        let threshold = 2; // Max edit distance
        self.roles
            .iter()
            .filter(|r| r.as_str() != role)
            .min_by_key(|r| levenshtein_distance(role, r))
            .filter(|r| levenshtein_distance(role, r) <= threshold)
    }

    /// Get all declared roles
    #[must_use]
    pub fn declared_roles(&self) -> &[String] {
        &self.roles
    }

    /// Check if a role is declared
    #[must_use]
    pub fn is_role_declared(&self, role: &str) -> bool {
        self.roles.iter().any(|r| r == role)
    }
}

/// Calculate Levenshtein edit distance between two strings
#[allow(clippy::needless_range_loop)]
fn levenshtein_distance(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let a_len = a_chars.len();
    let b_len = b_chars.len();

    if a_len == 0 {
        return b_len;
    }
    if b_len == 0 {
        return a_len;
    }

    let mut matrix = vec![vec![0usize; b_len + 1]; a_len + 1];

    for i in 0..=a_len {
        matrix[i][0] = i;
    }
    for j in 0..=b_len {
        matrix[0][j] = j;
    }

    for i in 1..=a_len {
        for j in 1..=b_len {
            let cost = if a_chars[i - 1] == b_chars[j - 1] {
                0
            } else {
                1
            };
            matrix[i][j] = std::cmp::min(
                std::cmp::min(matrix[i - 1][j] + 1, matrix[i][j - 1] + 1),
                matrix[i - 1][j - 1] + cost,
            );
        }
    }

    matrix[a_len][b_len]
}

/// Messages in a single branch
#[derive(Debug)]
struct BranchMessages {
    /// Branch label for participation tracking
    label: String,
    /// Messages in this branch
    messages: Vec<MessageInfo>,
}

/// Information about a single message
#[derive(Debug, Clone)]
struct MessageInfo {
    from: String,
    to: String,
    message_type: String,
}

/// Check if message types are distinguishing (unique per branch)
pub fn messages_are_distinguishing(messages_per_branch: &[String]) -> bool {
    let unique: HashSet<&String> = messages_per_branch.iter().collect();
    unique.len() == messages_per_branch.len()
}

/// Analyze choice propagation for a choreography
pub fn analyze_choreography_choices(protocol: &Protocol, roles: &[Role]) -> ChoiceAnalysisResult {
    let mut analyzer = ChoiceAnalyzer::new(roles);
    analyzer.analyze(protocol)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::MessageType;
    use proc_macro2::Ident;
    use proc_macro2::Span;

    fn make_role(name: &str) -> Role {
        Role {
            name: Ident::new(name, Span::call_site()),
            param: None,
            index: None,
            array_size: None,
        }
    }

    fn make_message(name: &str) -> MessageType {
        MessageType {
            name: Ident::new(name, Span::call_site()),
            type_annotation: None,
            payload: None,
        }
    }

    #[test]
    fn test_simple_informed_choice() {
        // case choose Seller of
        //     Accept => { Seller -> Buyer: Accepted; }
        //     Reject => { Seller -> Buyer: Rejected; }
        // }
        let seller = make_role("Seller");
        let buyer = make_role("Buyer");

        let protocol = Protocol::Choice {
            role: seller.clone(),
            branches: vec![
                Branch {
                    label: Ident::new("Accept", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Accepted"),
                        continuation: Box::new(Protocol::End),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                Branch {
                    label: Ident::new("Reject", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Rejected"),
                        continuation: Box::new(Protocol::End),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
            ],
            annotations: Default::default(),
        };

        let roles = vec![seller, buyer];
        let result = analyze_choreography_choices(&protocol, &roles);

        assert!(result.passed(), "Should pass: {:?}", result.diagnostics);
        assert_eq!(result.choices.len(), 1);

        let choice = &result.choices[0];
        assert!(choice.informed_roles.contains_key("Seller"));
        assert!(choice.informed_roles.contains_key("Buyer"));
        assert!(choice.uninformed_roles.is_empty());
    }

    #[test]
    fn test_uninformed_observer() {
        // case choose Seller of
        //     Accept => { Seller -> Buyer: Accepted; }
        //     Reject => { Seller -> Buyer: Rejected; }
        // }
        // Observer participates but is not informed
        let seller = make_role("Seller");
        let buyer = make_role("Buyer");
        let observer = make_role("Observer");

        let protocol = Protocol::Choice {
            role: seller.clone(),
            branches: vec![
                Branch {
                    label: Ident::new("Accept", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Accepted"),
                        continuation: Box::new(Protocol::Send {
                            from: buyer.clone(),
                            to: observer.clone(),
                            message: make_message("Done"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                Branch {
                    label: Ident::new("Reject", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Rejected"),
                        continuation: Box::new(Protocol::Send {
                            // Observer only gets message in one branch - still uninformed
                            // because the message type is the same ("Done")
                            from: buyer.clone(),
                            to: observer.clone(),
                            message: make_message("Done"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
            ],
            annotations: Default::default(),
        };

        let roles = vec![seller, buyer, observer];
        let result = analyze_choreography_choices(&protocol, &roles);

        // Observer IS informed because Buyer (who is informed) sends to Observer
        // This is transitive knowledge propagation
        assert!(result.passed(), "Should pass with transitive knowledge");
        assert_eq!(result.choices.len(), 1);

        let choice = &result.choices[0];
        assert!(choice.informed_roles.contains_key("Observer"));
    }

    #[test]
    fn test_truly_uninformed_observer() {
        // Observer participates in only ONE branch - they're uninformed
        let seller = make_role("Seller");
        let buyer = make_role("Buyer");
        let observer = make_role("Observer");

        let protocol = Protocol::Choice {
            role: seller.clone(),
            branches: vec![
                Branch {
                    label: Ident::new("Accept", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Accepted"),
                        continuation: Box::new(Protocol::Send {
                            from: buyer.clone(),
                            to: observer.clone(),
                            message: make_message("Notify"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                Branch {
                    label: Ident::new("Reject", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Rejected"),
                        continuation: Box::new(Protocol::End), // Observer not involved!
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
            ],
            annotations: Default::default(),
        };

        let roles = vec![seller, buyer, observer];
        let result = analyze_choreography_choices(&protocol, &roles);

        // Observer only participates in Accept branch - uninformed about choice
        assert!(!result.passed(), "Should fail: Observer uninformed");
        assert_eq!(result.error_count(), 1);

        let choice = &result.choices[0];
        assert!(choice.uninformed_roles.contains("Observer"));
    }

    #[test]
    fn test_transitive_knowledge() {
        // A -> B, B -> C means C knows transitively
        let a = make_role("A");
        let b = make_role("B");
        let c = make_role("C");

        let protocol = Protocol::Choice {
            role: a.clone(),
            branches: vec![
                Branch {
                    label: Ident::new("Left", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: a.clone(),
                        to: b.clone(),
                        message: make_message("L"),
                        continuation: Box::new(Protocol::Send {
                            from: b.clone(),
                            to: c.clone(),
                            message: make_message("Info"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                Branch {
                    label: Ident::new("Right", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: a.clone(),
                        to: b.clone(),
                        message: make_message("R"),
                        continuation: Box::new(Protocol::Send {
                            from: b.clone(),
                            to: c.clone(),
                            message: make_message("Info"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
            ],
            annotations: Default::default(),
        };

        let roles = vec![a, b, c];
        let result = analyze_choreography_choices(&protocol, &roles);

        assert!(result.passed());

        let choice = &result.choices[0];
        assert!(choice.informed_roles.contains_key("A")); // Chooser
        assert!(choice.informed_roles.contains_key("B")); // Direct message from chooser
        assert!(choice.informed_roles.contains_key("C")); // Informed via B

        // C is informed either via MessageFrom (receives in all branches) or Transitive
        match &choice.informed_roles["C"] {
            KnowledgeSource::MessageFrom { sender, .. } => {
                assert_eq!(sender, "B", "C should learn from B");
            }
            KnowledgeSource::Transitive { via, .. } => {
                assert_eq!(via, "B", "C should learn transitively via B");
            }
            other => panic!("Expected C to learn from B, got {:?}", other),
        }
    }

    #[test]
    fn test_choice_id() {
        let id1 = ChoiceId::new("Seller", 0);
        assert_eq!(id1.display(), "choice Seller #0");

        let id2 = ChoiceId::nested(&id1, "Buyer", 0);
        assert_eq!(id2.display(), "choice Buyer #0 (in Seller:0)");
    }

    #[test]
    fn test_messages_are_distinguishing() {
        assert!(messages_are_distinguishing(&[
            "A".to_string(),
            "B".to_string()
        ]));
        assert!(!messages_are_distinguishing(&[
            "A".to_string(),
            "A".to_string()
        ]));
        assert!(messages_are_distinguishing(&[
            "X".to_string(),
            "Y".to_string(),
            "Z".to_string()
        ]));
    }

    #[test]
    fn test_levenshtein_distance() {
        assert_eq!(levenshtein_distance("", ""), 0);
        assert_eq!(levenshtein_distance("abc", "abc"), 0);
        assert_eq!(levenshtein_distance("abc", "abd"), 1);
        assert_eq!(levenshtein_distance("abc", "abcd"), 1);
        assert_eq!(levenshtein_distance("Buyer", "Buyr"), 1);
        assert_eq!(levenshtein_distance("Seller", "Seler"), 1);
        assert_eq!(levenshtein_distance("Observer", "Observr"), 1);
        assert_eq!(levenshtein_distance("Alice", "Bob"), 5);
    }

    #[test]
    fn test_find_similar_role() {
        let roles = vec![
            make_role("Seller"),
            make_role("Buyer"),
            make_role("Observer"),
        ];
        let analyzer = ChoiceAnalyzer::new(&roles);

        // Typo should suggest similar role
        assert_eq!(
            analyzer.find_similar_role("Seler"),
            Some(&"Seller".to_string())
        );
        assert_eq!(
            analyzer.find_similar_role("Buyr"),
            Some(&"Buyer".to_string())
        );
        assert_eq!(
            analyzer.find_similar_role("Observr"),
            Some(&"Observer".to_string())
        );

        // Completely different name should not suggest
        assert_eq!(analyzer.find_similar_role("XYZ"), None);
        assert_eq!(analyzer.find_similar_role("Coordinator"), None);

        // Exact match should not suggest itself
        assert_eq!(analyzer.find_similar_role("Seller"), None);
    }

    #[test]
    fn test_branch_participation_tracking() {
        // Observer participates in only ONE branch
        let seller = make_role("Seller");
        let buyer = make_role("Buyer");
        let observer = make_role("Observer");

        let protocol = Protocol::Choice {
            role: seller.clone(),
            branches: vec![
                Branch {
                    label: Ident::new("Accept", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Accepted"),
                        continuation: Box::new(Protocol::Send {
                            from: buyer.clone(),
                            to: observer.clone(),
                            message: make_message("Notify"),
                            continuation: Box::new(Protocol::End),
                            annotations: Default::default(),
                            from_annotations: Default::default(),
                            to_annotations: Default::default(),
                        }),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
                Branch {
                    label: Ident::new("Reject", Span::call_site()),
                    guard: None,
                    protocol: Protocol::Send {
                        from: seller.clone(),
                        to: buyer.clone(),
                        message: make_message("Rejected"),
                        continuation: Box::new(Protocol::End),
                        annotations: Default::default(),
                        from_annotations: Default::default(),
                        to_annotations: Default::default(),
                    },
                },
            ],
            annotations: Default::default(),
        };

        let roles = vec![seller, buyer, observer];
        let result = analyze_choreography_choices(&protocol, &roles);

        let choice = &result.choices[0];

        // Check branch participation tracking
        assert!(choice.branch_participation.contains_key("Accept"));
        assert!(choice.branch_participation.contains_key("Reject"));

        // Observer should participate in Accept but not Reject
        let accept_roles = &choice.branch_participation["Accept"];
        let reject_roles = &choice.branch_participation["Reject"];

        assert!(
            accept_roles.contains("Observer"),
            "Observer should be in Accept"
        );
        assert!(
            !reject_roles.contains("Observer"),
            "Observer should NOT be in Reject"
        );

        // Seller and Buyer should be in both branches
        assert!(accept_roles.contains("Seller"));
        assert!(accept_roles.contains("Buyer"));
        assert!(reject_roles.contains("Seller"));
        assert!(reject_roles.contains("Buyer"));
    }

    #[test]
    fn test_declared_roles_methods() {
        let roles = vec![make_role("Alice"), make_role("Bob"), make_role("Carol")];
        let analyzer = ChoiceAnalyzer::new(&roles);

        assert_eq!(analyzer.declared_roles().len(), 3);
        assert!(analyzer.is_role_declared("Alice"));
        assert!(analyzer.is_role_declared("Bob"));
        assert!(analyzer.is_role_declared("Carol"));
        assert!(!analyzer.is_role_declared("Dave"));
    }
}
