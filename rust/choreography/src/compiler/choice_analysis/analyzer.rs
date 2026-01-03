//! Choice propagation analyzer.
//!
//! Implements the core analysis logic for verifying that all roles
//! learn which branch was selected in choice blocks.

use crate::ast::{Branch, Protocol, Role};
use crate::compiler::diagnostics::{Diagnostic, DiagnosticCode, DiagnosticCollector};
use std::collections::{HashMap, HashSet};

use super::types::{
    BranchMessages, ChoiceAnalysisResult, ChoiceId, ChoiceKnowledge, KnowledgeSource, MessageInfo,
};

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
            roles: roles.iter().map(|r| r.name().to_string()).collect(),
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
        let chooser_name = chooser.name().to_string();

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
                    from: from.name().to_string(),
                    to: to.name().to_string(),
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
                        from: from.name().to_string(),
                        to: to.name().to_string(),
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
                            from: from.name().to_string(),
                            to: to.name().to_string(),
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
                roles.insert(from.name().to_string());
                roles.insert(to.name().to_string());
                self.collect_roles_from_protocol(continuation, roles);
            }
            Protocol::Broadcast {
                from,
                to_all,
                continuation,
                ..
            } => {
                roles.insert(from.name().to_string());
                for to in to_all {
                    roles.insert(to.name().to_string());
                }
                self.collect_roles_from_protocol(continuation, roles);
            }
            Protocol::Choice { role, branches, .. } => {
                roles.insert(role.name().to_string());
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
    pub fn find_similar_role(&self, role: &str) -> Option<&String> {
        // Use Levenshtein distance to find similar names
        let threshold = 2; // Max edit distance
        self.roles
            .iter()
            .filter(|r| r.as_str() != role)
            .min_by_key(|r| super::levenshtein_distance(role, r))
            .filter(|r| super::levenshtein_distance(role, r) <= threshold)
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
