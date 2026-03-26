//! Types for choice propagation analysis.
//!
//! This module defines the core data structures used to track choice knowledge
//! propagation through protocol branches.

use crate::compiler::diagnostics::{Diagnostic, Severity, SourceLocation};
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

/// Messages in a single branch
#[derive(Debug)]
pub(super) struct BranchMessages {
    /// Branch label for participation tracking
    pub label: String,
    /// Messages in this branch
    pub messages: Vec<MessageInfo>,
}

/// Information about a single message
#[derive(Debug, Clone)]
pub(super) struct MessageInfo {
    pub from: String,
    pub to: String,
    pub message_type: String,
}
