// Protocol AST definitions

use super::{Role, MessageType, ValidationError};
use proc_macro2::{Ident, TokenStream};
use std::collections::HashMap;

/// Protocol specification using choreographic constructs
#[derive(Debug, Clone)]
pub enum Protocol {
    /// Message send: A -> B: Message
    Send {
        from: Role,
        to: Role,
        message: MessageType,
        continuation: Box<Protocol>,
        /// Statement-level annotations
        annotations: HashMap<String, String>,
        /// From role annotations
        from_annotations: HashMap<String, String>,
        /// To role annotations
        to_annotations: HashMap<String, String>,
    },

    /// Broadcast: A -> *: Message
    Broadcast {
        from: Role,
        to_all: Vec<Role>,
        message: MessageType,
        continuation: Box<Protocol>,
        /// Statement-level annotations
        annotations: HashMap<String, String>,
        /// From role annotations
        from_annotations: HashMap<String, String>,
    },

    /// Choice made by a role
    Choice { 
        role: Role, 
        branches: Vec<Branch>,
        /// Statement-level annotations
        annotations: HashMap<String, String>,
    },

    /// Loop construct
    Loop {
        condition: Option<Condition>,
        body: Box<Protocol>,
    },

    /// Parallel composition
    Parallel { protocols: Vec<Protocol> },

    /// Recursive protocol with label
    Rec { label: Ident, body: Box<Protocol> },

    /// Reference to recursive label
    Var(Ident),

    /// Protocol termination
    End,
}

/// A branch in a choice
#[derive(Debug, Clone)]
pub struct Branch {
    pub label: Ident,
    pub guard: Option<TokenStream>,
    pub protocol: Protocol,
}

/// Loop condition
#[derive(Debug, Clone)]
pub enum Condition {
    /// Loop while a role decides
    RoleDecides(Role),
    /// Fixed iteration count
    Count(usize),
    /// Custom condition
    Custom(TokenStream),
}

impl Protocol {
    #[must_use] 
    pub fn mentions_role(&self, role: &Role) -> bool {
        match self {
            Protocol::Send {
                from,
                to,
                continuation,
                ..
            } => {
                from.matches_family(role)
                    || to.matches_family(role)
                    || continuation.mentions_role(role)
            }
            Protocol::Broadcast {
                from,
                to_all,
                continuation,
                ..
            } => {
                from.matches_family(role)
                    || to_all.iter().any(|r| r.matches_family(role))
                    || continuation.mentions_role(role)
            }
            Protocol::Choice { role: r, branches, .. } => {
                r.matches_family(role) || branches.iter().any(|b| b.protocol.mentions_role(role))
            }
            Protocol::Loop { body, .. } => body.mentions_role(role),
            Protocol::Parallel { protocols } => protocols.iter().any(|p| p.mentions_role(role)),
            Protocol::Rec { body, .. } => body.mentions_role(role),
            Protocol::Var(_) | Protocol::End => false,
        }
    }

    pub(crate) fn validate(&self, roles: &[Role]) -> Result<(), ValidationError> {
        // Helper to check if a role instance matches any declared role family
        let role_is_declared = |r: &Role| roles.iter().any(|declared| r.matches_family(declared));

        match self {
            Protocol::Send {
                from,
                to,
                continuation,
                ..
            } => {
                if !role_is_declared(from) {
                    return Err(ValidationError::UndefinedRole(from.name.to_string()));
                }
                if !role_is_declared(to) {
                    return Err(ValidationError::UndefinedRole(to.name.to_string()));
                }
                continuation.validate(roles)
            }
            Protocol::Broadcast {
                from,
                to_all,
                continuation,
                ..
            } => {
                if !role_is_declared(from) {
                    return Err(ValidationError::UndefinedRole(from.name.to_string()));
                }
                for to in to_all {
                    if !role_is_declared(to) {
                        return Err(ValidationError::UndefinedRole(to.name.to_string()));
                    }
                }
                continuation.validate(roles)
            }
            Protocol::Choice { role, branches, .. } => {
                if !role_is_declared(role) {
                    return Err(ValidationError::UndefinedRole(role.name.to_string()));
                }
                // Validate each branch starts with the choosing role sending
                for branch in branches {
                    if let Protocol::Send { from, .. } = &branch.protocol {
                        if from != role {
                            return Err(ValidationError::InvalidChoice(role.name.to_string()));
                        }
                    } else {
                        return Err(ValidationError::InvalidChoice(role.name.to_string()));
                    }
                }
                Ok(())
            }
            Protocol::Loop { body, .. } => body.validate(roles),
            Protocol::Parallel { protocols } => {
                for p in protocols {
                    p.validate(roles)?;
                }
                Ok(())
            }
            Protocol::Rec { body, .. } => body.validate(roles),
            Protocol::Var(_) | Protocol::End => Ok(()),
        }
    }

    /// Get statement-level annotations for this protocol node
    pub fn get_annotations(&self) -> &HashMap<String, String> {
        match self {
            Protocol::Send { annotations, .. } => annotations,
            Protocol::Broadcast { annotations, .. } => annotations,
            Protocol::Choice { annotations, .. } => annotations,
            Protocol::Loop { .. } | Protocol::Parallel { .. } | Protocol::Rec { .. } | Protocol::Var(_) | Protocol::End => {
                // Return empty map for protocol nodes that don't have annotations yet
                static EMPTY: std::sync::LazyLock<HashMap<String, String>> = std::sync::LazyLock::new(HashMap::new);
                &EMPTY
            }
        }
    }

    /// Get a specific annotation value
    pub fn get_annotation(&self, key: &str) -> Option<&String> {
        self.get_annotations().get(key)
    }

    /// Check if this protocol node has a specific annotation
    pub fn has_annotation(&self, key: &str) -> bool {
        self.get_annotations().contains_key(key)
    }

    /// Get from-role annotations for Send/Broadcast statements
    pub fn get_from_annotations(&self) -> Option<&HashMap<String, String>> {
        match self {
            Protocol::Send { from_annotations, .. } => Some(from_annotations),
            Protocol::Broadcast { from_annotations, .. } => Some(from_annotations),
            _ => None,
        }
    }

    /// Get to-role annotations for Send statements  
    pub fn get_to_annotations(&self) -> Option<&HashMap<String, String>> {
        match self {
            Protocol::Send { to_annotations, .. } => Some(to_annotations),
            _ => None,
        }
    }

    /// Get mutable reference to annotations for modification
    pub fn get_annotations_mut(&mut self) -> Option<&mut HashMap<String, String>> {
        match self {
            Protocol::Send { annotations, .. } => Some(annotations),
            Protocol::Broadcast { annotations, .. } => Some(annotations),
            Protocol::Choice { annotations, .. } => Some(annotations),
            Protocol::Loop { .. } | Protocol::Parallel { .. } | Protocol::Rec { .. } | Protocol::Var(_) | Protocol::End => None,
        }
    }

    /// Get mutable reference to from-role annotations
    pub fn get_from_annotations_mut(&mut self) -> Option<&mut HashMap<String, String>> {
        match self {
            Protocol::Send { from_annotations, .. } => Some(from_annotations),
            Protocol::Broadcast { from_annotations, .. } => Some(from_annotations),
            _ => None,
        }
    }

    /// Get mutable reference to to-role annotations  
    pub fn get_to_annotations_mut(&mut self) -> Option<&mut HashMap<String, String>> {
        match self {
            Protocol::Send { to_annotations, .. } => Some(to_annotations),
            _ => None,
        }
    }

    /// Set a statement-level annotation
    pub fn set_annotation(&mut self, key: String, value: String) -> bool {
        if let Some(annotations) = self.get_annotations_mut() {
            annotations.insert(key, value);
            true
        } else {
            false
        }
    }

    /// Remove a statement-level annotation
    pub fn remove_annotation(&mut self, key: &str) -> Option<String> {
        self.get_annotations_mut()?.remove(key)
    }

    /// Set a from-role annotation
    pub fn set_from_annotation(&mut self, key: String, value: String) -> bool {
        if let Some(annotations) = self.get_from_annotations_mut() {
            annotations.insert(key, value);
            true
        } else {
            false
        }
    }

    /// Set a to-role annotation
    pub fn set_to_annotation(&mut self, key: String, value: String) -> bool {
        if let Some(annotations) = self.get_to_annotations_mut() {
            annotations.insert(key, value);
            true
        } else {
            false
        }
    }

    /// Remove a from-role annotation
    pub fn remove_from_annotation(&mut self, key: &str) -> Option<String> {
        self.get_from_annotations_mut()?.remove(key)
    }

    /// Remove a to-role annotation
    pub fn remove_to_annotation(&mut self, key: &str) -> Option<String> {
        self.get_to_annotations_mut()?.remove(key)
    }

    /// Clear all annotations on this protocol node
    pub fn clear_annotations(&mut self) {
        if let Some(annotations) = self.get_annotations_mut() {
            annotations.clear();
        }
        if let Some(from_annotations) = self.get_from_annotations_mut() {
            from_annotations.clear();
        }
        if let Some(to_annotations) = self.get_to_annotations_mut() {
            to_annotations.clear();
        }
    }

    /// Get annotation as a specific type (e.g., integer, boolean)
    pub fn get_annotation_as<T>(&self, key: &str) -> Option<T>
    where
        T: std::str::FromStr,
    {
        self.get_annotation(key)?.parse().ok()
    }

    /// Get annotation as boolean (supports "true"/"false", "1"/"0", "yes"/"no") 
    pub fn get_annotation_as_bool(&self, key: &str) -> Option<bool> {
        let value = self.get_annotation(key)?;
        match value.to_lowercase().as_str() {
            "true" | "1" | "yes" | "on" => Some(true),
            "false" | "0" | "no" | "off" => Some(false),
            _ => None,
        }
    }

    /// Check if annotation value matches a specific string (case-insensitive)
    pub fn annotation_matches(&self, key: &str, expected: &str) -> bool {
        self.get_annotation(key)
            .map(|value| value.eq_ignore_ascii_case(expected))
            .unwrap_or(false)
    }

    /// Get all annotation keys
    pub fn annotation_keys(&self) -> Vec<&String> {
        self.get_annotations().keys().collect()
    }

    /// Check if any annotations are present
    pub fn has_any_annotations(&self) -> bool {
        !self.get_annotations().is_empty()
            || self.get_from_annotations().map_or(false, |a| !a.is_empty())
            || self.get_to_annotations().map_or(false, |a| !a.is_empty())
    }

    /// Count total number of annotations (statement + role annotations)
    pub fn annotation_count(&self) -> usize {
        self.get_annotations().len()
            + self.get_from_annotations().map_or(0, |a| a.len())
            + self.get_to_annotations().map_or(0, |a| a.len())
    }

    /// Merge annotations from another protocol node
    pub fn merge_annotations_from(&mut self, other: &Protocol) {
        // Merge statement annotations
        if let Some(self_annotations) = self.get_annotations_mut() {
            for (key, value) in other.get_annotations() {
                self_annotations.insert(key.clone(), value.clone());
            }
        }

        // Merge from-role annotations
        if let (Some(self_from), Some(other_from)) = (self.get_from_annotations_mut(), other.get_from_annotations()) {
            for (key, value) in other_from {
                self_from.insert(key.clone(), value.clone());
            }
        }

        // Merge to-role annotations
        if let (Some(self_to), Some(other_to)) = (self.get_to_annotations_mut(), other.get_to_annotations()) {
            for (key, value) in other_to {
                self_to.insert(key.clone(), value.clone());
            }
        }
    }

    /// Filter annotations by key prefix
    pub fn get_annotations_with_prefix(&self, prefix: &str) -> HashMap<String, String> {
        self.get_annotations()
            .iter()
            .filter(|(key, _)| key.starts_with(prefix))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }

    /// Validate that required annotations are present
    pub fn validate_required_annotations(&self, required_keys: &[&str]) -> Result<(), Vec<String>> {
        let missing: Vec<String> = required_keys
            .iter()
            .filter(|&key| !self.has_annotation(key))
            .map(|&key| key.to_string())
            .collect();

        if missing.is_empty() {
            Ok(())
        } else {
            Err(missing)
        }
    }

    /// Collect all protocol nodes that have a specific annotation (recursive traversal)
    pub fn collect_nodes_with_annotation<'a>(&'a self, key: &str, nodes: &mut Vec<&'a Protocol>) {
        if self.has_annotation(key) {
            nodes.push(self);
        }

        // Recursively traverse protocol structure
        match self {
            Protocol::Send { continuation, .. } => {
                continuation.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Broadcast { continuation, .. } => {
                continuation.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    branch.protocol.collect_nodes_with_annotation(key, nodes);
                }
            }
            Protocol::Loop { body, .. } => {
                body.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    protocol.collect_nodes_with_annotation(key, nodes);
                }
            }
            Protocol::Rec { body, .. } => {
                body.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes - no further traversal needed
            }
        }
    }

    /// Collect all protocol nodes that have a specific annotation with a specific value
    pub fn collect_nodes_with_annotation_value<'a>(&'a self, key: &str, value: &str, nodes: &mut Vec<&'a Protocol>) {
        if self.annotation_matches(key, value) {
            nodes.push(self);
        }

        // Recursively traverse protocol structure
        match self {
            Protocol::Send { continuation, .. } => {
                continuation.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Broadcast { continuation, .. } => {
                continuation.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    branch.protocol.collect_nodes_with_annotation_value(key, value, nodes);
                }
            }
            Protocol::Loop { body, .. } => {
                body.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    protocol.collect_nodes_with_annotation_value(key, value, nodes);
                }
            }
            Protocol::Rec { body, .. } => {
                body.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes - no further traversal needed
            }
        }
    }

    /// Count total annotations throughout the protocol tree (recursive)
    pub fn deep_annotation_count(&self) -> usize {
        let mut count = self.annotation_count();

        match self {
            Protocol::Send { continuation, .. } => {
                count += continuation.deep_annotation_count();
            }
            Protocol::Broadcast { continuation, .. } => {
                count += continuation.deep_annotation_count();
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    count += branch.protocol.deep_annotation_count();
                }
            }
            Protocol::Loop { body, .. } => {
                count += body.deep_annotation_count();
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    count += protocol.deep_annotation_count();
                }
            }
            Protocol::Rec { body, .. } => {
                count += body.deep_annotation_count();
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes - no additional annotations
            }
        }

        count
    }

    /// Apply a function to all protocol nodes that have annotations (visitor pattern)
    pub fn visit_annotated_nodes<F>(&self, f: &mut F)
    where
        F: FnMut(&Protocol),
    {
        if self.has_any_annotations() {
            f(self);
        }

        match self {
            Protocol::Send { continuation, .. } => {
                continuation.visit_annotated_nodes(f);
            }
            Protocol::Broadcast { continuation, .. } => {
                continuation.visit_annotated_nodes(f);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    branch.protocol.visit_annotated_nodes(f);
                }
            }
            Protocol::Loop { body, .. } => {
                body.visit_annotated_nodes(f);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    protocol.visit_annotated_nodes(f);
                }
            }
            Protocol::Rec { body, .. } => {
                body.visit_annotated_nodes(f);
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes
            }
        }
    }

    /// Apply a mutable function to all protocol nodes that have annotations
    pub fn visit_annotated_nodes_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Protocol),
    {
        if self.has_any_annotations() {
            f(self);
        }

        match self {
            Protocol::Send { continuation, .. } => {
                continuation.visit_annotated_nodes_mut(f);
            }
            Protocol::Broadcast { continuation, .. } => {
                continuation.visit_annotated_nodes_mut(f);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    branch.protocol.visit_annotated_nodes_mut(f);
                }
            }
            Protocol::Loop { body, .. } => {
                body.visit_annotated_nodes_mut(f);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    protocol.visit_annotated_nodes_mut(f);
                }
            }
            Protocol::Rec { body, .. } => {
                body.visit_annotated_nodes_mut(f);
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes
            }
        }
    }
}
