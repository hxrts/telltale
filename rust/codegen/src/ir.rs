//! Intermediate Representation for Code Generation
//!
//! This module defines the IR used between parsing and code generation.
//! It decouples the session type representation from Rust-specific concerns.

use rumpsteak_types::{Label, LocalTypeR, PayloadSort};

/// Top-level IR for a complete protocol
#[derive(Debug, Clone)]
pub struct CodegenIR {
    /// Protocol name
    pub name: String,
    /// Protocol definition
    pub protocol: ProtocolIR,
}

/// Protocol-level IR
#[derive(Debug, Clone)]
pub struct ProtocolIR {
    /// All roles in the protocol
    pub roles: Vec<RoleIR>,
    /// All message types
    pub messages: Vec<MessageIR>,
}

/// Role-level IR
#[derive(Debug, Clone)]
pub struct RoleIR {
    /// Role name
    pub name: String,
    /// Local type for this role
    pub local_type: LocalTypeR,
    /// Channel partners
    pub partners: Vec<String>,
}

/// Message-level IR
#[derive(Debug, Clone)]
pub struct MessageIR {
    /// Message label
    pub label: Label,
    /// Whether this is a choice label
    pub is_choice: bool,
}

impl CodegenIR {
    /// Create a new CodegenIR
    pub fn new(name: impl Into<String>, protocol: ProtocolIR) -> Self {
        Self {
            name: name.into(),
            protocol,
        }
    }
}

impl ProtocolIR {
    /// Create a new empty protocol IR
    pub fn new() -> Self {
        Self {
            roles: Vec::new(),
            messages: Vec::new(),
        }
    }

    /// Add a role to the protocol
    pub fn add_role(&mut self, role: RoleIR) {
        self.roles.push(role);
    }

    /// Add a message to the protocol
    pub fn add_message(&mut self, message: MessageIR) {
        self.messages.push(message);
    }
}

impl Default for ProtocolIR {
    fn default() -> Self {
        Self::new()
    }
}

impl RoleIR {
    /// Create a new role IR
    pub fn new(name: impl Into<String>, local_type: LocalTypeR) -> Self {
        let name = name.into();
        let partners = local_type.partners();
        Self {
            name,
            local_type,
            partners,
        }
    }
}

impl MessageIR {
    /// Create a new message IR
    pub fn new(label: Label, is_choice: bool) -> Self {
        Self { label, is_choice }
    }

    /// Get the Rust type for this message's payload
    pub fn rust_type(&self) -> &'static str {
        match &self.label.sort {
            PayloadSort::Unit => "()",
            PayloadSort::Nat => "u64",
            PayloadSort::Bool => "bool",
            PayloadSort::String => "String",
            PayloadSort::Prod(_, _) => "/* tuple */",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_role_ir() {
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let role = RoleIR::new("A", lt);

        assert_eq!(role.name, "A");
        assert!(role.partners.contains(&"B".to_string()));
    }

    #[test]
    fn test_message_ir() {
        let msg = MessageIR::new(Label::with_sort("data", PayloadSort::Nat), false);
        assert_eq!(msg.rust_type(), "u64");
    }

    #[test]
    fn test_protocol_ir() {
        let mut protocol = ProtocolIR::new();
        let lt = LocalTypeR::End;
        protocol.add_role(RoleIR::new("A", lt));

        assert_eq!(protocol.roles.len(), 1);
    }
}
