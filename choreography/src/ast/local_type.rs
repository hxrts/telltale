// Local session types after projection

use super::{Role, MessageType};
use proc_macro2::Ident;

/// Local session type after projection
#[derive(Debug, Clone)]
pub enum LocalType {
    /// Send a message
    Send {
        to: Role,
        message: MessageType,
        continuation: Box<LocalType>,
    },

    /// Receive a message
    Receive {
        from: Role,
        message: MessageType,
        continuation: Box<LocalType>,
    },

    /// Make a choice (select)
    Select {
        to: Role,
        branches: Vec<(Ident, LocalType)>,
    },

    /// Receive a choice (branch)
    Branch {
        from: Role,
        branches: Vec<(Ident, LocalType)>,
    },

    /// Local choice (decision without communication)
    LocalChoice { branches: Vec<(Ident, LocalType)> },

    /// Loop construct
    Loop {
        condition: Option<super::protocol::Condition>,
        body: Box<LocalType>,
    },

    /// Recursive type
    Rec { label: Ident, body: Box<LocalType> },

    /// Variable (reference to recursive type)
    Var(Ident),

    /// Type termination
    End,
}

impl LocalType {
    /// Check if this type is well-formed
    #[must_use] 
    pub fn is_well_formed(&self) -> bool {
        self.check_well_formed(&mut vec![])
    }

    fn check_well_formed(&self, rec_vars: &mut Vec<Ident>) -> bool {
        match self {
            LocalType::Send { continuation, .. } => continuation.check_well_formed(rec_vars),
            LocalType::Receive { continuation, .. } => continuation.check_well_formed(rec_vars),
            LocalType::Select { branches, .. } => branches
                .iter()
                .all(|(_, ty)| ty.check_well_formed(rec_vars)),
            LocalType::Branch { branches, .. } => branches
                .iter()
                .all(|(_, ty)| ty.check_well_formed(rec_vars)),
            LocalType::LocalChoice { branches } => branches
                .iter()
                .all(|(_, ty)| ty.check_well_formed(rec_vars)),
            LocalType::Loop { body, .. } => body.check_well_formed(rec_vars),
            LocalType::Rec { label, body } => {
                rec_vars.push(label.clone());
                let result = body.check_well_formed(rec_vars);
                rec_vars.pop();
                result
            }
            LocalType::Var(label) => rec_vars.contains(label),
            LocalType::End => true,
        }
    }
}
