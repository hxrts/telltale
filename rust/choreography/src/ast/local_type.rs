//! Local Session Types for Multiparty Protocols
//!
//! This module defines local types that describe protocols from a single participant's
//! perspective. Local types are obtained by projecting global types onto specific roles.
//!
//! Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//!
//! # Correspondence with Lean
//!
//! The core `LocalTypeR` is re-exported from `telltale-types` and mirrors
//! `lean/Telltale/Protocol/LocalTypeR.lean`.
//!
//! The extended `LocalType` adds constructs for code generation (loops, timeouts, etc.).

// Re-export LocalTypeR from telltale-types
pub use telltale_types::LocalTypeR;

use super::{MessageType, Role};
use proc_macro2::Ident;
use std::time::Duration;

/// Extended local session type for code generation.
///
/// This enum extends `LocalTypeR` with additional constructs used during
/// code generation, such as loops, timeouts, and local choice.
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

    /// Timeout wrapper for protocol extensions
    Timeout {
        duration: Duration,
        body: Box<LocalType>,
    },

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
            LocalType::Timeout { body, .. } => body.check_well_formed(rec_vars),
            LocalType::End => true,
        }
    }

    /// Count the depth of a local type
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            LocalType::End | LocalType::Var(_) => 0,
            LocalType::Send { continuation, .. } | LocalType::Receive { continuation, .. } => {
                1 + continuation.depth()
            }
            LocalType::Select { branches, .. }
            | LocalType::Branch { branches, .. }
            | LocalType::LocalChoice { branches } => {
                1 + branches.iter().map(|(_, t)| t.depth()).max().unwrap_or(0)
            }
            LocalType::Loop { body, .. }
            | LocalType::Rec { body, .. }
            | LocalType::Timeout { body, .. } => 1 + body.depth(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::{Label, PayloadSort};

    #[test]
    fn test_simple_local_type() {
        // !B{msg.end}
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        assert!(lt.well_formed());
        assert_eq!(lt.partners().len(), 1);
        assert!(lt.mentions_partner("B"));
    }

    #[test]
    fn test_recursive_local_type() {
        // μt. !B{msg.t}
        let lt = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        assert!(lt.well_formed());
        assert!(lt.all_vars_bound());
    }

    #[test]
    fn test_dual() {
        // !B{msg.end} dual is ?B{msg.end}
        let send = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let recv = send.dual();

        match recv {
            LocalTypeR::Recv { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
            }
            _ => panic!("Expected Recv"),
        }
    }

    #[test]
    fn test_unfold() {
        // μt. !B{msg.t} unfolds to !B{msg.(μt. !B{msg.t})}
        let lt = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        let unfolded = lt.unfold();

        match unfolded {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert!(matches!(branches[0].2, LocalTypeR::Mu { .. }));
            }
            _ => panic!("Expected Send after unfold"),
        }
    }

    #[test]
    fn test_substitute() {
        let lt = LocalTypeR::var("t");
        let replacement = LocalTypeR::End;
        assert_eq!(lt.substitute("t", &replacement), LocalTypeR::End);
        assert_eq!(lt.substitute("s", &replacement), LocalTypeR::var("t"));
    }

    #[test]
    fn test_unbound_variable() {
        // !B{msg.t} where t is unbound
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t"));
        assert!(!lt.all_vars_bound());
        assert!(!lt.well_formed());
    }

    #[test]
    fn test_guarded() {
        // μt. t is not guarded
        let unguarded = LocalTypeR::mu("t", LocalTypeR::var("t"));
        assert!(!unguarded.is_guarded());

        // μt. !B{msg.t} is guarded
        let guarded = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("t")),
        );
        assert!(guarded.is_guarded());
    }

    #[test]
    fn test_free_vars() {
        // μt. !B{msg.s} has free var s
        let lt = LocalTypeR::mu(
            "t",
            LocalTypeR::send("B", Label::new("msg"), LocalTypeR::var("s")),
        );
        let free = lt.free_vars();
        assert_eq!(free, vec!["s"]);
    }

    #[test]
    fn test_choice_with_payload() {
        let branches = vec![
            (
                Label::with_sort("accept", PayloadSort::Bool),
                None,
                LocalTypeR::End,
            ),
            (Label::with_sort("data", PayloadSort::Nat), None, LocalTypeR::End),
        ];
        let lt = LocalTypeR::recv_choice("A", branches);
        assert!(lt.well_formed());
        assert_eq!(lt.labels(), vec!["accept", "data"]);
    }

    #[test]
    fn test_depth() {
        let lt = LocalTypeR::send(
            "B",
            Label::new("outer"),
            LocalTypeR::send("C", Label::new("inner"), LocalTypeR::End),
        );
        assert_eq!(lt.depth(), 2);
    }

    #[test]
    fn test_extended_local_type() {
        use proc_macro2::Span;

        let lt = LocalType::Rec {
            label: Ident::new("loop1", Span::call_site()),
            body: Box::new(LocalType::End),
        };
        assert!(lt.is_well_formed());
    }
}
