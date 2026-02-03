//! Value Types for Session Type Payloads
//!
//! Shared `ValType` definition matching Lean's `SessionTypes.ValType`.
//! Represents the types of values carried in messages.

use serde::{Deserialize, Serialize};

/// Value types for message payloads in session types.
///
/// Corresponds to Lean's `SessionTypes.ValType`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ValType {
    Unit,
    Bool,
    Nat,
    String,
    Prod(Box<ValType>, Box<ValType>),
    /// Channel endpoint type (session id, role)
    Chan {
        sid: usize,
        role: std::string::String,
    },
}
