//! Abstract Syntax Tree for choreographic protocols
//!
//! This module defines the core AST types used to represent choreographic protocols,
//! including global protocols, local (projected) types, roles, and messages.

/// Choreography definitions (global protocols with metadata)
pub mod choreography;

/// Local types resulting from projection
pub mod local_type;

/// Message type definitions
pub mod message;

/// Protocol combinators (global protocol constructs)
pub mod protocol;

/// Role definitions
pub mod role;

/// Validation errors and utilities
pub mod validation;

// Re-export core AST types explicitly for clarity
pub use choreography::Choreography;
pub use local_type::LocalType;
pub use message::MessageType;
pub use protocol::{Branch, Condition, Protocol};
pub use role::{
    Role, RoleParam, RoleIndex, RoleRange, RangeExpr,
    RoleValidationError, RoleValidationResult, RoleBoundsChecker,
    MAX_ROLE_COUNT, MAX_ROLE_INDEX, MAX_RANGE_SIZE
};
pub use validation::ValidationError;
