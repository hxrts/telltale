//! Abstract Syntax Tree for choreographic protocols
//!
//! This module defines the core AST types used to represent choreographic protocols,
//! including global protocols, local (projected) types, roles, and messages.
//!
//! Core types (GlobalType, LocalTypeR, Label, PayloadSort) are re-exported from
//! `rumpsteak-types` for Lean correspondence. Extended types (LocalType, Protocol)
//! are defined here for DSL-specific features.

/// Choreography definitions (global protocols with metadata)
pub mod choreography;

/// Conversion utilities between DSL types and theory types
pub mod convert;

/// Global types for multiparty session type protocols (extended, uses rumpsteak-types)
pub mod global_type;

/// Local types resulting from projection (extended, uses rumpsteak-types)
pub mod local_type;

/// Message type definitions
pub mod message;

/// Protocol combinators (global protocol constructs)
pub mod protocol;

/// Role definitions
pub mod role;

/// Validation errors and utilities
pub mod validation;

// Re-export core types from rumpsteak-types for Lean correspondence
pub use rumpsteak_types::{
    Action, GlobalType as GlobalTypeCore, Label, LocalAction, LocalTypeR, PayloadSort,
};

// Re-export DSL-specific types
pub use choreography::Choreography;
pub use global_type::GlobalType; // Extended GlobalType with DSL features
pub use local_type::LocalType; // Extended LocalType for code generation
pub use message::MessageType;
pub use protocol::{Branch, Condition, Protocol};
pub use role::{
    RangeExpr, Role, RoleBoundsChecker, RoleIndex, RoleParam, RoleRange, RoleValidationError,
    RoleValidationResult, MAX_RANGE_SIZE, MAX_ROLE_COUNT, MAX_ROLE_INDEX,
};
pub use validation::ValidationError;

// Re-export conversion utilities
pub use convert::{
    choreography_to_global, local_to_local_r, local_types_equivalent, protocol_to_global,
    ConversionError, ConversionResult,
};
