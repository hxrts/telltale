//! Code Generation from Session Types to Rust
//!
//! This crate generates Rust code from session type definitions.
//! It produces type-safe protocol implementations including:
//!
//! - Session types (Send, Recv, Choose, Offer)
//! - Role structs with channel parameters
//! - Message enums and structs
//! - Protocol runners
//! - Typed runner wrappers
//! - Effects-based protocols
//! - Concurrency control utilities
//!
//! # Architecture
//!
//! ```text
//! LocalTypeR ──► CodegenIR ──► TokenStream ──► Rust Code
//! ```
//!
//! The intermediate representation (IR) decouples parsing from code generation.

pub mod ir;
pub mod rust;
pub mod templates;

// Core IR types
pub use ir::{CodegenIR, MessageIR, ProtocolIR, RoleIR};

// Session type and protocol generation
pub use rust::{generate_messages, generate_protocol, generate_role, generate_session_type};

// Runner generation
pub use rust::{
    generate_all_runners, generate_execute_as, generate_output_types, generate_role_enum,
    generate_runner_fn,
};

// Typed runner generation
pub use rust::{
    extract_role_messages, generate_all_typed_runners, generate_typed_runner, MessageDirection,
    RoleMessageInfo, SerializationConfig, SerializationFormat,
};

// Effects-based generation
pub use rust::{generate_effects_protocol, interpret, Handler, InterpretResult, Label, Program};

// Concurrency control
pub use rust::{
    generate_batch_recv, generate_batch_send, generate_broadcast, generate_collection,
    generate_ordered_collection, generate_parallel_broadcast, generate_sequential_broadcast,
    generate_unordered_collection, BatchConfig, BroadcastMode, CollectionMode,
    ProtocolConcurrencyConfig, StatementConcurrencyConfig,
};
