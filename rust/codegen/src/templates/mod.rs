//! Protocol Templates
//!
//! This module provides template code for common protocol patterns.
//! Templates can be used as starting points for generating protocol implementations.
//!
//! # Available Templates
//!
//! - `protocol` - Basic protocol module structure
//! - `role` - Role struct with session type
//! - `message` - Message type definitions
//! - `runner` - Protocol runner boilerplate

mod message;
mod protocol;
mod role;
mod runner;

pub use message::{MessageEnumTemplate, MessageTemplate};
pub use protocol::ProtocolTemplate;
pub use role::RoleTemplate;
pub use runner::{ExecuteAsTemplate, RunnerTemplate};

use proc_macro2::TokenStream;

/// A template that can generate code.
pub trait Template {
    /// Generate the code for this template.
    fn generate(&self) -> TokenStream;

    /// Get the template name.
    fn name(&self) -> &str;

    /// Get template description.
    fn description(&self) -> &str;
}
