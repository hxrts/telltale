#![allow(clippy::type_complexity)]

//! External Demo - Full Rumpsteak-Aura Integration
//!
//! This crate demonstrates how external projects integrate with rumpsteak-aura
//! and the choreography DSL. It serves as a reference implementation for
//! third-party crates that want to use the MPST library.
//!
//! # Architecture
//!
//! ```text
//! external-demo/              ← Regular crate (re-exports rumpsteak-aura)
//! external-demo-macros/       ← Proc-macro crate (custom macros)
//! ```
//!
//! # Usage
//!
//! ```ignore
//! use external_demo::prelude::*;
//!
//! // Define choreography using the macro
//! choreography! {
//!     #[namespace = "my_protocol"]
//!     choreography Example {
//!         roles: Alice, Bob;
//!
//!         Alice -> Bob: Request;
//!         Bob -> Alice: Response;
//!     }
//! }
//! ```

// Re-export the choreography macro
pub use external_demo_macros::choreography;

// Prelude module for convenient imports
pub mod prelude {
    // Core session types and macros from rumpsteak-aura
    pub use rumpsteak_aura::{
        channel::Bidirectional, session, try_session, Branch, End, Message, Receive, Role, Roles,
        Select, Send,
    };

    // Choreography types
    pub use rumpsteak_aura_choreography::{
        ast::{Choreography, LocalType, MessageType, Protocol, Role as ChoreographyRole},
        compiler::{parser::parse_choreography_str_with_extensions, GrammarComposer},
        extensions::{ExtensionRegistry, ProtocolExtension},
        runtime::{ChoreographicAdapter, ProtocolContext, RoleId},
    };

    // Re-export futures for async support
    pub use futures::{channel::mpsc, executor, try_join};

    // Re-export our custom macro
    pub use external_demo_macros::choreography;
}

// Extension definitions for Aura
pub mod aura_extensions;

// Re-export aura extensions
pub use aura_extensions::{create_aura_extension_registry, register_aura_extensions};

// Re-export specific types to avoid ambiguity
// Users should use prelude::* or import from these explicitly

/// Core rumpsteak-aura types for session type programming
pub mod session {
    pub use rumpsteak_aura::{
        channel, session, try_session, Branch, End, Message, Receive, Role, Roles, Select, Send,
    };
}

/// Choreography DSL types and tools
pub mod choreography_dsl {
    pub use rumpsteak_aura_choreography::{
        ast, compiler, extensions, runtime, simulation, testing, tracing,
    };
}

/// Initialize the Aura extension system
///
/// This function configures the extension registry with Aura-specific
/// grammar extensions and statement parsers.
pub fn init_aura_extensions() -> rumpsteak_aura_choreography::extensions::ExtensionRegistry {
    let mut registry = rumpsteak_aura_choreography::extensions::ExtensionRegistry::new();
    aura_extensions::register_aura_extensions(&mut registry);
    registry
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extension_registry_initialization() {
        let registry = init_aura_extensions();
        // Verify extensions are registered
        assert!(registry.grammar_extensions().count() > 0);
    }

    #[test]
    fn test_prelude_imports() {
        // Verify prelude provides necessary types
        use crate::prelude::*;
        let _registry = ExtensionRegistry::new();
    }
}
