//! Choreographic Programming for Rumpsteak
//!
//! This crate provides a choreographic programming layer on top of Rumpsteak's
//! session types, enabling global protocol specification with automatic projection.
//!
//! The choreographic approach allows you to write distributed protocols from a
//! global viewpoint, with automatic generation of local session types for each
//! participant. This includes an effect handler system that decouples protocol
//! logic from transport implementation.

#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

pub mod ast;
pub mod compiler;
pub mod effects;
pub mod extensions;
pub mod runtime;
pub mod simulation;
pub mod testing;
pub mod tracing;

// Re-export runtime adapter types
pub use runtime::{
    ChoreographicAdapter, ChoreographicAdapterExt, Message, ProtocolContext, ProtocolOutput,
    RoleId as AdapterRoleId,
};

// Re-export main APIs
pub use ast::{Choreography, MessageType, Protocol, Role};
pub use compiler::generate_effects_protocol;
pub use compiler::{
    create_standard_extension_parser, ExtensionParseError, ExtensionParser, ExtensionParserBuilder,
    GrammarComposer, GrammarComposerBuilder, GrammarCompositionError,
};
pub use effects::middleware::{Metrics, Retry, Trace};
pub use effects::NoOpHandler;
pub use effects::{
    interpret, ChoreoHandler, ChoreoHandlerExt, ChoreographyError, Effect, Endpoint,
    InterpretResult, InterpreterState, Label, Program, ProgramMessage, Result, RoleId,
};
pub use effects::{InMemoryHandler, RecordedEvent, RecordingHandler};
pub use effects::{RumpsteakEndpoint, RumpsteakHandler, SimpleChannel};
pub use extensions::{
    CodegenContext, ExtensionRegistry, ExtensionValidationError, GrammarExtension, ParseContext,
    ParseError, ProjectionContext, ProtocolExtension, StatementParser,
};
pub use runtime::{spawn, spawn_local};

// Re-export simulation types for protocol testing
pub use simulation::{
    BlockedOn, Checkpoint, Clock, InMemoryTransport, MockClock, NullObserver, ProtocolEnvelope,
    ProtocolObserver, ProtocolStateMachine, RecordingObserver, Rng, SeededRng, SimulatedTransport,
    StepInput, StepOutput, SystemClock, TransportError,
};

// Re-export macros from rumpsteak-macros
pub use rumpsteak_aura_macros::choreography;

// High-level API functions for extension-aware compilation

/// Parse and generate choreography code with extension support
pub fn parse_and_generate_with_extensions(
    input: &str,
    extension_registry: &ExtensionRegistry,
) -> std::result::Result<proc_macro2::TokenStream, CompilationError> {
    use compiler::codegen::generate_choreography_code_with_extensions;
    use compiler::parser::parse_choreography_str_with_extensions;
    use compiler::projection::project;

    let (choreography, extensions) =
        parse_choreography_str_with_extensions(input, extension_registry)
            .map_err(CompilationError::ParseError)?;

    // Validate the choreography
    choreography
        .validate()
        .map_err(|e| CompilationError::ValidationError(e.to_string()))?;

    // Project to local types
    let mut local_types = Vec::new();
    for role in &choreography.roles {
        let local_type = project(&choreography, role)
            .map_err(|e| CompilationError::ProjectionError(e.to_string()))?;
        local_types.push((role.clone(), local_type));
    }

    // Generate code with extensions
    let generated_code =
        generate_choreography_code_with_extensions(&choreography, &local_types, &extensions);

    Ok(generated_code)
}

/// Convenience function for compiling choreography with built-in extensions
pub fn compile_choreography_with_extensions(
    input: &str,
) -> std::result::Result<proc_macro2::TokenStream, CompilationError> {
    let registry = ExtensionRegistry::with_builtin_extensions();
    parse_and_generate_with_extensions(input, &registry)
}

/// Parse choreography with extension support
pub fn parse_choreography_with_extensions(
    input: &str,
    extension_registry: &ExtensionRegistry,
) -> std::result::Result<(Choreography, Vec<Box<dyn ProtocolExtension>>), CompilationError> {
    use compiler::parser::parse_choreography_str_with_extensions;

    parse_choreography_str_with_extensions(input, extension_registry)
        .map_err(CompilationError::ParseError)
}

/// Compilation errors that can occur during choreography processing
#[derive(Debug, thiserror::Error)]
#[allow(clippy::enum_variant_names)]
pub enum CompilationError {
    #[error("Parse error: {0}")]
    ParseError(#[from] compiler::parser::ParseError),

    #[error("Validation error: {0}")]
    ValidationError(String),

    #[error("Projection error: {0}")]
    ProjectionError(String),

    #[error("Code generation error: {0}")]
    CodegenError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_structure() {
        // Test that main re-exports are available
        let _choreography: Option<Choreography> = None;
        let _protocol: Option<Protocol> = None;
        let _role: Option<Role> = None;
        let _message_type: Option<MessageType> = None;

        // Test effect system is available
        let _program: Option<Program<(), ()>> = None;
        let _result: Option<Result<()>> = None;
        let _label: Option<Label> = None;
    }

    #[test]
    fn test_free_algebra_integration() {
        use std::time::Duration;

        // Test that Program can be built using the free algebra API
        let program = Program::new()
            .send((), ())
            .recv::<()>(())
            .choose((), Label("test"))
            .offer(())
            .with_timeout((), Duration::from_millis(100), Program::new().end())
            .parallel(vec![Program::new().end()])
            .end();

        // Basic analysis should work
        assert_eq!(program.send_count(), 1);
        assert_eq!(program.recv_count(), 1);
        assert!(program.has_timeouts());
        assert!(program.has_parallel());
    }
}
