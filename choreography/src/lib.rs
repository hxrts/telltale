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
pub mod runtime;

// Re-export main APIs
pub use ast::{Choreography, MessageType, Protocol, Role};
pub use compiler::generate_effects_protocol;
pub use effects::middleware::{Metrics, Retry, Trace};
pub use effects::NoOpHandler;
pub use effects::{
    interpret, ChoreoHandler, ChoreoHandlerExt, ChoreographyError, Effect, Endpoint,
    InterpretResult, InterpreterState, Label, Program, ProgramMessage, Result, RoleId,
};
pub use effects::{InMemoryHandler, RecordedEvent, RecordingHandler};
pub use effects::{RumpsteakEndpoint, RumpsteakHandler, SimpleChannel};
pub use runtime::{spawn, spawn_local};

// Re-export macros from rumpsteak-macros
pub use rumpsteak_aura_macros::choreography;

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
