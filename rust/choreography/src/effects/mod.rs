//! Effect handler system for choreographic programming
//!
//! This module provides the effect handler abstraction that decouples protocol
//! logic from transport implementation, enabling testable and composable protocols.
//!
//! The system uses a free algebra approach where choreographic programs are
//! represented as data structures that can be analyzed, transformed, and interpreted.

pub mod algebra;
pub mod extension;
pub mod handler;
pub mod handlers;
pub mod interpreter;
pub mod middleware;
pub mod registry;

// Re-export core effect system types explicitly
pub use algebra::{
    Effect, InterpretResult, InterpreterState, Program, ProgramBuilder, ProgramError,
    ProgramMessage,
};
pub use extension::{ExtensionEffect, ExtensionError};
pub use handler::{
    ChoreoHandler, ChoreoHandlerExt, ChoreoResult, ChoreographyError, ContextExt, Endpoint,
    LabelId, MessageTag, NoOpHandler, RoleId,
};
pub use interpreter::{interpret, interpret_extensible};
pub use registry::{ExtensibleHandler, ExtensionRegistry};

// Re-export handler implementations for convenience
pub use handlers::{InMemoryHandler, RecordedEvent, RecordingHandler};
pub use handlers::{SimpleChannel, TelltaleEndpoint, TelltaleHandler, TelltaleSession};

// Re-export middleware for convenience
pub use middleware::{Metrics, Retry, Trace};

#[cfg(feature = "test-utils")]
pub use middleware::FaultInjection;
