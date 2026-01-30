// Effect Handler Implementations
//
// This module contains concrete implementations of the ChoreoHandler trait
// for different execution environments:
//
// - in_memory: WASM-compatible handler using futures channels for testing
// - recording: Captures effects for verification
// - telltale: Session-typed Telltale integration (WASM-compatible via SimpleChannel)

pub mod in_memory;
pub mod recording;
pub mod telltale;

// Re-export handler types for convenience
pub use in_memory::InMemoryHandler;
pub use recording::{RecordedEvent, RecordingHandler};
pub use telltale::{TelltaleEndpoint, TelltaleHandler, TelltaleSession, SimpleChannel};
