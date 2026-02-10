//! Simulation primitives for choreographic protocols
//!
//! This module provides building blocks for protocol simulation, testing,
//! and integration with external simulators like aura-simulator.
//!
//! # Overview
//!
//! The simulation module provides:
//!
//! - **Deterministic execution**: `Clock` and `Rng` traits for reproducible runs
//! - **State machines**: `ProtocolStateMachine` for step-by-step execution
//! - **Transport abstraction**: `SimulatedTransport` for custom message delivery
//! - **Event observation**: `ProtocolObserver` for monitoring protocol execution
//! - **Message envelopes**: `ProtocolEnvelope` for structured message passing
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    Simulator / Test Harness                  │
//! └─────────────────────────────────────────────────────────────┘
//!                              │
//!           ┌──────────────────┼──────────────────┐
//!           │                  │                  │
//!           ▼                  ▼                  ▼
//!    ┌─────────────┐   ┌─────────────┐   ┌─────────────┐
//!    │   Clock     │   │    Rng      │   │  Observer   │
//!    │   Trait     │   │    Trait    │   │    Trait    │
//!    └─────────────┘   └─────────────┘   └─────────────┘
//!                              │
//!                              ▼
//!    ┌─────────────────────────────────────────────────────────┐
//!    │              ProtocolStateMachine                        │
//!    │  blocked_on() -> BlockedOn                               │
//!    │  step(input) -> StepOutput                               │
//!    │  checkpoint() / restore()                                │
//!    └─────────────────────────────────────────────────────────┘
//!                              │
//!                              ▼
//!    ┌─────────────────────────────────────────────────────────┐
//!    │              SimulatedTransport                          │
//!    │  send(to, envelope) -> Result                           │
//!    │  recv(from) -> Result<Envelope>                         │
//!    └─────────────────────────────────────────────────────────┘
//! ```

pub mod clock;
pub mod envelope;
pub mod observer;
pub mod state_machine;
pub mod transport;

// Re-export main types
pub use clock::{Clock, MockClock, Rng, SeededRng, WallClock};
pub use envelope::ProtocolEnvelope;
pub use observer::{NullObserver, ProtocolObserver, RecordingObserver};
pub use state_machine::{BlockedOn, Checkpoint, ProtocolStateMachine, StepInput, StepOutput};
pub use transport::{
    AsyncSimulatedTransport, InMemoryTransport, SimulatedTransport, TransportError,
};
