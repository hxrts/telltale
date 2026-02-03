//! VM-backed simulation engine for Telltale choreographic protocols.
//!
//! Executes projected local types through the bytecode VM with pluggable
//! effect handlers.

pub mod analysis;
pub mod checkpoint;
pub mod continuum;
pub mod distributed;
pub mod fault;
pub mod hamiltonian;
pub mod ising;
pub mod material;
pub mod network;
pub mod property;
pub mod rng;
pub mod runner;
pub mod scenario;
pub mod trace;
mod value_conv;

pub use material::MaterialParams;
pub use network::{NetworkConfig, NetworkModel};
pub use property::{Property, PropertyMonitor};
pub use rng::SimRng;
pub use telltale_vm::effect::EffectHandler;
