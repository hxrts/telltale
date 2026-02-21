//! VM-backed simulation engine for Telltale choreographic protocols.
//!
//! Executes projected local types through the bytecode VM with pluggable
//! effect handlers.

// Simulator middleware uses internal Mutex locks that can panic if poisoned.
// This is intentional as poisoned locks indicate a prior panic in simulation.
#![allow(clippy::missing_panics_doc)]
// Simulator uses u64/usize conversions for tick/index interop with the VM.
#![allow(
    clippy::as_conversions,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss
)]
// Property monitor has complex evaluation logic by design.
#![allow(clippy::cognitive_complexity, clippy::too_many_lines)]
// Internal simulator errors are self-documenting via Result types.
#![allow(clippy::missing_errors_doc)]

pub mod analysis;
pub mod checkpoint;
pub mod distributed;
pub mod fault;
pub mod material;
pub mod material_handlers;
pub mod network;
pub mod property;
pub mod rng;
pub mod runner;
pub mod scenario;
pub mod trace;
mod value_conv;

pub use material::MaterialParams;
pub use material_handlers::{
    handler_from_material, ContinuumFieldHandler, HamiltonianHandler, IsingHandler,
};
pub use network::{NetworkConfig, NetworkModel};
pub use property::{Property, PropertyMonitor};
pub use rng::SimRng;
pub use telltale_vm::effect::EffectHandler;
