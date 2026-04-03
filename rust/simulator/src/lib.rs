//! Protocol-machine-backed simulation engine for Telltale choreographic protocols.
//!
//! Executes projected local types through the protocol machine with pluggable
//! effect handlers.

// Simulator uses explicit Result-based error propagation in runtime paths.
#![allow(clippy::missing_panics_doc)]
// Simulator uses u64/usize conversions for tick/index interop with the protocol machine.
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
pub mod contracts;
pub mod distributed;
#[doc(hidden)]
pub mod execution;
pub mod fault;
/// Generated effect-family simulator helpers and scenario surfaces.
pub mod generated;
pub mod harness;
pub mod material;
pub mod material_handlers;
pub mod network;
pub mod presets;
pub mod property;
pub mod rng;
pub mod runner;
pub mod scenario;
pub mod trace;
mod value_conv;

pub use contracts::{
    assert_contracts, evaluate_contracts, ContractCheckConfig, ContractCheckReport,
};
pub use harness::{
    derive_initial_states, derive_initial_states_for_model, DirectAdapter, HarnessConfig,
    HarnessSpec, HostAdapter, MaterialAdapter, SimulationHarness,
};
pub use material::{MaterialModel, MaterialParams};
pub use material_handlers::{
    handler_from_material, handler_from_model, ContinuumFieldHandler, HamiltonianHandler,
    IsingHandler,
};
pub use network::{NetworkConfig, NetworkModel};
pub use property::{Property, PropertyMonitor};
pub use rng::SimRng;
pub use telltale_machine::model::effects::EffectHandler;
