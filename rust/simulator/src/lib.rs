//! Lightweight simulation engine for Telltale choreographic protocols.
//!
//! Executes projected local types as state machines with pluggable effect
//! handlers. Supports multiple concurrent choreographies sharing a
//! single-threaded deterministic scheduler.

pub mod analysis;
pub mod continuum;
pub mod hamiltonian;
pub mod ising;
pub mod material;
pub mod scenario;
pub mod scheduler;
pub mod trace;
#[cfg(feature = "vm")]
pub mod vm_runner;

pub use material::MaterialParams;
