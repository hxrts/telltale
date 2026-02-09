//! Runtime drivers.
//!
//! Drivers own target/runtime orchestration while semantic stepping stays in
//! the VM kernel path.

pub mod single_thread;

#[cfg(feature = "multi-thread")]
pub mod threaded;

pub use single_thread::NativeSingleThreadDriver;

#[cfg(feature = "multi-thread")]
pub use threaded::NativeThreadedDriver;

#[cfg(target_arch = "wasm32")]
pub type WasmCooperativeDriver = NativeSingleThreadDriver;
