//! Runtime drivers.
//!
//! Drivers own target/runtime orchestration while semantic stepping stays in
//! the VM kernel path.

use cfg_if::cfg_if;

pub mod single_thread;

pub use single_thread::NativeSingleThreadDriver;

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        pub mod threaded;
        pub use threaded::NativeThreadedDriver;
    }
}

cfg_if! {
    if #[cfg(target_arch = "wasm32")] {
        /// Cooperative driver for WebAssembly targets.
        ///
        /// Uses the single-threaded driver since WASM lacks native threading support.
        pub type WasmCooperativeDriver = NativeSingleThreadDriver;
    }
}
