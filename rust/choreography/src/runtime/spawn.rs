//! Runtime abstraction layer for cross-platform async execution
//!
//! Provides platform-specific implementations for spawning tasks and running futures.
//! Supports both native (Tokio) and WASM (wasm-bindgen-futures) targets.

use cfg_if::cfg_if;
use std::future::Future;

/// Marker trait for runtime implementations (not used as trait object)
pub trait AsyncRuntime: Send + Sync + 'static {}

/// Helper function to spawn a task using platform-specific runtime
///
/// On native targets, uses `tokio::spawn`.
/// On WASM targets, uses `wasm_bindgen_futures::spawn_local`.
pub fn spawn<F>(future: F)
where
    F: Future<Output = ()> + Send + 'static,
{
    cfg_if! {
        if #[cfg(target_arch = "wasm32")] {
            wasm_bindgen_futures::spawn_local(future);
        } else {
            tokio::spawn(future);
        }
    }
}

/// Helper function to spawn a local task using platform-specific runtime
///
/// On native targets, uses `tokio::task::spawn_local`.
/// On WASM targets, uses `wasm_bindgen_futures::spawn_local`.
pub fn spawn_local<F>(future: F)
where
    F: Future<Output = ()> + 'static,
{
    cfg_if! {
        if #[cfg(target_arch = "wasm32")] {
            wasm_bindgen_futures::spawn_local(future);
        } else {
            tokio::task::spawn_local(future);
        }
    }
}
