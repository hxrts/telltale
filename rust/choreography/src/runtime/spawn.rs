//! Runtime abstraction layer for cross-platform async execution
//!
//! Provides platform-specific implementations for spawning tasks and running futures.
//! Supports both native (Tokio) and WASM (wasm-bindgen-futures) targets.

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
    #[cfg(not(target_arch = "wasm32"))]
    {
        tokio::spawn(future);
    }

    #[cfg(target_arch = "wasm32")]
    {
        wasm_bindgen_futures::spawn_local(future);
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
    #[cfg(not(target_arch = "wasm32"))]
    {
        tokio::task::spawn_local(future);
    }

    #[cfg(target_arch = "wasm32")]
    {
        wasm_bindgen_futures::spawn_local(future);
    }
}
