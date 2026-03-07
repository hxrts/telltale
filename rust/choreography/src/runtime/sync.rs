//! Platform-specific synchronization primitives
//!
//! This module provides cross-platform abstractions for synchronization primitives
//! that work on both native (tokio) and WASM targets.
//!
//! On native targets, we use tokio's async synchronization primitives.
//! On WASM, we use std::sync primitives (which work because WASM is single-threaded)
//! and futures::channel for message passing.

use cfg_if::cfg_if;

cfg_if! {
    if #[cfg(target_arch = "wasm32")] {
        pub use futures::channel::mpsc;
        pub use std::sync::{Mutex, RwLock};
    } else {
        pub use tokio::sync::{mpsc, Mutex, RwLock};
    }
}

/// Helper macro for acquiring a read lock.
///
/// On native targets, this awaits the async lock.
/// On WASM, this uses the blocking (but single-threaded safe) lock.
///
/// # Lock Poisoning (WASM only)
///
/// On WASM targets, lock poisoning is recovered by taking the inner guard.
/// This avoids panic-only behavior in adapter/runtime helpers.
///
/// # Example
///
/// ```ignore
/// let guard = read_lock!(self.data);
/// println!("{:?}", *guard);
/// ```
#[macro_export]
macro_rules! read_lock {
    ($lock:expr) => {{
        cfg_if::cfg_if! {
            if #[cfg(target_arch = "wasm32")] {
                match $lock.read() {
                    Ok(guard) => guard,
                    Err(poisoned) => poisoned.into_inner(),
                }
            } else {
                $lock.read().await
            }
        }
    }};
}

/// Helper macro for acquiring a write lock.
///
/// On native targets, this awaits the async lock.
/// On WASM, this uses the blocking (but single-threaded safe) lock.
///
/// # Lock Poisoning (WASM only)
///
/// On WASM targets, lock poisoning is recovered by taking the inner guard.
/// This avoids panic-only behavior in adapter/runtime helpers.
///
/// # Example
///
/// ```ignore
/// let mut guard = write_lock!(self.data);
/// *guard = new_value;
/// ```
#[macro_export]
macro_rules! write_lock {
    ($lock:expr) => {{
        cfg_if::cfg_if! {
            if #[cfg(target_arch = "wasm32")] {
                match $lock.write() {
                    Ok(guard) => guard,
                    Err(poisoned) => poisoned.into_inner(),
                }
            } else {
                $lock.write().await
            }
        }
    }};
}

/// Helper macro for acquiring a mutex lock.
///
/// On native targets, this awaits the async lock.
/// On WASM, this uses the blocking (but single-threaded safe) lock.
///
/// # Lock Poisoning (WASM only)
///
/// On WASM targets, lock poisoning is recovered by taking the inner guard.
/// This avoids panic-only behavior in adapter/runtime helpers.
///
/// # Example
///
/// ```ignore
/// let guard = mutex_lock!(self.state);
/// process(&*guard);
/// ```
#[macro_export]
macro_rules! mutex_lock {
    ($lock:expr) => {{
        cfg_if::cfg_if! {
            if #[cfg(target_arch = "wasm32")] {
                match $lock.lock() {
                    Ok(guard) => guard,
                    Err(poisoned) => poisoned.into_inner(),
                }
            } else {
                $lock.lock().await
            }
        }
    }};
}

// Re-export macros for use within the crate
pub use crate::mutex_lock;
pub use crate::read_lock;
pub use crate::write_lock;
