//! Platform-specific synchronization primitives
//!
//! This module provides cross-platform abstractions for synchronization primitives
//! that work on both native (tokio) and WASM targets.
//!
//! On native targets, we use tokio's async synchronization primitives.
//! On WASM, we use std::sync primitives (which work because WASM is single-threaded)
//! and futures::channel for message passing.

// Re-export platform-specific RwLock
#[cfg(not(target_arch = "wasm32"))]
pub use tokio::sync::RwLock;

#[cfg(target_arch = "wasm32")]
pub use std::sync::RwLock;

// Re-export platform-specific Mutex
#[cfg(not(target_arch = "wasm32"))]
pub use tokio::sync::Mutex;

#[cfg(target_arch = "wasm32")]
pub use std::sync::Mutex;

// Re-export platform-specific mpsc channels
#[cfg(not(target_arch = "wasm32"))]
pub use tokio::sync::mpsc;

#[cfg(target_arch = "wasm32")]
pub use futures::channel::mpsc;

/// Helper macro for acquiring a read lock.
///
/// On native targets, this awaits the async lock.
/// On WASM, this uses the blocking (but single-threaded safe) lock.
///
/// # Panics (WASM only)
///
/// On WASM targets, panics if the lock is poisoned (another thread panicked
/// while holding the lock). This should not occur in practice since WASM
/// is single-threaded.
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
        #[cfg(not(target_arch = "wasm32"))]
        {
            $lock.read().await
        }
        #[cfg(target_arch = "wasm32")]
        {
            $lock.read().expect("RwLock poisoned")
        }
    }};
}

/// Helper macro for acquiring a write lock.
///
/// On native targets, this awaits the async lock.
/// On WASM, this uses the blocking (but single-threaded safe) lock.
///
/// # Panics (WASM only)
///
/// On WASM targets, panics if the lock is poisoned (another thread panicked
/// while holding the lock). This should not occur in practice since WASM
/// is single-threaded.
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
        #[cfg(not(target_arch = "wasm32"))]
        {
            $lock.write().await
        }
        #[cfg(target_arch = "wasm32")]
        {
            $lock.write().expect("RwLock poisoned")
        }
    }};
}

/// Helper macro for acquiring a mutex lock.
///
/// On native targets, this awaits the async lock.
/// On WASM, this uses the blocking (but single-threaded safe) lock.
///
/// # Panics (WASM only)
///
/// On WASM targets, panics if the mutex is poisoned (another thread panicked
/// while holding the lock). This should not occur in practice since WASM
/// is single-threaded.
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
        #[cfg(not(target_arch = "wasm32"))]
        {
            $lock.lock().await
        }
        #[cfg(target_arch = "wasm32")]
        {
            $lock.lock().expect("Mutex poisoned")
        }
    }};
}

// Re-export macros for use within the crate
pub use crate::mutex_lock;
pub use crate::read_lock;
pub use crate::write_lock;
