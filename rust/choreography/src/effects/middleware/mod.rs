// Middleware Implementations
//
// This module contains composable middleware layers that can wrap effect handlers
// to add cross-cutting concerns like tracing, metrics, retries, and fault injection.
//
// Middleware follows the decorator pattern, wrapping inner handlers and forwarding
// operations while adding additional behavior.

pub mod fault_injection;
pub mod metrics;
pub mod retry;
pub mod trace;

// Re-export middleware types for convenience
pub use metrics::Metrics;
pub use retry::Retry;
pub use trace::Trace;

#[cfg(feature = "test-utils")]
pub use fault_injection::FaultInjection;
