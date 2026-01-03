//! Endpoint resolver implementations.
//!
//! This module provides concrete resolver implementations for different
//! deployment environments.

mod env;

pub use env::{EnvResolver, EnvResolverConfigError};
