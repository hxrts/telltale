//! Endpoint resolver implementations.
//!
//! This module provides concrete resolver implementations for different
//! deployment environments.

use std::collections::BTreeMap;

use async_trait::async_trait;
use telltale_choreography::{RoleName, TopologyEndpoint};
use thiserror::Error;

mod env;

pub use env::{EnvResolver, EnvResolverConfigError};

/// Reason for endpoint resolution failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionFailureReason {
    /// Environment variable not set.
    EnvVarNotSet {
        /// Name of missing environment variable.
        var_name: String,
    },
    /// Invalid endpoint address.
    InvalidAddress {
        /// Parse error details.
        details: String,
    },
    /// Resolver has no mapping for this role.
    NotConfigured,
}

/// Endpoint resolution errors.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ResolverError {
    /// Resolution failed for a specific role.
    #[error("resolution failed for {role}: {reason:?}")]
    ResolutionFailed {
        /// Role that could not be resolved.
        role: RoleName,
        /// Root cause for failure.
        reason: ResolutionFailureReason,
    },
}

/// Resolves role names to network endpoints.
#[async_trait]
pub trait EndpointResolver: Send + Sync {
    /// Resolve a role to an endpoint.
    async fn resolve(&self, role: &RoleName) -> Result<TopologyEndpoint, ResolverError>;

    /// Fast existence check for a role mapping.
    fn can_resolve(&self, _role: &RoleName) -> bool {
        true
    }
}

/// Static endpoint resolver backed by in-memory mappings.
#[derive(Debug, Clone, Default)]
pub struct StaticResolver {
    endpoints: BTreeMap<RoleName, TopologyEndpoint>,
}

impl StaticResolver {
    /// Create a resolver from explicit mappings.
    pub fn from_mappings(mappings: impl IntoIterator<Item = (RoleName, TopologyEndpoint)>) -> Self {
        Self {
            endpoints: mappings.into_iter().collect(),
        }
    }

    /// Create an empty resolver.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Add a role-to-endpoint mapping.
    pub fn with_mapping(mut self, role: RoleName, endpoint: TopologyEndpoint) -> Self {
        self.endpoints.insert(role, endpoint);
        self
    }
}

#[async_trait]
impl EndpointResolver for StaticResolver {
    async fn resolve(&self, role: &RoleName) -> Result<TopologyEndpoint, ResolverError> {
        self.endpoints
            .get(role)
            .cloned()
            .ok_or_else(|| ResolverError::ResolutionFailed {
                role: role.clone(),
                reason: ResolutionFailureReason::NotConfigured,
            })
    }

    fn can_resolve(&self, role: &RoleName) -> bool {
        self.endpoints.contains_key(role)
    }
}
