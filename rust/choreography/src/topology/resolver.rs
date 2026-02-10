//! Endpoint resolver trait and implementations.

use super::{Endpoint, Location, Topology};
use crate::RoleName;
use async_trait::async_trait;
use std::collections::HashMap;
use std::fmt;
use thiserror::Error;

/// Reason for resolution failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionFailureReason {
    /// Environment variable not set.
    EnvVarNotSet {
        /// The environment variable name that was expected.
        var_name: String,
    },
    /// DNS lookup failed.
    DnsLookupFailed,
    /// Resolution timed out.
    Timeout,
    /// Address format was invalid.
    InvalidAddress {
        /// Details about the parse failure.
        details: String,
    },
    /// Role not configured in static resolver.
    NotConfigured,
}

impl fmt::Display for ResolutionFailureReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EnvVarNotSet { var_name } => {
                write!(f, "environment variable {} not set", var_name)
            }
            Self::DnsLookupFailed => write!(f, "DNS lookup failed"),
            Self::Timeout => write!(f, "resolution timed out"),
            Self::InvalidAddress { details } => write!(f, "invalid address: {}", details),
            Self::NotConfigured => write!(f, "role not configured"),
        }
    }
}

/// Errors that can occur during endpoint resolution.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ResolverError {
    /// The role was not found in the resolver.
    #[error("role not found: {role}")]
    RoleNotFound {
        /// The role that was not found.
        role: RoleName,
    },

    /// Resolution failed for a role.
    #[error("resolution failed for {role}: {reason}")]
    ResolutionFailed {
        /// The role that failed to resolve.
        role: RoleName,
        /// The reason for the failure.
        reason: ResolutionFailureReason,
    },
}

/// Resolves role names to network endpoints.
///
/// Implementations of this trait provide different strategies for
/// discovering where roles are deployed (static configuration,
/// environment variables, DNS, service discovery, etc.).
#[async_trait]
pub trait EndpointResolver: Send + Sync {
    /// Resolve a role to a network endpoint.
    ///
    /// Returns the endpoint for the given role, or an error if
    /// the role cannot be resolved.
    async fn resolve(&self, role: &RoleName) -> Result<Endpoint, ResolverError>;

    /// Check if a role can be resolved.
    ///
    /// This is an optional optimization hint. The default implementation
    /// returns `true`, meaning callers should attempt resolution and
    /// handle errors. Implementations may override this to provide
    /// a fast check without performing the full resolution.
    fn can_resolve(&self, _role: &RoleName) -> bool {
        true
    }
}

/// Resolver that uses statically configured endpoints from Topology.
///
/// This resolver is constructed from a [`Topology`] and provides
/// endpoint resolution for roles that have [`Location::Remote`] entries.
#[derive(Debug, Clone)]
pub struct StaticResolver {
    endpoints: HashMap<RoleName, Endpoint>,
}

impl StaticResolver {
    /// Create a static resolver from a topology.
    ///
    /// Extracts all `Remote` locations from the topology and stores
    /// them for resolution. Local and colocated roles are not included.
    pub fn from_topology(topology: &Topology) -> Self {
        let mut endpoints = HashMap::with_capacity(topology.locations.len());
        for (role, location) in &topology.locations {
            if let Location::Remote(endpoint) = location {
                endpoints.insert(role.clone(), endpoint.clone());
            }
        }
        Self { endpoints }
    }

    /// Create a static resolver from explicit mappings.
    ///
    /// This is useful for testing or when the topology is not available.
    pub fn from_mappings(mappings: impl IntoIterator<Item = (RoleName, Endpoint)>) -> Self {
        Self {
            endpoints: mappings.into_iter().collect(),
        }
    }

    /// Create an empty static resolver.
    pub fn empty() -> Self {
        Self {
            endpoints: HashMap::new(),
        }
    }

    /// Add a mapping to the resolver.
    pub fn with_mapping(mut self, role: RoleName, endpoint: Endpoint) -> Self {
        self.endpoints.insert(role, endpoint);
        self
    }

    /// Get the number of configured endpoints.
    pub fn len(&self) -> usize {
        self.endpoints.len()
    }

    /// Check if the resolver has no configured endpoints.
    pub fn is_empty(&self) -> bool {
        self.endpoints.is_empty()
    }
}

#[async_trait]
impl EndpointResolver for StaticResolver {
    async fn resolve(&self, role: &RoleName) -> Result<Endpoint, ResolverError> {
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

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_static_resolver_from_mappings() {
        let resolver = StaticResolver::from_mappings([
            (
                RoleName::from_static("Alice"),
                Endpoint::parse("127.0.0.1:8080").unwrap(),
            ),
            (
                RoleName::from_static("Bob"),
                Endpoint::parse("127.0.0.1:8081").unwrap(),
            ),
        ]);

        let alice_endpoint = resolver
            .resolve(&RoleName::from_static("Alice"))
            .await
            .unwrap();
        assert_eq!(alice_endpoint.port(), 8080);

        let bob_endpoint = resolver
            .resolve(&RoleName::from_static("Bob"))
            .await
            .unwrap();
        assert_eq!(bob_endpoint.port(), 8081);
    }

    #[tokio::test]
    async fn test_static_resolver_not_configured() {
        let resolver = StaticResolver::empty();

        let result = resolver.resolve(&RoleName::from_static("Unknown")).await;
        assert!(matches!(
            result,
            Err(ResolverError::ResolutionFailed {
                reason: ResolutionFailureReason::NotConfigured,
                ..
            })
        ));
    }

    #[test]
    fn test_static_resolver_can_resolve() {
        let resolver = StaticResolver::from_mappings([(
            RoleName::from_static("Alice"),
            Endpoint::parse("127.0.0.1:8080").unwrap(),
        )]);

        assert!(resolver.can_resolve(&RoleName::from_static("Alice")));
        assert!(!resolver.can_resolve(&RoleName::from_static("Bob")));
    }

    #[test]
    fn test_static_resolver_with_mapping() {
        let resolver = StaticResolver::empty()
            .with_mapping(
                RoleName::from_static("Alice"),
                Endpoint::parse("127.0.0.1:8080").unwrap(),
            )
            .with_mapping(
                RoleName::from_static("Bob"),
                Endpoint::parse("127.0.0.1:8081").unwrap(),
            );

        assert_eq!(resolver.len(), 2);
        assert!(!resolver.is_empty());
    }

    #[test]
    fn test_resolution_failure_reason_display() {
        assert_eq!(
            ResolutionFailureReason::EnvVarNotSet {
                var_name: "FOO".to_string()
            }
            .to_string(),
            "environment variable FOO not set"
        );
        assert_eq!(
            ResolutionFailureReason::DnsLookupFailed.to_string(),
            "DNS lookup failed"
        );
        assert_eq!(
            ResolutionFailureReason::Timeout.to_string(),
            "resolution timed out"
        );
        assert_eq!(
            ResolutionFailureReason::InvalidAddress {
                details: "bad format".to_string()
            }
            .to_string(),
            "invalid address: bad format"
        );
        assert_eq!(
            ResolutionFailureReason::NotConfigured.to_string(),
            "role not configured"
        );
    }
}
