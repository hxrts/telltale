//! TCP transport factory.

use crate::config::TcpTransportConfig;
use crate::TcpTransport;
use async_trait::async_trait;
use rumpsteak_aura_choreography::{
    EndpointResolver, RoleName, Transport, TransportError, TransportFactory,
};
use std::sync::Arc;

/// Factory that creates TCP transports using an endpoint resolver.
///
/// This factory uses an [`EndpointResolver`] to discover peer endpoints
/// and creates [`TcpTransport`] instances for communication.
///
/// # Example
///
/// ```rust,no_run
/// use rumpsteak_transport::{EnvResolver, TcpTransportFactory, TcpTransportConfig};
/// use rumpsteak_aura_choreography::{TransportFactory, RoleName};
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// // Create factory with environment-based discovery
/// let resolver = EnvResolver::with_default_prefix();
/// let config = TcpTransportConfig::default();
/// let factory = TcpTransportFactory::new(resolver, config);
///
/// // Create transport for a role
/// let transport = factory.create(&RoleName::from_static("Alice")).await?;
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct TcpTransportFactory<R: EndpointResolver> {
    resolver: Arc<R>,
    config: TcpTransportConfig,
}

impl<R: EndpointResolver> TcpTransportFactory<R> {
    /// Create a new TCP transport factory.
    pub fn new(resolver: R, config: TcpTransportConfig) -> Self {
        Self {
            resolver: Arc::new(resolver),
            config,
        }
    }

    /// Create a factory with default configuration.
    pub fn with_resolver(resolver: R) -> Self {
        Self::new(resolver, TcpTransportConfig::default())
    }

    /// Get a reference to the resolver.
    pub fn resolver(&self) -> &R {
        &self.resolver
    }

    /// Get a reference to the configuration.
    pub fn config(&self) -> &TcpTransportConfig {
        &self.config
    }
}

impl<R: EndpointResolver> Clone for TcpTransportFactory<R> {
    fn clone(&self) -> Self {
        Self {
            resolver: Arc::clone(&self.resolver),
            config: self.config.clone(),
        }
    }
}

#[async_trait]
impl<R: EndpointResolver + 'static> TransportFactory for TcpTransportFactory<R> {
    async fn create(&self, role: &RoleName) -> Result<Box<dyn Transport>, TransportError> {
        // Resolve the endpoint for this role
        let endpoint = self.resolver.resolve(role).await.map_err(|e| {
            TransportError::ConnectionFailed {
                role: role.clone(),
                reason: format!("failed to resolve endpoint: {}", e),
            }
        })?;

        // Create TCP transport configuration for this role
        let transport_config = crate::config::TcpTransportConfig::new(
            role.as_str(),
            &format!("{}:{}", endpoint.host(), endpoint.port()),
        )
        .with_retry(self.config.retry.clone())
        .with_buffer_size(self.config.buffer_size);

        let transport = TcpTransport::new(transport_config);
        Ok(Box::new(transport))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rumpsteak_aura_choreography::StaticResolver;
    use rumpsteak_aura_choreography::topology::Endpoint;

    #[tokio::test]
    async fn test_factory_creates_transport() {
        let resolver = StaticResolver::from_mappings([(
            RoleName::from_static("Alice"),
            Endpoint::parse("127.0.0.1:8080").unwrap(),
        )]);

        let factory = TcpTransportFactory::with_resolver(resolver);
        let result = factory.create(&RoleName::from_static("Alice")).await;

        // Transport creation should succeed (even if we can't actually connect)
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_factory_fails_on_unresolved_role() {
        let resolver = StaticResolver::empty();
        let factory = TcpTransportFactory::with_resolver(resolver);

        let result = factory.create(&RoleName::from_static("Unknown")).await;
        assert!(result.is_err());
    }

    #[test]
    fn test_factory_clone() {
        let resolver = StaticResolver::empty();
        let factory = TcpTransportFactory::with_resolver(resolver);
        let cloned = factory.clone();

        // Both should share the same resolver
        assert!(Arc::ptr_eq(&factory.resolver, &cloned.resolver));
    }

    #[test]
    fn test_factory_accessors() {
        let resolver = StaticResolver::from_mappings([(
            RoleName::from_static("Alice"),
            Endpoint::parse("127.0.0.1:8080").unwrap(),
        )]);

        let config = TcpTransportConfig::default();
        let factory = TcpTransportFactory::new(resolver, config);

        // Can access resolver and config
        assert!(factory.resolver().can_resolve(&RoleName::from_static("Alice")));
        assert_eq!(factory.config().buffer_size.as_usize(), 32);
    }
}
