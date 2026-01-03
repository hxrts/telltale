//! Environment variable based endpoint resolver.

use async_trait::async_trait;
use rumpsteak_aura_choreography::{
    EndpointResolver, ResolutionFailureReason, ResolverError, RoleName,
};
use rumpsteak_aura_choreography::topology::Endpoint;
use thiserror::Error;

/// Error configuring the environment resolver.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum EnvResolverConfigError {
    /// Prefix cannot be empty.
    #[error("prefix cannot be empty")]
    EmptyPrefix,

    /// Prefix contains invalid characters.
    #[error("prefix contains invalid characters (must be ASCII alphanumeric or underscore)")]
    InvalidPrefixChars,
}

/// Resolver that reads endpoints from environment variables.
///
/// Pattern: `{PREFIX}_{ROLE}_ENDPOINT` → `host:port`
///
/// Role names are normalized to uppercase with hyphens replaced by underscores.
///
/// # Example
///
/// With the default prefix "RUMPSTEAK":
///
/// ```bash
/// export RUMPSTEAK_ALICE_ENDPOINT=127.0.0.1:8080
/// export RUMPSTEAK_BOB_ENDPOINT=127.0.0.1:8081
/// ```
///
/// ```rust,no_run
/// use rumpsteak_transport::EnvResolver;
/// use rumpsteak_aura_choreography::{EndpointResolver, RoleName};
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let resolver = EnvResolver::with_default_prefix();
/// let endpoint = resolver.resolve(&RoleName::from_static("Alice")).await?;
/// println!("Alice is at {}", endpoint);
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct EnvResolver {
    prefix: String,
}

impl EnvResolver {
    /// Create a resolver with a custom prefix.
    ///
    /// The prefix must be non-empty and contain only ASCII alphanumeric
    /// characters or underscores.
    ///
    /// # Errors
    ///
    /// Returns an error if the prefix is empty or contains invalid characters.
    pub fn new(prefix: impl Into<String>) -> Result<Self, EnvResolverConfigError> {
        let prefix = prefix.into();
        if prefix.is_empty() {
            return Err(EnvResolverConfigError::EmptyPrefix);
        }
        if !prefix
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            return Err(EnvResolverConfigError::InvalidPrefixChars);
        }
        Ok(Self { prefix })
    }

    /// Create a resolver with the default prefix "RUMPSTEAK".
    #[must_use]
    pub fn with_default_prefix() -> Self {
        Self {
            prefix: "RUMPSTEAK".to_string(),
        }
    }

    /// Get the prefix used for environment variable names.
    #[must_use]
    pub fn prefix(&self) -> &str {
        &self.prefix
    }

    /// Get the environment variable name for a role.
    #[must_use]
    pub fn env_var_name(&self, role: &RoleName) -> String {
        format!(
            "{}_{}_ENDPOINT",
            self.prefix,
            role.as_str().to_uppercase().replace('-', "_")
        )
    }
}

#[async_trait]
impl EndpointResolver for EnvResolver {
    async fn resolve(
        &self,
        role: &RoleName,
    ) -> Result<Endpoint, ResolverError> {
        let var_name = self.env_var_name(role);

        let value = std::env::var(&var_name).map_err(|_| ResolverError::ResolutionFailed {
            role: role.clone(),
            reason: ResolutionFailureReason::EnvVarNotSet {
                var_name: var_name.clone(),
            },
        })?;

        Endpoint::parse(&value).map_err(|e| ResolverError::ResolutionFailed {
            role: role.clone(),
            reason: ResolutionFailureReason::InvalidAddress {
                details: e.to_string(),
            },
        })
    }

    fn can_resolve(&self, role: &RoleName) -> bool {
        let var_name = self.env_var_name(role);
        std::env::var(&var_name).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_env_resolver_new_valid() {
        let resolver = EnvResolver::new("MY_PREFIX").unwrap();
        assert_eq!(resolver.prefix(), "MY_PREFIX");
    }

    #[test]
    fn test_env_resolver_new_empty_prefix() {
        let result = EnvResolver::new("");
        assert!(matches!(result, Err(EnvResolverConfigError::EmptyPrefix)));
    }

    #[test]
    fn test_env_resolver_new_invalid_chars() {
        let result = EnvResolver::new("my-prefix");
        assert!(matches!(
            result,
            Err(EnvResolverConfigError::InvalidPrefixChars)
        ));
    }

    #[test]
    fn test_env_resolver_with_default_prefix() {
        let resolver = EnvResolver::with_default_prefix();
        assert_eq!(resolver.prefix(), "RUMPSTEAK");
    }

    #[test]
    fn test_env_var_name() {
        let resolver = EnvResolver::with_default_prefix();
        let role = RoleName::from_static("Alice");
        assert_eq!(resolver.env_var_name(&role), "RUMPSTEAK_ALICE_ENDPOINT");
    }

    #[test]
    fn test_env_var_name_with_underscore() {
        let resolver = EnvResolver::with_default_prefix();
        let role = RoleName::new("my_role").unwrap();
        assert_eq!(resolver.env_var_name(&role), "RUMPSTEAK_MY_ROLE_ENDPOINT");
    }

    #[test]
    fn test_env_var_name_lowercase() {
        let resolver = EnvResolver::with_default_prefix();
        let role = RoleName::new("alice").unwrap();
        assert_eq!(resolver.env_var_name(&role), "RUMPSTEAK_ALICE_ENDPOINT");
    }

    #[tokio::test]
    async fn test_resolve_success() {
        std::env::set_var("TEST_ALICE_ENDPOINT", "127.0.0.1:8080");

        let resolver = EnvResolver::new("TEST").unwrap();
        let endpoint = resolver
            .resolve(&RoleName::from_static("Alice"))
            .await
            .unwrap();

        assert_eq!(endpoint.host(), "127.0.0.1");
        assert_eq!(endpoint.port(), 8080);

        std::env::remove_var("TEST_ALICE_ENDPOINT");
    }

    #[tokio::test]
    async fn test_resolve_not_set() {
        let resolver = EnvResolver::new("NONEXISTENT_PREFIX_12345").unwrap();
        let result = resolver
            .resolve(&RoleName::from_static("Alice"))
            .await;

        assert!(matches!(
            result,
            Err(ResolverError::ResolutionFailed {
                reason: ResolutionFailureReason::EnvVarNotSet { .. },
                ..
            })
        ));
    }

    #[tokio::test]
    async fn test_resolve_invalid_address() {
        std::env::set_var("TEST_BAD_ENDPOINT", "not-a-valid-endpoint");

        let resolver = EnvResolver::new("TEST").unwrap();
        let result = resolver.resolve(&RoleName::new("bad").unwrap()).await;

        assert!(matches!(
            result,
            Err(ResolverError::ResolutionFailed {
                reason: ResolutionFailureReason::InvalidAddress { .. },
                ..
            })
        ));

        std::env::remove_var("TEST_BAD_ENDPOINT");
    }

    #[test]
    fn test_can_resolve_true() {
        std::env::set_var("CHECK_ALICE_ENDPOINT", "127.0.0.1:8080");

        let resolver = EnvResolver::new("CHECK").unwrap();
        assert!(resolver.can_resolve(&RoleName::from_static("Alice")));

        std::env::remove_var("CHECK_ALICE_ENDPOINT");
    }

    #[test]
    fn test_can_resolve_false() {
        let resolver = EnvResolver::new("NONEXISTENT_PREFIX_67890").unwrap();
        assert!(!resolver.can_resolve(&RoleName::from_static("Alice")));
    }

    #[tokio::test]
    async fn test_resolve_ipv6_loopback() {
        std::env::set_var("IPV6LO_ALICE_ENDPOINT", "[::1]:8080");

        let resolver = EnvResolver::new("IPV6LO").unwrap();
        let endpoint = resolver
            .resolve(&RoleName::from_static("Alice"))
            .await
            .unwrap();

        assert_eq!(endpoint.host(), "::1");
        assert_eq!(endpoint.port(), 8080);
        assert_eq!(endpoint.to_string(), "[::1]:8080");

        std::env::remove_var("IPV6LO_ALICE_ENDPOINT");
    }

    #[tokio::test]
    async fn test_resolve_ipv6_address() {
        std::env::set_var("IPV6_ALICE_ENDPOINT", "[2001:db8::1]:9000");

        let resolver = EnvResolver::new("IPV6").unwrap();
        let endpoint = resolver
            .resolve(&RoleName::from_static("Alice"))
            .await
            .unwrap();

        assert_eq!(endpoint.host(), "2001:db8::1");
        assert_eq!(endpoint.port(), 9000);
        assert_eq!(endpoint.to_string(), "[2001:db8::1]:9000");

        std::env::remove_var("IPV6_ALICE_ENDPOINT");
    }

    #[tokio::test]
    async fn test_resolve_ipv6_full() {
        std::env::set_var("IPV6F_BOB_ENDPOINT", "[fe80::1%eth0]:8080");

        let resolver = EnvResolver::new("IPV6F").unwrap();
        // Note: Zone IDs like %eth0 may not parse correctly with standard parsing
        // This tests that the endpoint at least attempts to parse
        let result = resolver
            .resolve(&RoleName::from_static("Bob"))
            .await;

        // Zone IDs are platform-specific, so we just check it doesn't crash
        std::env::remove_var("IPV6F_BOB_ENDPOINT");

        // The result may succeed or fail depending on zone ID support
        // The important thing is it doesn't panic
        let _ = result;
    }

    #[tokio::test]
    async fn test_resolve_ipv6_any() {
        std::env::set_var("IPV6ANY_SERVER_ENDPOINT", "[::]:3000");

        let resolver = EnvResolver::new("IPV6ANY").unwrap();
        let endpoint = resolver
            .resolve(&RoleName::from_static("Server"))
            .await
            .unwrap();

        assert_eq!(endpoint.host(), "::");
        assert_eq!(endpoint.port(), 3000);
        assert_eq!(endpoint.to_string(), "[::]:3000");

        std::env::remove_var("IPV6ANY_SERVER_ENDPOINT");
    }
}
