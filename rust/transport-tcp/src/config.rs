//! Configuration for TCP transport.

use std::collections::HashMap;
use std::time::Duration;

/// Configuration for a TCP transport instance.
#[derive(Debug, Clone)]
pub struct TcpTransportConfig {
    /// Name of this role.
    pub role: String,
    /// Address this role listens on.
    pub listen_addr: String,
    /// Map of peer role names to their addresses.
    pub peers: HashMap<String, String>,
    /// Connection retry settings.
    pub retry: RetryConfig,
    /// Channel buffer size for incoming messages.
    pub buffer_size: usize,
}

/// Configuration for connection retry behavior.
#[derive(Debug, Clone)]
pub struct RetryConfig {
    /// Maximum number of connection attempts.
    pub max_attempts: u32,
    /// Initial delay between retries.
    pub initial_delay: Duration,
    /// Maximum delay between retries.
    pub max_delay: Duration,
    /// Multiplier for exponential backoff.
    pub backoff_multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 5,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(10),
            backoff_multiplier: 2.0,
        }
    }
}

impl TcpTransportConfig {
    /// Create a new configuration for a role.
    ///
    /// # Arguments
    ///
    /// * `role` - Name of this role
    /// * `listen_addr` - Address to listen on (e.g., "127.0.0.1:8080")
    pub fn new(role: impl Into<String>, listen_addr: impl Into<String>) -> Self {
        Self {
            role: role.into(),
            listen_addr: listen_addr.into(),
            peers: HashMap::new(),
            retry: RetryConfig::default(),
            buffer_size: 32,
        }
    }

    /// Add a peer role with its address.
    pub fn with_peer(mut self, role: impl Into<String>, addr: impl Into<String>) -> Self {
        self.peers.insert(role.into(), addr.into());
        self
    }

    /// Set retry configuration.
    pub fn with_retry(mut self, retry: RetryConfig) -> Self {
        self.retry = retry;
        self
    }

    /// Set the buffer size for incoming message channels.
    pub fn with_buffer_size(mut self, size: usize) -> Self {
        self.buffer_size = size;
        self
    }

    /// Create configuration from environment variables.
    ///
    /// Expected variables:
    /// - `ROLE`: Name of this role
    /// - `LISTEN_ADDR`: Address to listen on
    /// - `PEER_{ROLE}`: Address for each peer role (e.g., `PEER_BOB=127.0.0.1:8081`)
    ///
    /// # Errors
    ///
    /// Returns an error if required variables are missing.
    pub fn from_env() -> Result<Self, std::env::VarError> {
        let role = std::env::var("ROLE")?;
        let listen_addr = std::env::var("LISTEN_ADDR")?;

        let mut config = Self::new(role, listen_addr);

        // Scan for PEER_* variables
        for (key, value) in std::env::vars() {
            if let Some(peer_role) = key.strip_prefix("PEER_") {
                config.peers.insert(peer_role.to_string(), value);
            }
        }

        Ok(config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_builder() {
        let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
            .with_peer("Bob", "127.0.0.1:8081")
            .with_peer("Carol", "127.0.0.1:8082")
            .with_buffer_size(64);

        assert_eq!(config.role, "Alice");
        assert_eq!(config.listen_addr, "127.0.0.1:8080");
        assert_eq!(config.peers.len(), 2);
        assert_eq!(config.peers.get("Bob"), Some(&"127.0.0.1:8081".to_string()));
        assert_eq!(config.buffer_size, 64);
    }

    #[test]
    fn test_retry_defaults() {
        let retry = RetryConfig::default();
        assert_eq!(retry.max_attempts, 5);
        assert_eq!(retry.initial_delay, Duration::from_millis(100));
    }
}
