//! Configuration for TCP transport.

use std::collections::BTreeMap;
use std::time::Duration;
use telltale_machine::RuntimeTransportContract;
use telltale_runtime::QueueCapacity;
use telltale_types::FixedQ32;

/// Peer authentication mode for the TCP handshake.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TcpPeerAuthentication {
    /// Authenticate peers with a 32-byte pre-shared key.
    PreSharedKey([u8; 32]),
    /// Permit unauthenticated TCP only on a trusted network.
    UnauthenticatedTrustedNetwork { explicit_allow: bool },
}

/// Configuration for a TCP transport instance.
#[derive(Debug, Clone)]
pub struct TcpTransportConfig {
    /// Name of this role.
    pub role: String,
    /// Address this role listens on.
    pub listen_addr: String,
    /// Map of peer role names to their addresses.
    pub peers: BTreeMap<String, String>,
    /// Connection retry settings.
    pub retry: RetryConfig,
    /// Channel buffer size for incoming messages.
    pub buffer_size: QueueCapacity,
    /// Maximum concurrently accepted inbound connections.
    pub max_connections: usize,
    /// Maximum total payload bytes being read by inbound connection handlers.
    pub max_inflight_payload_bytes: usize,
    /// Maximum live inbound connections per source IP.
    pub per_source_connection_limit: usize,
    /// Maximum accepted reconnect attempts per source IP within `reconnect_window`.
    pub per_source_reconnect_limit: usize,
    /// Sliding window for per-source reconnect limiting.
    pub reconnect_window: Duration,
    /// Authentication mode for peer admission.
    pub authentication: TcpPeerAuthentication,
    /// Timeout for inbound handshake and frame reads.
    pub read_timeout: Duration,
    /// Timeout for outbound handshake and frame writes.
    pub write_timeout: Duration,
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
    pub backoff_multiplier: FixedQ32,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 5,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(10),
            backoff_multiplier: FixedQ32::from_ratio(2, 1)
                .expect("retry backoff multiplier default must be representable"),
        }
    }
}

impl Default for TcpTransportConfig {
    fn default() -> Self {
        Self {
            role: String::new(),
            listen_addr: String::new(),
            peers: BTreeMap::new(),
            retry: RetryConfig::default(),
            buffer_size: QueueCapacity::try_new(32).expect("default buffer size in range"),
            max_connections: 1024,
            max_inflight_payload_bytes: 16 * 1024 * 1024,
            per_source_connection_limit: 64,
            per_source_reconnect_limit: 128,
            reconnect_window: Duration::from_secs(10),
            authentication: TcpPeerAuthentication::UnauthenticatedTrustedNetwork {
                explicit_allow: false,
            },
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(10),
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
            peers: BTreeMap::new(),
            retry: RetryConfig::default(),
            buffer_size: QueueCapacity::try_new(32).expect("default buffer size in range"),
            max_connections: 1024,
            max_inflight_payload_bytes: 16 * 1024 * 1024,
            per_source_connection_limit: 64,
            per_source_reconnect_limit: 128,
            reconnect_window: Duration::from_secs(10),
            authentication: TcpPeerAuthentication::UnauthenticatedTrustedNetwork {
                explicit_allow: false,
            },
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(10),
        }
    }

    /// Add a peer role with its address.
    #[must_use]
    pub fn with_peer(mut self, role: impl Into<String>, addr: impl Into<String>) -> Self {
        self.peers.insert(role.into(), addr.into());
        self
    }

    /// Set retry configuration.
    #[must_use]
    pub fn with_retry(mut self, retry: RetryConfig) -> Self {
        self.retry = retry;
        self
    }

    /// Set the buffer size for incoming message channels.
    #[must_use]
    pub fn with_buffer_size(mut self, size: QueueCapacity) -> Self {
        self.buffer_size = size;
        self
    }

    /// Set the maximum number of concurrently accepted inbound connections.
    #[must_use]
    pub fn with_max_connections(mut self, max_connections: usize) -> Self {
        self.max_connections = max_connections;
        self
    }

    /// Set the global inbound payload byte cap.
    #[must_use]
    pub fn with_max_inflight_payload_bytes(mut self, max_bytes: usize) -> Self {
        self.max_inflight_payload_bytes = max_bytes;
        self
    }

    /// Set per-source connection and reconnect storm limits.
    #[must_use]
    pub fn with_per_source_limits(
        mut self,
        live_connection_limit: usize,
        reconnect_limit: usize,
        reconnect_window: Duration,
    ) -> Self {
        self.per_source_connection_limit = live_connection_limit;
        self.per_source_reconnect_limit = reconnect_limit;
        self.reconnect_window = reconnect_window;
        self
    }

    /// Authenticate TCP peers with a pre-shared key.
    ///
    /// This mode exports `authenticated_peers = true` from
    /// [`TcpTransportConfig::runtime_transport_contract`] and can satisfy
    /// theorem-pack admission profiles that require protocol-origin integrity.
    #[must_use]
    pub fn with_preshared_key(mut self, key: [u8; 32]) -> Self {
        self.authentication = TcpPeerAuthentication::PreSharedKey(key);
        self
    }

    /// Explicitly allow unauthenticated TCP for trusted-network deployments.
    ///
    /// This mode exports `authenticated_peers = false` from
    /// [`TcpTransportConfig::runtime_transport_contract`]. It is valid for
    /// example and trusted-network deployments, but theorem-pack admission will
    /// reject protocol-origin claims that require authenticated peers.
    #[must_use]
    pub fn allow_unauthenticated_for_trusted_network(mut self) -> Self {
        self.authentication = TcpPeerAuthentication::UnauthenticatedTrustedNetwork {
            explicit_allow: true,
        };
        self
    }

    /// Set read and write timeouts for TCP handshakes and frames.
    #[must_use]
    pub fn with_io_timeouts(mut self, read_timeout: Duration, write_timeout: Duration) -> Self {
        self.read_timeout = read_timeout;
        self.write_timeout = write_timeout;
        self
    }

    /// Export the semantic transport contract used by theorem-pack admission.
    ///
    /// The ProtocolMachine only consumes the semantic result. The TCP-specific
    /// authentication-mode mapping stays in this crate: pre-shared-key mode is
    /// authenticated, while trusted-network mode is deliberately
    /// unauthenticated.
    #[must_use]
    pub fn runtime_transport_contract(&self) -> RuntimeTransportContract {
        RuntimeTransportContract::new("TcpTransport", "Tcp")
            .with_role_addressed_routing(true)
            .with_authenticated_peers(matches!(
                self.authentication,
                TcpPeerAuthentication::PreSharedKey(_)
            ))
            .with_per_peer_fifo_delivery(true)
            .with_fail_closed_unknown_role(true)
            .with_no_message_synthesis(true)
            .with_explicit_readiness_errors(true)
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
    use telltale_machine::{
        validate_transport_contracts_for_execution_profile, ProtocolMachineExecutionProfile,
        TransportContractGateError,
    };

    #[test]
    fn test_config_builder() {
        let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
            .with_peer("Bob", "127.0.0.1:8081")
            .with_peer("Carol", "127.0.0.1:8082")
            .with_buffer_size(QueueCapacity::try_new(64).expect("test buffer size in range"));

        assert_eq!(config.role, "Alice");
        assert_eq!(config.listen_addr, "127.0.0.1:8080");
        assert_eq!(config.peers.len(), 2);
        assert_eq!(config.peers.get("Bob"), Some(&"127.0.0.1:8081".to_string()));
        assert_eq!(
            config.buffer_size,
            QueueCapacity::try_new(64).expect("test buffer size in range")
        );
    }

    #[test]
    fn test_retry_defaults() {
        let retry = RetryConfig::default();
        assert_eq!(retry.max_attempts, 5);
        assert_eq!(retry.initial_delay, Duration::from_millis(100));
    }

    #[test]
    fn runtime_transport_contract_reflects_preshared_key_authentication() {
        let contract = TcpTransportConfig::new("Alice", "127.0.0.1:0")
            .with_preshared_key([1; 32])
            .runtime_transport_contract();

        assert_eq!(contract.transport_name, "TcpTransport");
        assert_eq!(contract.transport_type, "Tcp");
        assert!(contract.role_addressed_routing);
        assert!(contract.authenticated_peers);
        assert!(contract.per_peer_fifo_delivery);
        assert!(contract.fail_closed_unknown_role);
        assert!(contract.no_message_synthesis);
    }

    #[test]
    fn runtime_transport_contract_reflects_trusted_network_mode() {
        let contract = TcpTransportConfig::new("Alice", "127.0.0.1:0")
            .allow_unauthenticated_for_trusted_network()
            .runtime_transport_contract();

        assert!(contract.role_addressed_routing);
        assert!(!contract.authenticated_peers);
        assert!(contract.per_peer_fifo_delivery);
        assert!(contract.fail_closed_unknown_role);
        assert!(contract.no_message_synthesis);
    }

    #[test]
    fn preshared_key_contract_satisfies_theorem_transport_admission() {
        let profile = ProtocolMachineExecutionProfile::full();
        let contract = TcpTransportConfig::new("Alice", "127.0.0.1:0")
            .with_preshared_key([1; 32])
            .runtime_transport_contract();

        assert_eq!(
            validate_transport_contracts_for_execution_profile(&profile, &[contract]),
            Ok(())
        );
    }

    #[test]
    fn trusted_network_contract_fails_authenticated_theorem_admission() {
        let profile = ProtocolMachineExecutionProfile::full();
        let contract = TcpTransportConfig::new("Alice", "127.0.0.1:0")
            .allow_unauthenticated_for_trusted_network()
            .runtime_transport_contract();

        assert_eq!(
            validate_transport_contracts_for_execution_profile(&profile, &[contract]),
            Err(
                TransportContractGateError::UnsatisfiedTransportRequirement {
                    transport_name: "TcpTransport".to_string(),
                    requirement: "authenticated_peers",
                }
            )
        );
    }

    #[test]
    fn mixed_transport_set_fails_if_any_selected_transport_is_unauthenticated() {
        let profile = ProtocolMachineExecutionProfile::full();
        let authenticated = TcpTransportConfig::new("Alice", "127.0.0.1:0")
            .with_preshared_key([1; 32])
            .runtime_transport_contract();
        let unauthenticated = TcpTransportConfig::new("Bob", "127.0.0.1:0")
            .allow_unauthenticated_for_trusted_network()
            .runtime_transport_contract();

        assert_eq!(
            validate_transport_contracts_for_execution_profile(
                &profile,
                &[authenticated, unauthenticated]
            ),
            Err(
                TransportContractGateError::UnsatisfiedTransportRequirement {
                    transport_name: "TcpTransport".to_string(),
                    requirement: "authenticated_peers",
                }
            )
        );
    }
}
