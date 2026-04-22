//! Example TCP Transport for Telltale Session Types
//!
//! This crate provides a reference TCP transport implementation for the
//! Telltale session types library. It is useful as an executable example and
//! integration target; applications with stronger operational requirements
//! may wrap or replace it with a transport that satisfies the same documented
//! contract.
//!
//! `telltale-transport` participates in the first-party runtime contract
//! boundary as a reference implementation with documented transport-contract
//! profiles. Third-party transports remain outside the formal-verification
//! claim unless they separately satisfy the same contract.
//!
//! ## Features
//!
//! - TCP transport with length-prefixed message framing
//! - **Full IPv4 and IPv6 support** (including dual-stack)
//! - Environment-based endpoint resolution
//! - Transport factory pattern for easy instantiation
//! - Automatic connection management with retry and backoff
//! - Role-based addressing (each role has a unique address)
//! - Graceful shutdown support
//! - Tracing instrumentation for observability
//!
//! ## Security Boundary
//!
//! The first-party TCP transport supports pre-shared-key peer authentication.
//! Plaintext unauthenticated mode is trusted-network only and must be enabled
//! explicitly with `allow_unauthenticated_for_trusted_network()`. The protocol
//! machine's formal guarantees assume the selected transport satisfies its
//! documented contract. Enable the `redacted-logs` feature when structured logs
//! must not expose peer roles or socket addresses.
//!
//! ## Example
//!
//! ```no_run
//! use telltale_transport::{TcpTransport, TcpTransportConfig, EnvResolver, TcpTransportFactory};
//! use telltale_runtime::{RoleName, Transport};
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // Option 1: Direct configuration with IPv4
//!     let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
//!         .allow_unauthenticated_for_trusted_network()
//!         .with_peer("Bob", "127.0.0.1:8081")
//!         .with_peer("Carol", "127.0.0.1:8082");
//!
//!     let transport = TcpTransport::new(config);
//!     transport.start().await?;
//!
//!     // Option 2: Factory with environment-based discovery
//!     // Set environment variables:
//!     //   TELLTALE_ALICE_ENDPOINT=127.0.0.1:8080
//!     //   TELLTALE_BOB_ENDPOINT=127.0.0.1:8081
//!     let resolver = EnvResolver::with_default_prefix();
//!     let factory = TcpTransportFactory::with_resolver(resolver);
//!     let transport = factory.create(&RoleName::from_static("Alice")).await?;
//!
//!     Ok(())
//! }
//! ```
//!
//! ## IPv6 Support
//!
//! The transport fully supports IPv6 addresses. Use bracket notation for IPv6:
//!
//! ```no_run
//! use telltale_transport::TcpTransportConfig;
//!
//! // IPv6 loopback
//! let config = TcpTransportConfig::new("Server", "[::1]:8080")
//!     .allow_unauthenticated_for_trusted_network()
//!     .with_peer("Client", "[::1]:8081");
//!
//! // IPv6 any address (dual-stack binding)
//! let dual_stack = TcpTransportConfig::new("Server", "[::]:8080")
//!     .allow_unauthenticated_for_trusted_network();
//!
//! // Mixed IPv4 and IPv6 peers
//! let mixed = TcpTransportConfig::new("Gateway", "0.0.0.0:8080")
//!     .allow_unauthenticated_for_trusted_network()
//!     .with_peer("IPv4Peer", "192.168.1.100:8081")
//!     .with_peer("IPv6Peer", "[2001:db8::1]:8082");
//! ```
//!
//! Environment variables also support IPv6:
//!
//! ```bash
//! export TELLTALE_ALICE_ENDPOINT=[::1]:8080
//! export TELLTALE_BOB_ENDPOINT=[2001:db8::1]:8081
//! ```
//!
//! ## Message Framing
//!
//! Messages are framed with a simple length-prefix protocol:
//!
//! ```text
//! +----------------+------------------+
//! | Length (4 bytes) | Payload (N bytes) |
//! | (big-endian u32) |                  |
//! +----------------+------------------+
//! ```
//!
//! ## Connection Protocol
//!
//! When a connection is established, the connecting peer sends its role name
//! (also length-prefixed) so the receiving peer can route messages correctly.

#![allow(
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]

mod config;
mod error;
mod factory;
mod resolver;
mod transport;

// Configuration
pub use config::{RetryConfig, TcpTransportConfig};

// Errors
pub use error::{TcpResult, TcpTransportError};

// Factory
pub use factory::TcpTransportFactory;

// Resolver
pub use resolver::{
    EndpointResolver, EnvResolver, EnvResolverConfigError, ResolutionFailureReason, ResolverError,
    StaticResolver,
};

// Transport
pub use transport::{TcpTransport, TransportState};

// Re-export core traits and types for convenience
pub use telltale_runtime::topology::{Transport, TransportError, TransportResult};
pub use telltale_runtime::RoleName;
