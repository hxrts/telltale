//! TCP Transport for Rumpsteak Session Types
//!
//! This crate provides a production-ready TCP transport implementation for
//! the Rumpsteak session types library.
//!
//! ## Features
//!
//! - Length-prefixed message framing for reliable delivery
//! - Automatic connection management with retry and backoff
//! - Role-based addressing (each role has a unique address)
//! - Graceful shutdown support
//! - Tracing instrumentation for observability
//!
//! ## Example
//!
//! ```no_run
//! use rumpsteak_transport_tcp::{TcpTransport, TcpTransportConfig};
//! use rumpsteak_aura_choreography::Transport;
//! use std::collections::HashMap;
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // Configure the transport
//!     let config = TcpTransportConfig::new("Alice", "127.0.0.1:8080")
//!         .with_peer("Bob", "127.0.0.1:8081")
//!         .with_peer("Carol", "127.0.0.1:8082");
//!
//!     // Create and start the transport
//!     let transport = TcpTransport::new(config);
//!     transport.start().await?;
//!
//!     // Connect to peers
//!     transport.connect_to("Bob").await?;
//!
//!     // Use with your session type protocol
//!     transport.send("Bob", b"Hello".to_vec()).await?;
//!     let response = transport.recv("Bob").await?;
//!
//!     transport.close().await?;
//!     Ok(())
//! }
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

mod config;
mod error;
mod transport;

pub use config::TcpTransportConfig;
pub use error::TcpTransportError;
pub use transport::TcpTransport;

// Re-export Transport trait for convenience
pub use rumpsteak_aura_choreography::Transport;
