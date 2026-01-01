//! Error types for TCP transport.

use rumpsteak_aura_choreography::identifiers::RoleName;
use rumpsteak_aura_choreography::TransportError;
use std::io;
use thiserror::Error;

/// Errors specific to TCP transport operations.
#[derive(Debug, Error)]
pub enum TcpTransportError {
    /// IO error during network operations.
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    /// Failed to connect to a peer.
    #[error("Connection to {peer} failed: {reason}")]
    ConnectionFailed { peer: String, reason: String },

    /// Peer not found in configuration.
    #[error("Unknown peer: {0}")]
    UnknownPeer(String),

    /// Transport not started.
    #[error("Transport not started")]
    NotStarted,

    /// Transport already started.
    #[error("Transport already started")]
    AlreadyStarted,

    /// Invalid message format.
    #[error("Invalid message: {0}")]
    InvalidMessage(String),

    /// Connection closed unexpectedly.
    #[error("Connection closed")]
    ConnectionClosed,

    /// Operation timed out.
    #[error("Operation timed out")]
    Timeout,
}

impl From<TcpTransportError> for TransportError {
    fn from(err: TcpTransportError) -> Self {
        match err {
            TcpTransportError::Io(e) => TransportError::IoError(e),
            TcpTransportError::ConnectionFailed { peer, reason } => {
                TransportError::ConnectionFailed(format!("{}: {}", peer, reason))
            }
            TcpTransportError::UnknownPeer(peer) => {
                // Peer names are validated at configuration time
                TransportError::UnknownRole(
                    RoleName::new(&peer).unwrap_or_else(|_| RoleName::from_static("unknown")),
                )
            }
            TcpTransportError::NotStarted => TransportError::NotReady,
            TcpTransportError::AlreadyStarted => {
                TransportError::ConnectionFailed("Already started".to_string())
            }
            TcpTransportError::InvalidMessage(msg) => TransportError::ReceiveFailed(msg),
            TcpTransportError::ConnectionClosed => TransportError::ChannelClosed,
            TcpTransportError::Timeout => TransportError::Timeout,
        }
    }
}

/// Result type for TCP transport operations.
pub type Result<T> = std::result::Result<T, TcpTransportError>;
