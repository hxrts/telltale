//! Error types for TCP transport.

use std::io;
use telltale_runtime::topology::wire::TcpWireError;
use thiserror::Error;

/// Errors specific to TCP transport operations.
#[derive(Debug, Error)]
pub enum TcpTransportError {
    /// IO error during network operations.
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    /// Failed to connect to a peer.
    #[error("connection to {peer} failed: {reason}")]
    ConnectionFailed {
        /// The peer we failed to connect to.
        peer: String,
        /// The reason for the failure.
        reason: String,
    },

    /// Peer not found in configuration.
    #[error("unknown peer: {0}")]
    UnknownPeer(String),

    /// Peer role already has a live inbound connection.
    #[error("duplicate peer connection: {0}")]
    DuplicatePeer(String),

    /// Authentication mode was not explicitly configured.
    #[error("authentication mode not configured")]
    AuthenticationModeNotConfigured,

    /// Peer authentication failed.
    #[error("authentication failed: {0}")]
    AuthenticationFailed(String),

    /// Transport not started.
    #[error("transport not started")]
    NotStarted,

    /// Transport already started.
    #[error("transport already started")]
    AlreadyStarted,

    /// Invalid message format.
    #[error("invalid message: {0}")]
    InvalidMessage(String),

    /// Unsupported wire protocol.
    #[error("unsupported protocol: {0}")]
    UnsupportedProtocol(String),

    /// Connection closed unexpectedly.
    #[error("connection closed")]
    ConnectionClosed,

    /// Transport-level resource limit exceeded.
    #[error("resource limit exceeded: {0}")]
    ResourceLimitExceeded(String),

    /// Operation timed out.
    #[error("operation timed out")]
    Timeout,
}

/// Result type for TCP transport operations.
pub type TcpResult<T> = std::result::Result<T, TcpTransportError>;

impl From<TcpWireError> for TcpTransportError {
    fn from(error: TcpWireError) -> Self {
        match error {
            TcpWireError::Io(error) => Self::Io(error),
            TcpWireError::Timeout => Self::Timeout,
            TcpWireError::UnsupportedProtocol(message) => Self::UnsupportedProtocol(message),
            TcpWireError::InvalidMessage(message) => Self::InvalidMessage(message),
        }
    }
}
