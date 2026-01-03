//! Error types for TCP transport.

use std::io;
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

    /// Transport not started.
    #[error("transport not started")]
    NotStarted,

    /// Transport already started.
    #[error("transport already started")]
    AlreadyStarted,

    /// Invalid message format.
    #[error("invalid message: {0}")]
    InvalidMessage(String),

    /// Connection closed unexpectedly.
    #[error("connection closed")]
    ConnectionClosed,

    /// Operation timed out.
    #[error("operation timed out")]
    Timeout,
}

/// Result type for TCP transport operations.
pub type TcpResult<T> = std::result::Result<T, TcpTransportError>;
