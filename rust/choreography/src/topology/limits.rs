//! Transport layer constants and limits.
//!
//! All bounds are explicit and named with units per style guide.

/// Maximum message size in bytes (16 MB).
pub const MAX_MESSAGE_SIZE_BYTES: u32 = 16 * 1024 * 1024;

/// Maximum role name length in bytes.
pub const MAX_ROLE_NAME_LEN: usize = 256;

/// Default channel buffer size for in-memory transport.
pub const CHANNEL_BUFFER_SIZE_DEFAULT: u32 = 32;

/// Maximum retry attempts for connection.
pub const RETRY_ATTEMPTS_MAX: u32 = 10;

/// Initial retry backoff delay in milliseconds.
pub const RETRY_BACKOFF_INITIAL_MS: u64 = 100;

/// Maximum retry backoff delay in milliseconds.
pub const RETRY_BACKOFF_MAX_MS: u64 = 30_000;

/// Default backoff multiplier.
pub const RETRY_BACKOFF_MULTIPLIER: f64 = 2.0;
