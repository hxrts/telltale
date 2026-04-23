//! Shared low-level TCP wire helpers for topology transports.
//!
//! This module intentionally does not decide whether a peer is authenticated.
//! It only owns the mechanical wire contract shared by the runtime topology TCP
//! helper and the example `telltale-transport` TCP implementation.

use std::io;
use std::time::Duration;

use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::time::timeout;

use super::TransportError;

/// Four-byte TCP wire magic.
pub const TCP_WIRE_MAGIC: [u8; 4] = *b"TTL1";
/// TCP wire version.
pub const TCP_WIRE_VERSION: u8 = 1;
/// Maximum accepted role-name length in bytes.
pub const TCP_ROLE_NAME_LEN_MAX_BYTES: usize = 1024;

/// Low-level TCP wire errors.
#[derive(Debug, thiserror::Error)]
pub enum TcpWireError {
    /// IO error during network operations.
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    /// Operation timed out.
    #[error("operation timed out")]
    Timeout,

    /// Unsupported wire protocol.
    #[error("unsupported protocol: {0}")]
    UnsupportedProtocol(String),

    /// Invalid wire message.
    #[error("invalid message: {0}")]
    InvalidMessage(String),
}

impl From<TcpWireError> for TransportError {
    fn from(error: TcpWireError) -> Self {
        match error {
            TcpWireError::Io(error) => TransportError::IoError(error),
            TcpWireError::Timeout => TransportError::Timeout,
            TcpWireError::UnsupportedProtocol(message) => {
                TransportError::UnsupportedProtocol(message)
            }
            TcpWireError::InvalidMessage(message) => TransportError::ReceiveFailed(message),
        }
    }
}

/// Read exactly `buf.len()` bytes within `read_timeout`.
pub async fn read_exact_timeout<R>(
    reader: &mut R,
    buf: &mut [u8],
    read_timeout: Duration,
) -> Result<(), TcpWireError>
where
    R: AsyncRead + Unpin,
{
    timeout(read_timeout, reader.read_exact(buf))
        .await
        .map_err(|_| TcpWireError::Timeout)?
        .map(|_| ())
        .map_err(Into::into)
}

/// Write all bytes within `write_timeout`.
pub async fn write_all_timeout<W>(
    writer: &mut W,
    bytes: &[u8],
    write_timeout: Duration,
) -> Result<(), TcpWireError>
where
    W: AsyncWrite + Unpin,
{
    timeout(write_timeout, writer.write_all(bytes))
        .await
        .map_err(|_| TcpWireError::Timeout)?
        .map_err(Into::into)
}

/// Flush a writer within `write_timeout`.
pub async fn flush_timeout<W>(writer: &mut W, write_timeout: Duration) -> Result<(), TcpWireError>
where
    W: AsyncWrite + Unpin,
{
    timeout(write_timeout, writer.flush())
        .await
        .map_err(|_| TcpWireError::Timeout)?
        .map_err(Into::into)
}

/// Read a big-endian `u32`.
pub async fn read_u32_timeout<R>(
    reader: &mut R,
    read_timeout: Duration,
) -> Result<u32, TcpWireError>
where
    R: AsyncRead + Unpin,
{
    let mut bytes = [0_u8; 4];
    read_exact_timeout(reader, &mut bytes, read_timeout).await?;
    Ok(u32::from_be_bytes(bytes))
}

/// Write a big-endian `u32`.
pub async fn write_u32_timeout<W>(
    writer: &mut W,
    value: u32,
    write_timeout: Duration,
) -> Result<(), TcpWireError>
where
    W: AsyncWrite + Unpin,
{
    write_all_timeout(writer, &value.to_be_bytes(), write_timeout).await
}

/// Write the shared TCP wire preamble.
pub async fn write_preamble<W>(writer: &mut W, write_timeout: Duration) -> Result<(), TcpWireError>
where
    W: AsyncWrite + Unpin,
{
    write_all_timeout(writer, &TCP_WIRE_MAGIC, write_timeout).await?;
    write_all_timeout(writer, &[TCP_WIRE_VERSION], write_timeout).await
}

/// Read and validate the shared TCP wire preamble.
pub async fn read_preamble<R>(reader: &mut R, read_timeout: Duration) -> Result<(), TcpWireError>
where
    R: AsyncRead + Unpin,
{
    let mut magic = [0_u8; 4];
    read_exact_timeout(reader, &mut magic, read_timeout).await?;
    if magic != TCP_WIRE_MAGIC {
        return Err(TcpWireError::UnsupportedProtocol(
            "invalid TCP wire magic".to_string(),
        ));
    }

    let mut version = [0_u8; 1];
    read_exact_timeout(reader, &mut version, read_timeout).await?;
    if version[0] != TCP_WIRE_VERSION {
        return Err(TcpWireError::UnsupportedProtocol(format!(
            "unsupported TCP wire version {}",
            version[0]
        )));
    }

    Ok(())
}

/// Write a length-prefixed role name.
pub async fn write_role_name<W>(
    writer: &mut W,
    role_bytes: &[u8],
    write_timeout: Duration,
) -> Result<(), TcpWireError>
where
    W: AsyncWrite + Unpin,
{
    let role_len = u32::try_from(role_bytes.len()).map_err(|_| {
        TcpWireError::InvalidMessage("role name exceeds u32 length prefix".to_string())
    })?;
    write_u32_timeout(writer, role_len, write_timeout).await?;
    write_all_timeout(writer, role_bytes, write_timeout).await
}

/// Read a length-prefixed role name as raw UTF-8 bytes.
pub async fn read_role_name_bytes<R>(
    reader: &mut R,
    read_timeout: Duration,
) -> Result<Vec<u8>, TcpWireError>
where
    R: AsyncRead + Unpin,
{
    let role_len = read_u32_timeout(reader, read_timeout).await?;
    let role_len = usize::try_from(role_len)
        .map_err(|_| TcpWireError::InvalidMessage("invalid role name length".to_string()))?;
    if role_len > TCP_ROLE_NAME_LEN_MAX_BYTES {
        return Err(TcpWireError::InvalidMessage(format!(
            "sender role header is {role_len} bytes, max is {TCP_ROLE_NAME_LEN_MAX_BYTES}"
        )));
    }

    let mut role_buf = vec![0_u8; role_len];
    read_exact_timeout(reader, &mut role_buf, read_timeout).await?;
    Ok(role_buf)
}

/// Read a payload length, validated against the shared message-length bound.
pub async fn read_payload_len<R>(
    reader: &mut R,
    read_timeout: Duration,
) -> Result<telltale_types::MessageLenBytes, TcpWireError>
where
    R: AsyncRead + Unpin,
{
    let payload_len = read_u32_timeout(reader, read_timeout).await?;
    telltale_types::MessageLenBytes::try_new(payload_len)
        .map_err(|error| TcpWireError::InvalidMessage(error.to_string()))
}

/// Write a payload length.
pub async fn write_payload_len<W>(
    writer: &mut W,
    payload_len: telltale_types::MessageLenBytes,
    write_timeout: Duration,
) -> Result<(), TcpWireError>
where
    W: AsyncWrite + Unpin,
{
    write_u32_timeout(writer, payload_len.get(), write_timeout).await
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_TIMEOUT: Duration = Duration::from_secs(1);

    #[tokio::test]
    async fn tcp_wire_preamble_round_trips() {
        let (mut client, mut server) = tokio::io::duplex(64);

        let writer = tokio::spawn(async move { write_preamble(&mut client, TEST_TIMEOUT).await });
        read_preamble(&mut server, TEST_TIMEOUT)
            .await
            .expect("valid preamble should be accepted");
        writer
            .await
            .expect("writer task should not panic")
            .expect("preamble write should succeed");
    }

    #[tokio::test]
    async fn tcp_wire_rejects_invalid_magic() {
        let (mut client, mut server) = tokio::io::duplex(64);

        let writer = tokio::spawn(async move {
            write_all_timeout(&mut client, b"NOPE", TEST_TIMEOUT).await?;
            write_all_timeout(&mut client, &[TCP_WIRE_VERSION], TEST_TIMEOUT).await
        });
        let err = read_preamble(&mut server, TEST_TIMEOUT)
            .await
            .expect_err("invalid magic should be rejected");
        assert!(matches!(err, TcpWireError::UnsupportedProtocol(_)));
        writer
            .await
            .expect("writer task should not panic")
            .expect("invalid preamble bytes should write");
    }

    #[tokio::test]
    async fn tcp_wire_rejects_invalid_version() {
        let (mut client, mut server) = tokio::io::duplex(64);

        let writer = tokio::spawn(async move {
            write_all_timeout(&mut client, &TCP_WIRE_MAGIC, TEST_TIMEOUT).await?;
            write_all_timeout(&mut client, &[TCP_WIRE_VERSION + 1], TEST_TIMEOUT).await
        });
        let err = read_preamble(&mut server, TEST_TIMEOUT)
            .await
            .expect_err("invalid version should be rejected");
        assert!(matches!(err, TcpWireError::UnsupportedProtocol(_)));
        writer
            .await
            .expect("writer task should not panic")
            .expect("invalid version bytes should write");
    }

    #[tokio::test]
    async fn tcp_wire_rejects_oversized_role_name() {
        let (mut client, mut server) = tokio::io::duplex(64);

        let writer = tokio::spawn(async move {
            write_u32_timeout(
                &mut client,
                u32::try_from(TCP_ROLE_NAME_LEN_MAX_BYTES + 1).expect("test role length fits u32"),
                TEST_TIMEOUT,
            )
            .await
        });
        let err = read_role_name_bytes(&mut server, TEST_TIMEOUT)
            .await
            .expect_err("oversized role name should be rejected");
        assert!(matches!(err, TcpWireError::InvalidMessage(_)));
        writer
            .await
            .expect("writer task should not panic")
            .expect("oversized role length should write");
    }

    #[tokio::test]
    async fn tcp_wire_rejects_oversized_payload_len() {
        let (mut client, mut server) = tokio::io::duplex(64);

        let writer = tokio::spawn(async move {
            write_u32_timeout(
                &mut client,
                telltale_types::MAX_MESSAGE_LEN_BYTES + 1,
                TEST_TIMEOUT,
            )
            .await
        });
        let err = read_payload_len(&mut server, TEST_TIMEOUT)
            .await
            .expect_err("oversized payload length should be rejected");
        assert!(matches!(err, TcpWireError::InvalidMessage(_)));
        writer
            .await
            .expect("writer task should not panic")
            .expect("oversized payload length should write");
    }

    #[tokio::test]
    async fn tcp_wire_read_timeout_is_reported() {
        let (_client, mut server) = tokio::io::duplex(64);
        let mut buf = [0_u8; 1];

        let err = read_exact_timeout(&mut server, &mut buf, Duration::from_millis(1))
            .await
            .expect_err("read with no writer should time out");
        assert!(matches!(err, TcpWireError::Timeout));
    }
}
