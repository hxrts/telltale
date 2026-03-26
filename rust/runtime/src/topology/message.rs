//! Bounded message type for transport.

use super::limits::MAX_MESSAGE_SIZE_BYTES;
use thiserror::Error;

/// Error creating a message.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum MessageError {
    /// Message exceeds maximum size.
    #[error("message too large: {size_bytes} bytes exceeds maximum {max_bytes} bytes")]
    TooLarge {
        /// Actual size of the message.
        size_bytes: u32,
        /// Maximum allowed size.
        max_bytes: u32,
    },
}

/// A bounded message for transport.
///
/// Messages are validated on construction to enforce size limits.
/// The maximum size is defined by [`MAX_MESSAGE_SIZE_BYTES`].
#[derive(Debug, Clone)]
#[must_use]
pub struct Message {
    bytes: Vec<u8>,
}

impl Message {
    /// Create a new message from bytes.
    ///
    /// Returns an error if the message exceeds [`MAX_MESSAGE_SIZE_BYTES`].
    pub fn new(bytes: Vec<u8>) -> Result<Self, MessageError> {
        let size = bytes.len();
        if size > MAX_MESSAGE_SIZE_BYTES as usize {
            return Err(MessageError::TooLarge {
                size_bytes: size as u32,
                max_bytes: MAX_MESSAGE_SIZE_BYTES,
            });
        }
        Ok(Self { bytes })
    }

    /// Create a message without validation (for trusted internal use).
    ///
    /// # Panics
    ///
    /// Debug builds will panic if `bytes.len() > MAX_MESSAGE_SIZE_BYTES`.
    pub(crate) fn new_unchecked(bytes: Vec<u8>) -> Self {
        debug_assert!(
            bytes.len() <= MAX_MESSAGE_SIZE_BYTES as usize,
            "Message::new_unchecked called with {} bytes, max is {}",
            bytes.len(),
            MAX_MESSAGE_SIZE_BYTES
        );
        Self { bytes }
    }

    /// Consume the message and return the underlying bytes.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// View the message bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Message length in bytes.
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Check if the message is empty.
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }
}

impl From<Message> for Vec<u8> {
    fn from(msg: Message) -> Self {
        msg.bytes
    }
}

impl AsRef<[u8]> for Message {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_message_new_valid() {
        let bytes = vec![1, 2, 3, 4, 5];
        let msg = Message::new(bytes.clone()).unwrap();
        assert_eq!(msg.as_bytes(), &bytes);
        assert_eq!(msg.len(), 5);
        assert!(!msg.is_empty());
    }

    #[test]
    fn test_message_empty() {
        let msg = Message::new(vec![]).unwrap();
        assert!(msg.is_empty());
        assert_eq!(msg.len(), 0);
    }

    #[test]
    fn test_message_too_large() {
        let bytes = vec![0u8; (MAX_MESSAGE_SIZE_BYTES + 1) as usize];
        let result = Message::new(bytes);
        assert!(matches!(
            result,
            Err(MessageError::TooLarge {
                size_bytes,
                max_bytes
            }) if size_bytes == MAX_MESSAGE_SIZE_BYTES + 1 && max_bytes == MAX_MESSAGE_SIZE_BYTES
        ));
    }

    #[test]
    fn test_message_max_size() {
        let bytes = vec![0u8; MAX_MESSAGE_SIZE_BYTES as usize];
        let msg = Message::new(bytes).unwrap();
        assert_eq!(msg.len(), MAX_MESSAGE_SIZE_BYTES as usize);
    }

    #[test]
    fn test_message_into_bytes() {
        let bytes = vec![1, 2, 3];
        let msg = Message::new(bytes.clone()).unwrap();
        assert_eq!(msg.into_bytes(), bytes);
    }

    #[test]
    fn test_message_as_ref() {
        let bytes = vec![1, 2, 3];
        let msg = Message::new(bytes.clone()).unwrap();
        let slice: &[u8] = msg.as_ref();
        assert_eq!(slice, &bytes);
    }
}
