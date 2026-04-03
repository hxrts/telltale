//! Content Addressing for Session Types
//!
//! This module provides content-addressable identifiers for protocol artifacts.
//! Content IDs enable structural sharing, memoization, and deterministic verification.
//!
//! # Design
//!
//! The hash algorithm is abstracted via the `Hasher` trait, allowing users to swap
//! implementations for different use cases (performance, ZK compatibility, etc.).
//!
//! # Lean Correspondence
//!
//! This module corresponds to `lean/SessionTypes/ContentIdentityPolicy.lean`.

#[cfg(feature = "sha256")]
use sha2::Digest;
use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;

/// Trait for hash algorithms used in content addressing.
///
/// Implementors must provide a deterministic hash function that maps
/// arbitrary byte sequences to fixed-size digests.
///
/// # Example
///
/// ```
/// use telltale_types::content_id::{Blake3Hasher, Hasher};
///
/// let data = b"hello world";
/// let hash = Blake3Hasher::digest(data);
/// assert_eq!(hash.len(), Blake3Hasher::HASH_SIZE);
/// ```
pub trait Hasher: Clone + Default + PartialEq + Send + Sync + 'static {
    /// Fixed-size digest type produced by this hasher.
    type Digest: AsRef<[u8]> + Clone + PartialEq + Eq + Hash + Send + Sync + 'static;

    /// Size of the hash output in bytes.
    const HASH_SIZE: usize;

    /// Compute the cryptographic digest of the input data.
    ///
    /// This function must be deterministic: the same input always produces
    /// the same output.
    fn digest(data: &[u8]) -> Self::Digest;

    /// Name of the hash algorithm (for display/debugging).
    fn algorithm_name() -> &'static str;
}

/// BLAKE3 hasher implementation (default).
///
/// BLAKE3 is chosen as the default because:
/// - Fast on modern CPUs
/// - Deterministic 256-bit output
/// - Strong implementation ergonomics for high-throughput content addressing
/// - Good fit for memoization-heavy protocol tooling
#[derive(Clone, Default, Debug, PartialEq, Eq, Hash)]
pub struct Blake3Hasher;

impl Hasher for Blake3Hasher {
    type Digest = [u8; 32];

    const HASH_SIZE: usize = 32;

    fn digest(data: &[u8]) -> Self::Digest {
        *blake3::hash(data).as_bytes()
    }

    fn algorithm_name() -> &'static str {
        "blake3"
    }
}

/// Central default hasher policy for content addressing.
///
/// Higher layers should prefer this alias over naming a concrete hash
/// implementation directly so the workspace can change defaults in one place.
pub type DefaultContentHasher = Blake3Hasher;

/// SHA-256 hasher implementation.
///
/// SHA-256 remains available as an explicit alternative when compatibility
/// with external systems or proof assumptions requires it.
#[cfg(feature = "sha256")]
#[derive(Clone, Default, Debug, PartialEq, Eq, Hash)]
pub struct Sha256Hasher;

#[cfg(feature = "sha256")]
impl Hasher for Sha256Hasher {
    type Digest = [u8; 32];

    const HASH_SIZE: usize = 32;

    fn digest(data: &[u8]) -> Self::Digest {
        sha2::Sha256::digest(data).into()
    }

    fn algorithm_name() -> &'static str {
        "sha256"
    }
}

/// Content identifier parameterized by hash algorithm.
///
/// A `ContentId` is a cryptographic fingerprint of a value's canonical
/// serialization. Two values with the same ContentId are considered
/// structurally equivalent (modulo α-equivalence for types with binders).
///
/// # Type Parameter
///
/// - `H`: The hash algorithm to use (default: `DefaultContentHasher`)
///
/// # Examples
///
/// ```
/// use telltale_types::content_id::{ContentId, DefaultContentHasher};
///
/// let cid: ContentId<DefaultContentHasher> = ContentId::from_bytes(b"test data");
/// assert_eq!(cid.as_bytes().len(), 32);
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ContentId<H: Hasher = DefaultContentHasher> {
    hash: H::Digest,
    _hasher: PhantomData<H>,
}

/// Errors that can occur when constructing a ContentId.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContentIdError {
    expected: usize,
    actual: usize,
}

impl ContentIdError {
    #[must_use]
    pub fn invalid_length(expected: usize, actual: usize) -> Self {
        Self { expected, actual }
    }
}

impl fmt::Display for ContentIdError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "hash length {} doesn't match expected size {}",
            self.actual, self.expected
        )
    }
}

impl std::error::Error for ContentIdError {}

impl<H: Hasher> ContentId<H> {
    /// Create a ContentId by hashing raw bytes.
    #[must_use]
    pub fn from_bytes(data: &[u8]) -> Self {
        Self {
            hash: H::digest(data),
            _hasher: PhantomData,
        }
    }

    /// Create a ContentId from a pre-computed hash.
    ///
    /// # Errors
    ///
    /// Returns [`ContentIdError`] if the hash length doesn't match the hasher's output size.
    pub fn from_hash(hash: impl AsRef<[u8]>) -> Result<Self, ContentIdError>
    where
        for<'a> H::Digest: TryFrom<&'a [u8]>,
    {
        let bytes = hash.as_ref();
        if bytes.len() != H::HASH_SIZE {
            return Err(ContentIdError::invalid_length(H::HASH_SIZE, bytes.len()));
        }
        let digest = H::Digest::try_from(bytes)
            .map_err(|_| ContentIdError::invalid_length(H::HASH_SIZE, bytes.len()))?;
        Ok(Self {
            hash: digest,
            _hasher: PhantomData,
        })
    }

    /// Get the raw hash bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.hash.as_ref()
    }

    /// Convert to a hexadecimal string.
    #[must_use]
    pub fn to_hex(&self) -> String {
        self.hash
            .as_ref()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    /// Get the hash algorithm name.
    #[must_use]
    pub fn algorithm(&self) -> &'static str {
        H::algorithm_name()
    }
}

impl<H: Hasher> fmt::Debug for ContentId<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Show first 8 bytes in hex for readability
        let short_hex: String = self
            .hash
            .as_ref()
            .iter()
            .take(8)
            .map(|b| format!("{b:02x}"))
            .collect();
        write!(f, "ContentId<{}>({short_hex}...)", H::algorithm_name())
    }
}

impl<H: Hasher> fmt::Display for ContentId<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_hex())
    }
}

/// Convenience type alias for default-hasher content IDs.
pub type DefaultContentId = ContentId<DefaultContentHasher>;

/// Convenience type alias for BLAKE3 content IDs.
pub type ContentIdBlake3 = ContentId<Blake3Hasher>;

/// Convenience type alias for SHA-256 content IDs.
#[cfg(feature = "sha256")]
pub type ContentIdSha256 = ContentId<Sha256Hasher>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_blake3_empty() {
        let hash = Blake3Hasher::digest(b"");
        let hex: String = hash.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        );
    }

    #[test]
    fn test_blake3_hello() {
        let hash = Blake3Hasher::digest(b"hello");
        let hex: String = hash.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "ea8f163db38682925e4491c5e58d4bb3506ef8c14eb78a86e908c5624a67200f"
        );
    }

    #[cfg(feature = "sha256")]
    #[test]
    fn test_sha256_empty() {
        // SHA-256 of empty string
        let hash = Sha256Hasher::digest(b"");
        let hex: String = hash.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[cfg(feature = "sha256")]
    #[test]
    fn test_sha256_hello() {
        // SHA-256 of "hello"
        let hash = Sha256Hasher::digest(b"hello");
        let hex: String = hash.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
        );
    }

    #[test]
    fn test_content_id_from_bytes() {
        let cid = ContentIdBlake3::from_bytes(b"test");
        assert_eq!(cid.as_bytes().len(), 32);
    }

    #[test]
    fn test_content_id_deterministic() {
        let cid1 = ContentIdBlake3::from_bytes(b"same data");
        let cid2 = ContentIdBlake3::from_bytes(b"same data");
        assert_eq!(cid1, cid2);
    }

    #[test]
    fn test_content_id_different() {
        let cid1 = ContentIdBlake3::from_bytes(b"data1");
        let cid2 = ContentIdBlake3::from_bytes(b"data2");
        assert_ne!(cid1, cid2);
    }

    #[test]
    fn test_content_id_hex() {
        let cid = ContentIdBlake3::from_bytes(b"");
        assert_eq!(
            cid.to_hex(),
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        );
    }

    #[test]
    fn test_content_id_debug() {
        let cid = ContentIdBlake3::from_bytes(b"test");
        let debug = format!("{cid:?}");
        assert!(debug.contains("ContentId<blake3>"));
    }
}
