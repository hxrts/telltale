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
//! This module corresponds to `lean/Rumpsteak/Protocol/ContentId.lean`.

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
/// use rumpsteak_types::content_id::{Hasher, Sha256Hasher};
///
/// let data = b"hello world";
/// let hash = Sha256Hasher::digest(data);
/// assert_eq!(hash.len(), Sha256Hasher::HASH_SIZE);
/// ```
pub trait Hasher: Clone + Default + PartialEq + Send + Sync + 'static {
    /// Size of the hash output in bytes.
    const HASH_SIZE: usize;

    /// Compute the cryptographic digest of the input data.
    ///
    /// This function must be deterministic: the same input always produces
    /// the same output.
    fn digest(data: &[u8]) -> Vec<u8>;

    /// Name of the hash algorithm (for display/debugging).
    fn algorithm_name() -> &'static str;
}

/// SHA-256 hasher implementation (default).
///
/// SHA-256 is chosen as the default because:
/// - Widely supported and well-understood
/// - 256-bit output provides strong collision resistance
/// - Compatible with most ZK systems
/// - Native hardware acceleration on modern CPUs
///
/// Uses `sha2` crate.
#[derive(Clone, Default, Debug, PartialEq, Eq, Hash)]
pub struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    const HASH_SIZE: usize = 32;

    fn digest(data: &[u8]) -> Vec<u8> {
        sha2::Sha256::digest(data).to_vec()
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
/// - `H`: The hash algorithm to use (default: `Sha256Hasher`)
///
/// # Examples
///
/// ```
/// use rumpsteak_types::content_id::{ContentId, Sha256Hasher};
///
/// let cid: ContentId<Sha256Hasher> = ContentId::from_bytes(b"test data");
/// assert_eq!(cid.as_bytes().len(), 32);
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ContentId<H: Hasher = Sha256Hasher> {
    hash: Vec<u8>,
    _hasher: PhantomData<H>,
}

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
    /// # Panics
    ///
    /// Panics if the hash length doesn't match the hasher's output size.
    #[must_use]
    pub fn from_hash(hash: Vec<u8>) -> Self {
        assert_eq!(
            hash.len(),
            H::HASH_SIZE,
            "Hash length {} doesn't match expected size {}",
            hash.len(),
            H::HASH_SIZE
        );
        Self {
            hash,
            _hasher: PhantomData,
        }
    }

    /// Get the raw hash bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.hash
    }

    /// Convert to a hexadecimal string.
    #[must_use]
    pub fn to_hex(&self) -> String {
        self.hash.iter().map(|b| format!("{b:02x}")).collect()
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

/// Convenience type alias for SHA-256 content IDs.
pub type ContentIdSha256 = ContentId<Sha256Hasher>;

#[cfg(test)]
mod tests {
    use super::*;

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
        let cid = ContentIdSha256::from_bytes(b"test");
        assert_eq!(cid.as_bytes().len(), 32);
    }

    #[test]
    fn test_content_id_deterministic() {
        let cid1 = ContentIdSha256::from_bytes(b"same data");
        let cid2 = ContentIdSha256::from_bytes(b"same data");
        assert_eq!(cid1, cid2);
    }

    #[test]
    fn test_content_id_different() {
        let cid1 = ContentIdSha256::from_bytes(b"data1");
        let cid2 = ContentIdSha256::from_bytes(b"data2");
        assert_ne!(cid1, cid2);
    }

    #[test]
    fn test_content_id_hex() {
        let cid = ContentIdSha256::from_bytes(b"");
        assert_eq!(
            cid.to_hex(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn test_content_id_debug() {
        let cid = ContentIdSha256::from_bytes(b"test");
        let debug = format!("{cid:?}");
        assert!(debug.contains("ContentId<sha256>"));
    }
}
