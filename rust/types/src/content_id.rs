//! Content Addressing for Session Types
//!
//! This module provides content-addressable identifiers for protocol artifacts.
//! Content IDs enable structural sharing, memoization, and deterministic verification.
//!
//! # Design
//!
//! The hash algorithm is abstracted via the `Hasher` trait, allowing users to swap
//! implementations for different use cases (performance, ZK compatibility, etc.).
//! SHA-256 is the default implementation.
//!
//! # Lean Correspondence
//!
//! This module corresponds to `lean/Rumpsteak/Protocol/ContentId.lean`.

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
#[derive(Clone, Default, Debug, PartialEq, Eq, Hash)]
pub struct Sha256Hasher;

impl Hasher for Sha256Hasher {
    const HASH_SIZE: usize = 32;

    fn digest(data: &[u8]) -> Vec<u8> {
        // Simple SHA-256 implementation using the standard approach
        // In production, this would use the `sha2` crate
        sha256_hash(data)
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

// ============================================================================
// SHA-256 Implementation (minimal, for bootstrapping)
// ============================================================================

/// Minimal SHA-256 implementation.
///
/// This is a straightforward implementation for bootstrapping.
/// In production builds, consider using the `sha2` crate for better performance.
fn sha256_hash(data: &[u8]) -> Vec<u8> {
    // SHA-256 constants (first 32 bits of fractional parts of cube roots of first 64 primes)
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    // Initial hash values (first 32 bits of fractional parts of square roots of first 8 primes)
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    // Pre-processing: pad message
    let mut msg = data.to_vec();
    let original_len_bits = (data.len() as u64) * 8;

    // Append bit '1' to message
    msg.push(0x80);

    // Append zeros until message length ≡ 448 (mod 512)
    while (msg.len() % 64) != 56 {
        msg.push(0x00);
    }

    // Append original length as 64-bit big-endian
    msg.extend_from_slice(&original_len_bits.to_be_bytes());

    // Process message in 512-bit chunks
    for chunk in msg.chunks(64) {
        let mut w = [0u32; 64];

        // Break chunk into sixteen 32-bit big-endian words
        for (i, word_bytes) in chunk.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([word_bytes[0], word_bytes[1], word_bytes[2], word_bytes[3]]);
        }

        // Extend the sixteen 32-bit words into sixty-four 32-bit words
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        // Initialize working variables
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;

        // Compression function main loop
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        // Add compressed chunk to current hash value
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    // Produce final hash value (big-endian)
    let mut result = Vec::with_capacity(32);
    for word in &h {
        result.extend_from_slice(&word.to_be_bytes());
    }
    result
}

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
