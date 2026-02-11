//! Verification model primitives aligned with the Lean VM typeclass.
//!
//! This module provides domain-separated hashing, signing/verification helpers,
//! and a Merkle authentication tree for commitment proofs.

use std::hash::{Hash as StdHash, Hasher};

use serde::{Deserialize, Serialize};

use crate::coroutine::Value;
use crate::instr::Endpoint;

/// Domain-separated 32-byte hash.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Hash(pub [u8; 32]);

/// Hash domain tags to avoid cross-domain collisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum HashTag {
    /// Generic value hashing.
    Value,
    /// Signed value digest.
    SignedValue,
    /// Merkle tree leaf hash.
    MerkleLeaf,
    /// Merkle tree internal node hash.
    MerkleNode,
    /// Resource commitment hash.
    Commitment,
    /// Nullifier hash for consumption tracking.
    Nullifier,
    /// Signing key derivation hash.
    SigningKey,
}

impl HashTag {
    fn domain_byte(self) -> u8 {
        match self {
            Self::Value => 0x01,
            Self::SignedValue => 0x02,
            Self::MerkleLeaf => 0x03,
            Self::MerkleNode => 0x04,
            Self::Commitment => 0x05,
            Self::Nullifier => 0x06,
            Self::SigningKey => 0x07,
        }
    }
}

/// Signing key used to sign values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct SigningKey(pub [u8; 32]);

/// Verification key used to verify signatures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct VerifyingKey(pub [u8; 32]);

/// Signature attached to a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Signature {
    /// Signer identity.
    pub signer: VerifyingKey,
    /// Domain-separated payload digest.
    pub digest: Hash,
}

/// Commitment for resource/state commitments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Commitment(pub Hash);

/// Nullifier for one-time resource consumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Nullifier(pub Hash);

/// Verification model typeclass.
pub trait VerificationModel {
    /// Hash type.
    type Hash;
    /// Signing key type.
    type SigningKey;
    /// Verifying key type.
    type VerifyingKey;
    /// Signature type.
    type Signature;
    /// Commitment type.
    type Commitment;
    /// Nullifier type.
    type Nullifier;

    /// Domain-separated hash.
    fn hash(tag: HashTag, bytes: &[u8]) -> Self::Hash;
    /// Derive a verifying key from a signing key.
    fn deriving(signing: &Self::SigningKey) -> Self::VerifyingKey;
    /// Sign a value payload.
    fn sign_value(payload: &Value, key: &Self::SigningKey) -> Self::Signature;
    /// Verify a signed value payload.
    fn verify_signed_value(
        payload: &Value,
        signature: &Self::Signature,
        key: &Self::VerifyingKey,
    ) -> bool;
    /// Compute a commitment for a value.
    fn commitment(payload: &Value) -> Self::Commitment;
    /// Compute a nullifier for a value.
    fn nullifier(payload: &Value) -> Self::Nullifier;
}

/// Default runtime verification model.
#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize)]
pub struct DefaultVerificationModel;

fn hash_bytes_with_tag(tag: HashTag, bytes: &[u8]) -> Hash {
    // Portable deterministic pseudo-hash suitable for replay/consensus tests.
    // Crypto-grade implementations can replace this model behind the trait.
    let mut out = [0_u8; 32];
    for block in 0_u64..4 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        tag.domain_byte().hash(&mut hasher);
        block.hash(&mut hasher);
        bytes.hash(&mut hasher);
        let digest = hasher.finish().to_le_bytes();
        let start = usize::try_from(block).expect("u64 block index fits in usize") * 8;
        out[start..start + 8].copy_from_slice(&digest);
    }
    Hash(out)
}

fn encode_value(value: &Value) -> Vec<u8> {
    serde_json::to_vec(value).unwrap_or_else(|_| format!("{value:?}").into_bytes())
}

impl VerificationModel for DefaultVerificationModel {
    type Hash = Hash;
    type SigningKey = SigningKey;
    type VerifyingKey = VerifyingKey;
    type Signature = Signature;
    type Commitment = Commitment;
    type Nullifier = Nullifier;

    fn hash(tag: HashTag, bytes: &[u8]) -> Self::Hash {
        hash_bytes_with_tag(tag, bytes)
    }

    fn deriving(signing: &Self::SigningKey) -> Self::VerifyingKey {
        let digest = hash_bytes_with_tag(HashTag::SigningKey, &signing.0);
        VerifyingKey(digest.0)
    }

    fn sign_value(payload: &Value, key: &Self::SigningKey) -> Self::Signature {
        sign_value(payload, key)
    }

    fn verify_signed_value(
        payload: &Value,
        signature: &Self::Signature,
        key: &Self::VerifyingKey,
    ) -> bool {
        verify_signed_value(payload, signature, key)
    }

    fn commitment(payload: &Value) -> Self::Commitment {
        Commitment(hash_bytes_with_tag(
            HashTag::Commitment,
            &encode_value(payload),
        ))
    }

    fn nullifier(payload: &Value) -> Self::Nullifier {
        Nullifier(hash_bytes_with_tag(
            HashTag::Nullifier,
            &encode_value(payload),
        ))
    }
}

/// Deterministically derive a signing key for an endpoint.
#[must_use]
pub fn signing_key_for_endpoint(endpoint: &Endpoint) -> SigningKey {
    let mut bytes = endpoint.sid.to_le_bytes().to_vec();
    bytes.extend_from_slice(endpoint.role.as_bytes());
    let digest = hash_bytes_with_tag(HashTag::SigningKey, &bytes);
    SigningKey(digest.0)
}

/// Deterministically derive a verifying key for an endpoint.
#[must_use]
pub fn verifying_key_for_endpoint(endpoint: &Endpoint) -> VerifyingKey {
    DefaultVerificationModel::deriving(&signing_key_for_endpoint(endpoint))
}

/// Sign one runtime value.
#[must_use]
pub fn sign_value(payload: &Value, key: &SigningKey) -> Signature {
    let verifying = DefaultVerificationModel::deriving(key);
    let mut bytes = verifying.0.to_vec();
    bytes.extend_from_slice(&encode_value(payload));
    let digest = hash_bytes_with_tag(HashTag::SignedValue, &bytes);
    Signature {
        signer: verifying,
        digest,
    }
}

/// Verify one signed runtime value.
#[must_use]
pub fn verify_signed_value(payload: &Value, signature: &Signature, key: &VerifyingKey) -> bool {
    if signature.signer != *key {
        return false;
    }
    let mut bytes = key.0.to_vec();
    bytes.extend_from_slice(&encode_value(payload));
    let expected = hash_bytes_with_tag(HashTag::SignedValue, &bytes);
    expected == signature.digest
}

/// Compatibility alias requested in discrepancy tracking.
#[allow(non_snake_case)]
#[must_use]
pub fn signValue(payload: &Value, key: &SigningKey) -> Signature {
    sign_value(payload, key)
}

/// Compatibility alias requested in discrepancy tracking.
#[allow(non_snake_case)]
#[must_use]
pub fn verifySignedValue(payload: &Value, signature: &Signature, key: &VerifyingKey) -> bool {
    verify_signed_value(payload, signature, key)
}

fn merge_hash_pair(left: Hash, right: Hash) -> Hash {
    let mut bytes = left.0.to_vec();
    bytes.extend_from_slice(&right.0);
    hash_bytes_with_tag(HashTag::MerkleNode, &bytes)
}

/// Merkle authentication path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthProof {
    /// Zero-based index of the leaf.
    pub index: usize,
    /// Sibling hashes from leaf level upward.
    pub siblings: Vec<Hash>,
    /// Whether each sibling hash is on the left side.
    pub sibling_on_left: Vec<bool>,
}

/// Merkle authentication tree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthTree {
    leaves: Vec<Hash>,
    levels: Vec<Vec<Hash>>,
}

impl AuthTree {
    /// Build an authentication tree from leaf payload hashes.
    #[must_use]
    pub fn new(leaves: Vec<Hash>) -> Self {
        if leaves.is_empty() {
            return Self {
                leaves,
                levels: vec![vec![hash_bytes_with_tag(HashTag::MerkleLeaf, &[])]],
            };
        }
        let mut levels = vec![leaves.clone()];
        let mut level = leaves.clone();
        while level.len() > 1 {
            let mut next = Vec::with_capacity(level.len().div_ceil(2));
            for chunk in level.chunks(2) {
                let left = chunk[0];
                let right = if chunk.len() == 2 { chunk[1] } else { chunk[0] };
                next.push(merge_hash_pair(left, right));
            }
            levels.push(next.clone());
            level = next;
        }
        Self { leaves, levels }
    }

    /// Root hash of the tree.
    #[must_use]
    pub fn root(&self) -> Hash {
        self.levels
            .last()
            .and_then(|level| level.first().copied())
            .unwrap_or_else(|| hash_bytes_with_tag(HashTag::MerkleLeaf, &[]))
    }

    /// Generate an authentication proof for a leaf index.
    #[must_use]
    pub fn prove(&self, index: usize) -> Option<AuthProof> {
        if index >= self.leaves.len() {
            return None;
        }
        let mut idx = index;
        let mut siblings = Vec::new();
        let mut sibling_on_left = Vec::new();
        for level in &self.levels {
            if level.len() <= 1 {
                break;
            }
            let pair_index = idx ^ 1;
            let sibling = if pair_index < level.len() {
                level[pair_index]
            } else {
                level[idx]
            };
            siblings.push(sibling);
            sibling_on_left.push(pair_index < idx);
            idx /= 2;
        }
        Some(AuthProof {
            index,
            siblings,
            sibling_on_left,
        })
    }

    /// Verify a proof against the expected root hash.
    #[must_use]
    pub fn verify(root: Hash, leaf: Hash, proof: &AuthProof) -> bool {
        if proof.siblings.len() != proof.sibling_on_left.len() {
            return false;
        }
        let mut current = leaf;
        let mut index = proof.index;
        for (sibling, on_left) in proof.siblings.iter().zip(proof.sibling_on_left.iter()) {
            let expected_on_left = index % 2 == 1;
            if *on_left != expected_on_left {
                return false;
            }
            current = if *on_left {
                merge_hash_pair(*sibling, current)
            } else {
                merge_hash_pair(current, *sibling)
            };
            index /= 2;
        }
        current == root
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signature_roundtrip() {
        let ep = Endpoint {
            sid: 9,
            role: "Alice".to_string(),
        };
        let sk = signing_key_for_endpoint(&ep);
        let vk = verifying_key_for_endpoint(&ep);
        let payload = Value::Nat(42);
        let sig = sign_value(&payload, &sk);
        assert!(verify_signed_value(&payload, &sig, &vk));
        assert!(!verify_signed_value(&Value::Nat(7), &sig, &vk));
    }

    #[test]
    fn auth_tree_proof_roundtrip() {
        let leaves = vec![
            hash_bytes_with_tag(HashTag::MerkleLeaf, b"a"),
            hash_bytes_with_tag(HashTag::MerkleLeaf, b"b"),
            hash_bytes_with_tag(HashTag::MerkleLeaf, b"c"),
        ];
        let tree = AuthTree::new(leaves.clone());
        let proof = tree.prove(1).expect("proof for valid index");
        assert!(AuthTree::verify(tree.root(), leaves[1], &proof));
    }
}
