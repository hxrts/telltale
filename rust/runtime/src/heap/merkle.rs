//! # Merkle Tree Utilities
//!
//! Merkle tree construction and verification for heap state.
//!
//! ## Overview
//!
//! This module provides Merkle tree operations for heap state verification:
//! - Compute Merkle root from heap resources
//! - Generate inclusion proofs
//! - Verify inclusion proofs
//!
//! ## Lean Correspondence
//!
//! Merkle tree operations are currently Rust-only.

use super::heap_impl::Heap;
use super::encoding::{
    encode_heap_commitment_preimage, encode_merkle_node_preimage, encode_nullifier_leaf_preimage,
    encode_resource_leaf_preimage,
};
use super::resource::{Resource, ResourceId};
use std::marker::PhantomData;
use telltale_types::{DefaultContentHasher, Hasher};

/// Direction in a Merkle proof path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Sibling is on the left
    Left,
    /// Sibling is on the right
    Right,
}

/// A single step in a Merkle proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep<H: Hasher = DefaultContentHasher> {
    /// Direction: is this node a left or right sibling?
    pub direction: Direction,
    /// The sibling hash at this level
    pub sibling_hash: H::Digest,
}

/// A Merkle inclusion proof.
///
/// The proof consists of sibling hashes from leaf to root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleProof<H: Hasher = DefaultContentHasher> {
    /// The leaf hash being proven
    pub leaf_hash: H::Digest,
    /// Proof path from leaf to root
    pub path: Vec<ProofStep<H>>,
    /// The expected root hash
    pub root: H::Digest,
}

impl<H: Hasher> MerkleProof<H> {
    /// Verify this proof.
    pub fn verify(&self) -> bool {
        let computed_root =
            self.path
                .iter()
                .fold(self.leaf_hash.clone(), |current, step| {
                    match step.direction {
                        Direction::Left => {
                            merkle_node_hash::<H>(&step.sibling_hash, &current)
                        }
                        Direction::Right => {
                            merkle_node_hash::<H>(&current, &step.sibling_hash)
                        }
                    }
                });
        computed_root == self.root
    }
}

/// Hash two child digests to get a Merkle parent digest.
///
/// The hasher consumes a tagged preimage that contains the left child and
/// right child digests in order.
pub fn merkle_node_hash<H: Hasher>(left: &H::Digest, right: &H::Digest) -> H::Digest {
    let preimage = encode_merkle_node_preimage(left.as_ref(), right.as_ref());
    H::digest(&preimage)
}

/// Compute the digest of an active-resource leaf.
///
/// The hasher consumes a tagged preimage that contains the `ResourceId`
/// digest and the canonical resource bytes.
pub fn resource_leaf_hash<H: Hasher>(rid: &ResourceId<H>, resource: &Resource) -> H::Digest {
    let resource_bytes = resource.canonical_bytes();
    let preimage = encode_resource_leaf_preimage(rid.as_bytes(), &resource_bytes);
    H::digest(&preimage)
}

/// Compute the digest of a nullifier leaf.
///
/// The hasher consumes a tagged preimage that contains the `ResourceId`
/// digest bytes.
pub fn nullifier_leaf_hash<H: Hasher>(rid: &ResourceId<H>) -> H::Digest {
    let preimage = encode_nullifier_leaf_preimage(rid.as_bytes());
    H::digest(&preimage)
}

/// Empty tree root (hash of empty).
fn empty_root<H: Hasher>() -> H::Digest {
    H::digest(&[])
}

/// Merkle tree structure for efficient proof generation.
#[derive(Debug, Clone)]
pub struct MerkleTree<H: Hasher = DefaultContentHasher> {
    /// Root hash
    pub root: H::Digest,
    /// Leaf hashes in order
    leaves: Vec<H::Digest>,
    /// Internal nodes (for proof generation)
    /// Stored level by level, bottom up
    levels: Vec<Vec<H::Digest>>,
    _hasher: PhantomData<H>,
}

impl<H: Hasher> MerkleTree<H> {
    /// Build a Merkle tree from a list of leaf hashes.
    pub fn from_leaves(leaves: Vec<H::Digest>) -> Self {
        if leaves.is_empty() {
            return Self {
                root: empty_root::<H>(),
                leaves: Vec::new(),
                levels: Vec::new(),
                _hasher: PhantomData,
            };
        }

        let mut levels = vec![leaves.clone()];
        let mut current_level = leaves.clone();

        while current_level.len() > 1 {
            if current_level.len() % 2 == 1 {
                current_level.push(current_level.last().expect("non-empty level").clone());
            }

            let next_level: Vec<H::Digest> = current_level
                .chunks(2)
                .map(|pair| merkle_node_hash::<H>(&pair[0], &pair[1]))
                .collect();

            levels.push(next_level.clone());
            current_level = next_level;
        }

        let root = current_level[0].clone();

        Self {
            root,
            leaves,
            levels,
            _hasher: PhantomData,
        }
    }

    /// Build a Merkle tree from a heap.
    pub fn from_heap(heap: &Heap<H>) -> Self {
        let leaves: Vec<H::Digest> = heap
            .active_resources()
            .map(|(rid, resource)| resource_leaf_hash::<H>(rid, resource))
            .collect();
        Self::from_leaves(leaves)
    }

    /// Get the number of leaves.
    pub fn size(&self) -> usize {
        self.leaves.len()
    }

    /// Generate an inclusion proof for a leaf at the given index.
    pub fn prove(&self, index: usize) -> Option<MerkleProof<H>> {
        if index >= self.leaves.len() {
            return None;
        }

        let leaf_hash = self.leaves[index].clone();
        let mut path = Vec::new();
        let mut current_index = index;

        for level in &self.levels[..self.levels.len().saturating_sub(1)] {
            let sibling_index = if current_index % 2 == 0 {
                current_index + 1
            } else {
                current_index - 1
            };

            let sibling_hash = if sibling_index < level.len() {
                level[sibling_index].clone()
            } else {
                level[current_index].clone()
            };

            let direction = if current_index % 2 == 0 {
                Direction::Right
            } else {
                Direction::Left
            };

            path.push(ProofStep {
                direction,
                sibling_hash,
            });

            current_index /= 2;
        }

        Some(MerkleProof {
            leaf_hash,
            path,
            root: self.root.clone(),
        })
    }
}

/// Commitment to heap state (roots + counter).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeapCommitment<H: Hasher = DefaultContentHasher> {
    /// Merkle root of resources
    pub resource_root: H::Digest,
    /// Merkle root of nullifiers
    pub nullifier_root: H::Digest,
    /// Allocation counter
    pub counter: u64,
}

impl<H: Hasher> HeapCommitment<H> {
    /// Compute commitment from a heap.
    pub fn from_heap(heap: &Heap<H>) -> Self {
        let resource_leaves: Vec<H::Digest> = heap
            .active_resources()
            .map(|(rid, resource)| resource_leaf_hash::<H>(rid, resource))
            .collect();
        let resource_tree = MerkleTree::<H>::from_leaves(resource_leaves);

        let nullifier_leaves: Vec<H::Digest> =
            heap.consumed_ids().map(nullifier_leaf_hash::<H>).collect();
        let nullifier_tree = MerkleTree::<H>::from_leaves(nullifier_leaves);

        Self {
            resource_root: resource_tree.root,
            nullifier_root: nullifier_tree.root,
            counter: heap.alloc_counter(),
        }
    }

    /// Hash this commitment to a single value.
    ///
    /// The hasher consumes a tagged preimage that contains the resource root,
    /// the nullifier root, and the allocation counter.
    pub fn hash(&self) -> H::Digest {
        let preimage = encode_heap_commitment_preimage(
            self.resource_root.as_ref(),
            self.nullifier_root.as_ref(),
            self.counter,
        );
        H::digest(&preimage)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::DefaultContentHasher;

    fn to_hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{:02x}", byte)).collect()
    }

    fn from_hex(hex: &str) -> Vec<u8> {
        assert_eq!(hex.len() % 2, 0, "hex input must have even length");
        hex.as_bytes()
            .chunks(2)
            .map(|pair| {
                let hi = (pair[0] as char).to_digit(16).expect("valid hex") as u8;
                let lo = (pair[1] as char).to_digit(16).expect("valid hex") as u8;
                (hi << 4) | lo
            })
            .collect()
    }

    #[test]
    fn test_empty_tree() {
        let tree = MerkleTree::<DefaultContentHasher>::from_leaves(vec![]);
        assert_eq!(tree.root, empty_root::<DefaultContentHasher>());
        assert_eq!(tree.size(), 0);
    }

    #[test]
    fn test_single_leaf() {
        let leaf = DefaultContentHasher::digest(b"hello");
        let tree = MerkleTree::<DefaultContentHasher>::from_leaves(vec![leaf]);
        assert_eq!(tree.root, leaf);
        assert_eq!(tree.size(), 1);
    }

    #[test]
    fn test_two_leaves() {
        let leaf1 = DefaultContentHasher::digest(b"hello");
        let leaf2 = DefaultContentHasher::digest(b"world");
        let tree = MerkleTree::<DefaultContentHasher>::from_leaves(vec![leaf1, leaf2]);

        let expected_root = merkle_node_hash::<DefaultContentHasher>(&leaf1, &leaf2);
        assert_eq!(tree.root, expected_root);
        assert_eq!(tree.size(), 2);
    }

    #[test]
    fn test_four_leaves() {
        let leaves: Vec<_> = (0_u8..4)
            .map(|i| DefaultContentHasher::digest(&[i]))
            .collect();
        let tree = MerkleTree::<DefaultContentHasher>::from_leaves(leaves.clone());

        let h01 = merkle_node_hash::<DefaultContentHasher>(&leaves[0], &leaves[1]);
        let h23 = merkle_node_hash::<DefaultContentHasher>(&leaves[2], &leaves[3]);
        let expected_root = merkle_node_hash::<DefaultContentHasher>(&h01, &h23);

        assert_eq!(tree.root, expected_root);
        assert_eq!(tree.size(), 4);
    }

    #[test]
    fn test_proof_generation_and_verification() {
        let leaves: Vec<_> = (0_u8..4)
            .map(|i| DefaultContentHasher::digest(&[i]))
            .collect();
        let tree = MerkleTree::<DefaultContentHasher>::from_leaves(leaves);

        for i in 0..4 {
            let proof = tree.prove(i).expect("should generate proof");
            assert!(proof.verify(), "proof for leaf {} should verify", i);
        }
    }

    #[test]
    fn test_proof_for_out_of_bounds() {
        let leaves: Vec<_> = (0_u8..4)
            .map(|i| DefaultContentHasher::digest(&[i]))
            .collect();
        let tree = MerkleTree::<DefaultContentHasher>::from_leaves(leaves);

        assert!(tree.prove(4).is_none());
        assert!(tree.prove(100).is_none());
    }

    #[test]
    fn test_odd_number_of_leaves() {
        let leaves: Vec<_> = (0_u8..3)
            .map(|i| DefaultContentHasher::digest(&[i]))
            .collect();
        let tree = MerkleTree::<DefaultContentHasher>::from_leaves(leaves);

        for i in 0..3 {
            let proof = tree.prove(i).expect("should generate proof");
            assert!(proof.verify(), "proof for leaf {} should verify", i);
        }
    }

    #[test]
    fn test_heap_merkle_root() {
        let heap = Heap::<DefaultContentHasher>::new();
        let (_, heap) = heap.alloc_channel("Alice", "Bob");
        let (_, heap) = heap.alloc_message("Alice", "Bob", "Hello", vec![], 0);

        let root = MerkleTree::<DefaultContentHasher>::from_heap(&heap).root;
        assert_ne!(root, empty_root::<DefaultContentHasher>());
    }

    #[test]
    fn test_heap_commitment() {
        let heap = Heap::<DefaultContentHasher>::new();
        let (rid, heap) = heap.alloc_channel("Alice", "Bob");
        let heap = heap.consume(&rid).unwrap();

        let commitment = HeapCommitment::<DefaultContentHasher>::from_heap(&heap);

        assert_eq!(commitment.counter, 1);
    }

    #[test]
    fn test_leaf_and_node_fixed_vectors() {
        let resource = Resource::message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
        let resource_id = ResourceId::<DefaultContentHasher>::from_resource(&resource, 1);
        let resource_leaf = resource_leaf_hash::<DefaultContentHasher>(&resource_id, &resource);
        let nullifier_leaf = nullifier_leaf_hash::<DefaultContentHasher>(&resource_id);

        assert_eq!(
            to_hex(resource_leaf.as_ref()),
            "7526f89408115ad41ff135f26fd3c0be0ca91c93589c2f17cea2d8115bda9cf3"
        );
        assert_eq!(
            to_hex(nullifier_leaf.as_ref()),
            "c8ff09f3959b1a2d654b86e29d8f12df277db70f05256f0e433bf26a6c98acb1"
        );

        let sibling: [u8; 32] = from_hex(
            "981652f6785b2e7147a3ba489d050f3924700e808b9a7b229470754507c5a13c",
        )
        .try_into()
        .expect("32-byte test vector");
        let root = merkle_node_hash::<DefaultContentHasher>(&resource_leaf, &sibling);
        assert_eq!(
            to_hex(root.as_ref()),
            "1555554394a0a595200d7717fa5c4710ce608dab3ffd793ff3644eecb99df1fa"
        );
    }

    #[test]
    fn test_heap_commitment_fixed_vector() {
        let heap = Heap::<DefaultContentHasher>::new();
        let (rid0, heap) = heap.alloc_channel("Alice", "Bob");
        let (_rid1, heap) = heap.alloc_message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
        let (_rid2, heap) = heap.alloc_session("Alice", 12345);
        let heap = heap.consume(&rid0).unwrap();

        let commitment = HeapCommitment::<DefaultContentHasher>::from_heap(&heap);

        assert_eq!(
            to_hex(commitment.resource_root.as_ref()),
            "1555554394a0a595200d7717fa5c4710ce608dab3ffd793ff3644eecb99df1fa"
        );
        assert_eq!(
            to_hex(commitment.nullifier_root.as_ref()),
            "c045d1ac8bad212b29fffbe54d774d1401242771c75275fc30b6136b007f52d6"
        );
        assert_eq!(
            to_hex(commitment.hash().as_ref()),
            "57d07742f7a22b083e88dcae71804c9f03a727df11fe9d1d4c0aa553a34dac0d"
        );
    }

    #[test]
    fn test_merkle_proof_fixed_vector() {
        let heap = Heap::<DefaultContentHasher>::new();
        let (rid0, heap) = heap.alloc_channel("Alice", "Bob");
        let (_rid1, heap) = heap.alloc_message("Alice", "Bob", "Hello", vec![1, 2, 3], 7);
        let (_rid2, heap) = heap.alloc_session("Alice", 12345);
        let heap = heap.consume(&rid0).unwrap();

        let tree = MerkleTree::<DefaultContentHasher>::from_heap(&heap);
        let proof = tree.prove(0).expect("proof should exist");

        assert_eq!(
            to_hex(proof.leaf_hash.as_ref()),
            "7526f89408115ad41ff135f26fd3c0be0ca91c93589c2f17cea2d8115bda9cf3"
        );
        assert_eq!(proof.path.len(), 1);
        assert_eq!(proof.path[0].direction, Direction::Right);
        assert_eq!(
            to_hex(proof.path[0].sibling_hash.as_ref()),
            "981652f6785b2e7147a3ba489d050f3924700e808b9a7b229470754507c5a13c"
        );
        assert_eq!(
            to_hex(proof.root.as_ref()),
            "1555554394a0a595200d7717fa5c4710ce608dab3ffd793ff3644eecb99df1fa"
        );
        assert!(proof.verify());
    }

    #[test]
    fn test_commitment_determinism() {
        let heap1 = Heap::<DefaultContentHasher>::new();
        let (_, heap1) = heap1.alloc_channel("Alice", "Bob");

        let heap2 = Heap::<DefaultContentHasher>::new();
        let (_, heap2) = heap2.alloc_channel("Alice", "Bob");

        let c1 = HeapCommitment::<DefaultContentHasher>::from_heap(&heap1);
        let c2 = HeapCommitment::<DefaultContentHasher>::from_heap(&heap2);

        assert_eq!(c1, c2);
        assert_eq!(c1.hash(), c2.hash());
    }
}
