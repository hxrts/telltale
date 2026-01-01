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
//! This module corresponds to `lean/Rumpsteak/Protocol/Merkle.lean`:
//! - `MerkleTree` ↔ Lean's `MerkleTree`
//! - `MerkleProof` ↔ Lean's `MerkleProof`
//! - `merkle_root` ↔ Lean's `merkleRoot`

use super::heap_impl::Heap;
use super::resource::{Resource, ResourceId};
use sha2::{Digest, Sha256};

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
pub struct ProofStep {
    /// Direction: is this node a left or right sibling?
    pub direction: Direction,
    /// The sibling hash at this level
    pub sibling_hash: [u8; 32],
}

/// A Merkle inclusion proof.
///
/// The proof consists of sibling hashes from leaf to root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleProof {
    /// The leaf hash being proven
    pub leaf_hash: [u8; 32],
    /// Proof path from leaf to root
    pub path: Vec<ProofStep>,
    /// The expected root hash
    pub root: [u8; 32],
}

impl MerkleProof {
    /// Verify this proof.
    pub fn verify(&self) -> bool {
        let computed_root =
            self.path
                .iter()
                .fold(self.leaf_hash, |current, step| match step.direction {
                    Direction::Left => hash_pair(&step.sibling_hash, &current),
                    Direction::Right => hash_pair(&current, &step.sibling_hash),
                });
        computed_root == self.root
    }
}

/// Hash two child hashes to get parent hash.
fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(left);
    hasher.update(right);
    hasher.finalize().into()
}

/// Compute hash of a (ResourceId, Resource) leaf.
fn hash_leaf(rid: &ResourceId, resource: &Resource) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(rid.hash);
    hasher.update(resource.to_bytes());
    hasher.finalize().into()
}

/// Empty tree root (hash of empty).
fn empty_root() -> [u8; 32] {
    Sha256::digest([]).into()
}

/// Merkle tree structure for efficient proof generation.
#[derive(Debug, Clone)]
pub struct MerkleTree {
    /// Root hash
    pub root: [u8; 32],
    /// Leaf hashes in order
    leaves: Vec<[u8; 32]>,
    /// Internal nodes (for proof generation)
    /// Stored level by level, bottom up
    levels: Vec<Vec<[u8; 32]>>,
}

impl MerkleTree {
    /// Build a Merkle tree from a list of leaf hashes.
    pub fn from_leaves(leaves: Vec<[u8; 32]>) -> Self {
        if leaves.is_empty() {
            return Self {
                root: empty_root(),
                leaves: Vec::new(),
                levels: Vec::new(),
            };
        }

        let mut levels = vec![leaves.clone()];
        let mut current_level = leaves.clone();

        while current_level.len() > 1 {
            // Pad to even if needed
            if current_level.len() % 2 == 1 {
                current_level.push(*current_level.last().unwrap());
            }

            // Compute next level
            let next_level: Vec<[u8; 32]> = current_level
                .chunks(2)
                .map(|pair| hash_pair(&pair[0], &pair[1]))
                .collect();

            levels.push(next_level.clone());
            current_level = next_level;
        }

        let root = current_level[0];

        Self {
            root,
            leaves,
            levels,
        }
    }

    /// Build a Merkle tree from a heap.
    pub fn from_heap(heap: &Heap) -> Self {
        let leaves: Vec<[u8; 32]> = heap
            .active_resources()
            .map(|(rid, resource)| hash_leaf(rid, resource))
            .collect();
        Self::from_leaves(leaves)
    }

    /// Get the number of leaves.
    pub fn size(&self) -> usize {
        self.leaves.len()
    }

    /// Generate an inclusion proof for a leaf at the given index.
    pub fn prove(&self, index: usize) -> Option<MerkleProof> {
        if index >= self.leaves.len() {
            return None;
        }

        let leaf_hash = self.leaves[index];
        let mut path = Vec::new();
        let mut current_index = index;

        for level in &self.levels[..self.levels.len().saturating_sub(1)] {
            let sibling_index = if current_index % 2 == 0 {
                current_index + 1
            } else {
                current_index - 1
            };

            // Handle odd-length levels (last element duplicated)
            let sibling_hash = if sibling_index < level.len() {
                level[sibling_index]
            } else {
                level[current_index]
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
            root: self.root,
        })
    }
}

/// Commitment to heap state (roots + counter).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeapCommitment {
    /// Merkle root of resources
    pub resource_root: [u8; 32],
    /// Merkle root of nullifiers
    pub nullifier_root: [u8; 32],
    /// Allocation counter
    pub counter: u64,
}

impl HeapCommitment {
    /// Compute commitment from a heap.
    pub fn from_heap(heap: &Heap) -> Self {
        let resource_leaves: Vec<[u8; 32]> = heap
            .active_resources()
            .map(|(rid, resource)| hash_leaf(rid, resource))
            .collect();
        let resource_tree = MerkleTree::from_leaves(resource_leaves);

        let nullifier_leaves: Vec<[u8; 32]> = heap.consumed_ids().map(|rid| rid.hash).collect();
        let nullifier_tree = MerkleTree::from_leaves(nullifier_leaves);

        Self {
            resource_root: resource_tree.root,
            nullifier_root: nullifier_tree.root,
            counter: heap.alloc_counter(),
        }
    }

    /// Hash this commitment to a single value.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(self.resource_root);
        hasher.update(self.nullifier_root);
        hasher.update(self.counter.to_le_bytes());
        hasher.finalize().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let tree = MerkleTree::from_leaves(vec![]);
        assert_eq!(tree.root, empty_root());
        assert_eq!(tree.size(), 0);
    }

    #[test]
    fn test_single_leaf() {
        let leaf = Sha256::digest(b"hello").into();
        let tree = MerkleTree::from_leaves(vec![leaf]);
        assert_eq!(tree.root, leaf);
        assert_eq!(tree.size(), 1);
    }

    #[test]
    fn test_two_leaves() {
        let leaf1: [u8; 32] = Sha256::digest(b"hello").into();
        let leaf2: [u8; 32] = Sha256::digest(b"world").into();
        let tree = MerkleTree::from_leaves(vec![leaf1, leaf2]);

        let expected_root = hash_pair(&leaf1, &leaf2);
        assert_eq!(tree.root, expected_root);
        assert_eq!(tree.size(), 2);
    }

    #[test]
    fn test_four_leaves() {
        let leaves: Vec<[u8; 32]> = (0..4).map(|i| Sha256::digest([i as u8]).into()).collect();
        let tree = MerkleTree::from_leaves(leaves.clone());

        let h01 = hash_pair(&leaves[0], &leaves[1]);
        let h23 = hash_pair(&leaves[2], &leaves[3]);
        let expected_root = hash_pair(&h01, &h23);

        assert_eq!(tree.root, expected_root);
        assert_eq!(tree.size(), 4);
    }

    #[test]
    fn test_proof_generation_and_verification() {
        let leaves: Vec<[u8; 32]> = (0..4).map(|i| Sha256::digest([i as u8]).into()).collect();
        let tree = MerkleTree::from_leaves(leaves);

        for i in 0..4 {
            let proof = tree.prove(i).expect("should generate proof");
            assert!(proof.verify(), "proof for leaf {} should verify", i);
        }
    }

    #[test]
    fn test_proof_for_out_of_bounds() {
        let leaves: Vec<[u8; 32]> = (0..4).map(|i| Sha256::digest([i as u8]).into()).collect();
        let tree = MerkleTree::from_leaves(leaves);

        assert!(tree.prove(4).is_none());
        assert!(tree.prove(100).is_none());
    }

    #[test]
    fn test_odd_number_of_leaves() {
        let leaves: Vec<[u8; 32]> = (0..3).map(|i| Sha256::digest([i as u8]).into()).collect();
        let tree = MerkleTree::from_leaves(leaves);

        // Should still work with 3 leaves
        for i in 0..3 {
            let proof = tree.prove(i).expect("should generate proof");
            assert!(proof.verify(), "proof for leaf {} should verify", i);
        }
    }

    #[test]
    fn test_heap_merkle_root() {
        let heap = Heap::new();
        let (_, heap) = heap.alloc_channel("Alice", "Bob");
        let (_, heap) = heap.alloc_message("Alice", "Bob", "Hello", vec![], 0);

        let root = MerkleTree::from_heap(&heap).root;
        assert_ne!(root, empty_root());
    }

    #[test]
    fn test_heap_commitment() {
        let heap = Heap::new();
        let (rid, heap) = heap.alloc_channel("Alice", "Bob");
        let heap = heap.consume(&rid).unwrap();

        let commitment = HeapCommitment::from_heap(&heap);

        // Resource root should be empty (resource consumed)
        // Nullifier root should not be empty (has consumed ID)
        assert_eq!(commitment.counter, 1);
    }

    #[test]
    fn test_commitment_determinism() {
        let heap1 = Heap::new();
        let (_, heap1) = heap1.alloc_channel("Alice", "Bob");

        let heap2 = Heap::new();
        let (_, heap2) = heap2.alloc_channel("Alice", "Bob");

        let c1 = HeapCommitment::from_heap(&heap1);
        let c2 = HeapCommitment::from_heap(&heap2);

        assert_eq!(c1, c2);
        assert_eq!(c1.hash(), c2.hash());
    }
}
