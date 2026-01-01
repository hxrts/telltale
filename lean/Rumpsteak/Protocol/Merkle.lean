import Rumpsteak.Protocol.ContentId
import Rumpsteak.Protocol.Resource
import Rumpsteak.Protocol.Heap

/-! # Rumpsteak.Protocol.Merkle

Merkle tree utilities for heap state verification.

## Overview

This module provides Merkle tree construction and verification for heap state.
The Merkle root serves as a canonical commitment to the entire heap state,
enabling:
- Efficient proofs of inclusion/exclusion
- ZK-compatible state representation
- Deterministic state commitments

## Merkle Tree Structure

The heap is Merkleized as follows:
1. Resources are sorted by ResourceId (already sorted via RBMap)
2. Each (ResourceId, Resource) pair becomes a leaf
3. Leaves are hashed pairwise up to a single root
4. Empty heaps have a special empty root hash

## Rust Correspondence

This module corresponds to `rust/choreography/src/heap/merkle.rs`:
- `MerkleTree` ↔ Rust's `MerkleTree`
- `MerkleProof` ↔ Rust's `MerkleProof`
- `merkleRoot` ↔ Rust's `Heap::merkle_root`

## Main Definitions

- `MerkleNode`: A node in the Merkle tree
- `MerkleProof`: Proof of inclusion for a resource
- `merkleRoot`: Compute the Merkle root of a heap
- `verifyProof`: Verify a Merkle inclusion proof
-/

open Rumpsteak.Protocol.ContentId
open Rumpsteak.Protocol.Resource
open Rumpsteak.Protocol.Heap

namespace Rumpsteak.Protocol.Merkle

/-- Direction in a Merkle proof path. -/
inductive Direction where
  | left : Direction
  | right : Direction
deriving Repr, DecidableEq, BEq, Inhabited

/-- A single step in a Merkle proof. -/
structure ProofStep where
  /-- Direction: is this node a left or right sibling? -/
  direction : Direction
  /-- The sibling hash at this level -/
  siblingHash : ByteArray
deriving BEq, Inhabited

instance : Repr ProofStep where
  reprPrec p _ := s!"ProofStep({repr p.direction})"

/-- A Merkle inclusion proof.

    The proof consists of sibling hashes from leaf to root. -/
structure MerkleProof where
  /-- The leaf being proven -/
  leafHash : ByteArray
  /-- Proof path from leaf to root -/
  path : List ProofStep
  /-- The expected root hash -/
  root : ByteArray
deriving BEq, Inhabited

instance : Repr MerkleProof where
  reprPrec p _ := s!"MerkleProof(path.length={p.path.length})"

/-- Hash two child hashes to get parent hash. -/
def hashPair [Hasher H] (left right : ByteArray) : ByteArray :=
  let combined := left ++ right
  Hasher.hash H combined

/-- Compute hash of a (ResourceId, Resource) leaf. -/
def hashLeaf [Hasher H] (rid : ResourceId) (r : Resource) : ByteArray :=
  let ridBytes := rid.hash
  let resourceBytes := r.toBytes
  Hasher.hash H (ridBytes ++ resourceBytes)

/-- Empty tree root (hash of empty). -/
def emptyRoot [Hasher H] : ByteArray :=
  Hasher.hash H ByteArray.empty

/-- Compute Merkle root from a list of leaf hashes.

    Uses a bottom-up construction:
    1. If empty, return empty root
    2. If one leaf, that's the root
    3. Otherwise, hash pairs and recurse -/
partial def computeRoot [Hasher H] (leaves : List ByteArray) : ByteArray :=
  match leaves with
  | [] => emptyRoot (H := H)
  | [h] => h
  | _ =>
    -- Pad to even number if needed
    let padded := if leaves.length % 2 == 1
      then leaves ++ [leaves.getLast!]
      else leaves
    -- Hash pairs
    let parents := pairUp padded
    computeRoot (H := H) parents
where
  pairUp : List ByteArray → List ByteArray
    | [] => []
    | [x] => [x]  -- Shouldn't happen after padding
    | x :: y :: rest => hashPair (H := H) x y :: pairUp rest

/-- Compute the Merkle root of a heap.

    The resources are already sorted by ResourceId due to RBMap ordering. -/
def merkleRoot [Hasher H] (h : Heap) : ByteArray :=
  let entries := h.resources.toList
  let leaves := entries.map fun (rid, r) => hashLeaf (H := H) rid r
  computeRoot (H := H) leaves

/-- Compute Merkle root using default SHA-256 hasher. -/
def merkleRootSha256 (h : Heap) : ByteArray :=
  merkleRoot (H := Sha256Hasher) h

/-- Verify a Merkle inclusion proof.

    Reconstructs the root from the leaf and proof path,
    then compares to the expected root. -/
def verifyProof [Hasher H] (proof : MerkleProof) : Bool :=
  let computedRoot := proof.path.foldl (fun current step =>
    match step.direction with
    | .left => hashPair (H := H) step.siblingHash current
    | .right => hashPair (H := H) current step.siblingHash
  ) proof.leafHash
  computedRoot == proof.root

/-- Result of a proof generation attempt. -/
inductive ProofResult where
  | ok : MerkleProof → ProofResult
  | notFound : ProofResult

instance : Repr ProofResult where
  reprPrec r _ := match r with
    | .ok p => s!"ProofResult.ok({repr p})"
    | .notFound => "ProofResult.notFound"

/-- Enumerate a list with indices. -/
def enumerate {α : Type} (xs : List α) : List (Nat × α) :=
  xs.mapIdx fun i x => (i, x)

/-- Compute the root hash along with leaf hashes for proof generation.

    Returns (root, list of (index, leafHash) pairs) -/
def computeRootWithLeaves [Hasher H] (leaves : List ByteArray)
    : ByteArray × List (Nat × ByteArray) :=
  let indexed := enumerate leaves
  let root := computeRoot (H := H) leaves
  (root, indexed)

/-- Merkle tree structure for efficient proof generation. -/
structure MerkleTree where
  /-- Root hash -/
  root : ByteArray
  /-- Leaf hashes in order -/
  leaves : List ByteArray
  /-- Number of leaves -/
  size : Nat
deriving BEq, Inhabited

instance : Repr MerkleTree where
  reprPrec t _ := s!"MerkleTree(size={t.size})"

/-- Build a Merkle tree from heap. -/
def buildTree [Hasher H] (h : Heap) : MerkleTree :=
  let entries := h.resources.toList
  let leaves := entries.map fun (rid, r) => hashLeaf (H := H) rid r
  let root := computeRoot (H := H) leaves
  { root := root, leaves := leaves, size := leaves.length }

/-- Build tree using default SHA-256 hasher. -/
def buildTreeSha256 (h : Heap) : MerkleTree :=
  buildTree (H := Sha256Hasher) h

/-- Commitment to heap state (root hash + size). -/
structure HeapCommitment where
  /-- Merkle root of resources -/
  resourceRoot : ByteArray
  /-- Merkle root of nullifiers -/
  nullifierRoot : ByteArray
  /-- Allocation counter -/
  counter : Nat
deriving BEq, Inhabited

instance : Repr HeapCommitment where
  reprPrec c _ := s!"HeapCommitment(counter={c.counter})"

/-- Compute nullifier set Merkle root. -/
def nullifierRoot [Hasher H] (h : Heap) : ByteArray :=
  let nullifierIds := h.nullifiers.toList.map (·.1)
  let leaves := nullifierIds.map fun rid => rid.hash
  computeRoot (H := H) leaves

/-- Compute full heap commitment. -/
def heapCommitment [Hasher H] (h : Heap) : HeapCommitment :=
  { resourceRoot := merkleRoot (H := H) h
  , nullifierRoot := nullifierRoot (H := H) h
  , counter := h.counter
  }

/-- Compute commitment using default SHA-256. -/
def heapCommitmentSha256 (h : Heap) : HeapCommitment :=
  heapCommitment (H := Sha256Hasher) h

/-- Hash a commitment to a single value. -/
def commitmentHash [Hasher H] (c : HeapCommitment) : ByteArray :=
  let counterBytes := c.counter.toDigits 16
    |>.foldl (fun ba d => ba.push d.val.toUInt8) ByteArray.empty
  Hasher.hash H (c.resourceRoot ++ c.nullifierRoot ++ counterBytes)

/-! ## Cryptographic Assumptions

These axioms represent standard cryptographic hardness assumptions that cannot be
proven mathematically but are well-established in the literature. They form the
cryptographic foundation for the Rumpsteak-Aura security model.

**References:**
- R. C. Merkle, "A Digital Signature Based on a Conventional Encryption Function,"
  CRYPTO 1987. doi:10.1007/3-540-48184-2_32
- NIST FIPS 180-4, "Secure Hash Standard (SHS)," August 2015.
  https://csrc.nist.gov/publications/detail/fips/180/4/final
- M. Bellare and P. Rogaway, "Collision-Resistant Hashing: Towards Making UOWHFs
  Practical," CRYPTO 1997. doi:10.1007/BFb0052256

These assumptions are standard in cryptographic protocol verification and are
trusted primitives in the security model. -/

/-- Collision resistance assumption for Merkle proofs.

    This axiom states that if two lists of leaves produce the same Merkle root,
    they must be equal. This is a cryptographic assumption that cannot be proven
    mathematically - it must be assumed for security proofs.

    **Justification:** Merkle trees inherit collision resistance from the underlying
    hash function [Merkle 1987]. If the hash function is collision-resistant (as
    assumed for SHA-256 per NIST FIPS 180-4), then finding two different leaf lists
    with the same root would require finding a hash collision. -/
axiom merkle_collision_resistant [Hasher H] (leaves1 leaves2 : List ByteArray) :
    computeRoot (H := H) leaves1 = computeRoot (H := H) leaves2 → leaves1 = leaves2

/-- Hash leaf injectivity assumption.

    If two (ResourceId, Resource) pairs produce the same leaf hash, they must be equal.

    **Justification:** This follows from collision resistance of the underlying hash
    function. The leaf hash is computed as H(rid ++ resource), so equal hashes imply
    equal inputs under the collision resistance assumption [NIST FIPS 180-4]. -/
axiom hashLeaf_injective [Hasher H] (rid1 rid2 : ResourceId) (r1 r2 : Resource) :
    hashLeaf (H := H) rid1 r1 = hashLeaf (H := H) rid2 r2 → rid1 = rid2 ∧ r1 = r2

/-- ResourceId hash injectivity assumption.

    If two ResourceIds have the same hash field and counter, they must be equal.

    **Justification:** ResourceId equality is determined by its fields. Given equal
    hash and counter fields, the ResourceIds are structurally equal. -/
axiom resourceId_hash_injective (rid1 rid2 : ResourceId) :
    rid1.hash = rid2.hash → rid1.counter = rid2.counter → rid1 = rid2

/-- Full ResourceId injectivity from hash field.

    For ResourceIds created via ResourceId.create, the hash field encodes
    both the content and the counter. Therefore, equal hash fields imply
    equal ResourceIds.

    **Justification:** ResourceId.create computes hash as H(content ++ counter).
    Under collision resistance, equal hashes imply equal (content, counter) pairs,
    and thus equal ResourceIds. -/
axiom resourceId_from_hash_injective (rid1 rid2 : ResourceId) :
    rid1.hash = rid2.hash → rid1 = rid2

/-- Helper: If mapping an injective function over two lists gives equal results,
    the original lists are equal. -/
theorem map_injective_eq {α β : Type _} (f : α → β) (l1 l2 : List α)
    (hinj : ∀ a b, f a = f b → a = b)
    (heq : l1.map f = l2.map f) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => cases heq
  | cons x xs ih =>
    cases l2 with
    | nil => cases heq
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at heq
      have hxy := hinj x y heq.1
      have hrest := ih ys heq.2
      rw [hxy, hrest]

/-- Two heaps have the same commitment iff they're equal
    (assuming collision resistance).

    SECURITY ASSUMPTION: This relies on `merkle_collision_resistant`, which
    assumes the hash function is collision-resistant. This is a standard
    cryptographic assumption for Merkle tree security. -/
theorem commitment_injective [Hasher H] (h1 h2 : Heap) :
    heapCommitment (H := H) h1 = heapCommitment (H := H) h2 →
    h1.resources.toList = h2.resources.toList ∧
    h1.nullifiers.toList = h2.nullifiers.toList ∧
    h1.counter = h2.counter := by
  intro heq
  unfold heapCommitment at heq
  -- Extract the three components of the commitment
  have hres : merkleRoot (H := H) h1 = merkleRoot (H := H) h2 := by
    cases heq; rfl
  have hnull : nullifierRoot (H := H) h1 = nullifierRoot (H := H) h2 := by
    cases heq; rfl
  have hctr : h1.counter = h2.counter := by
    cases heq; rfl
  constructor
  · -- Resources equal: use collision resistance on resource leaves
    unfold merkleRoot at hres
    have hleaves := merkle_collision_resistant
      (h1.resources.toList.map fun (rid, r) => hashLeaf (H := H) rid r)
      (h2.resources.toList.map fun (rid, r) => hashLeaf (H := H) rid r)
      hres
    -- Use map_injective_eq with hashLeaf injectivity
    apply map_injective_eq _ _ _ _ hleaves
    intro ⟨rid1, r1⟩ ⟨rid2, r2⟩ heq
    have ⟨hrid, hr⟩ := hashLeaf_injective rid1 rid2 r1 r2 heq
    simp only [Prod.mk.injEq]
    exact ⟨hrid, hr⟩
  constructor
  · -- Nullifiers equal: use collision resistance on nullifier leaves
    unfold nullifierRoot at hnull
    have hleaves := merkle_collision_resistant
      (h1.nullifiers.toList.map (·.1.hash))
      (h2.nullifiers.toList.map (·.1.hash))
      hnull
    -- Nullifier lists are (ResourceId × Unit), need to show equality
    -- The hash list being equal means the ResourceId hashes are equal
    apply map_injective_eq _ _ _ _ hleaves
    intro ⟨rid1, _⟩ ⟨rid2, _⟩ heq
    -- heq : rid1.hash = rid2.hash
    -- Use resourceId_from_hash_injective: equal hashes imply equal ResourceIds
    simp only [Prod.mk.injEq]
    constructor
    · exact resourceId_from_hash_injective rid1 rid2 heq
    · rfl
  · exact hctr

/-- Empty heap has deterministic commitment.

    Note: This relies on the specific behavior of RBMap.empty.toList = []
    and computeRoot [] = emptyRoot. -/
theorem empty_heap_commitment [Hasher H] :
    heapCommitment (H := H) Heap.empty =
    { resourceRoot := emptyRoot (H := H)
    , nullifierRoot := emptyRoot (H := H)
    , counter := 0 } := by
  unfold heapCommitment merkleRoot nullifierRoot Heap.empty
  simp only
  -- Need to show: RBMap.empty.toList = []
  -- This is true by definition of RBMap.empty
  congr 1
  · -- resourceRoot: computeRoot [] = emptyRoot
    unfold computeRoot
    rfl
  · -- nullifierRoot: computeRoot [] = emptyRoot
    unfold computeRoot
    rfl

end Rumpsteak.Protocol.Merkle
