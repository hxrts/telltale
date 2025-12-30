/-! # Rumpsteak.Protocol.ContentId

Content addressing for session types.

## Overview

This module provides content-addressable identifiers for protocol artifacts.
Content IDs enable structural sharing, memoization, and deterministic verification.

The hash algorithm is abstracted via the `Hasher` typeclass, allowing users to
swap implementations for different use cases (performance, ZK compatibility, etc.).
SHA-256 is the default implementation.

## Rust Correspondence

This module corresponds to `rust/types/src/content_id.rs`:
- `Hasher` ↔ Rust's `Hasher` trait
- `ContentId` ↔ Rust's `ContentId<H>`
- `Sha256Hasher` ↔ Rust's `Sha256Hasher`
- `Contentable` ↔ Rust's `Contentable` trait (in contentable.rs)

## Main Definitions

- `Hasher`: Typeclass for hash algorithms
- `ContentId`: Content identifier parameterized by hasher
- `Sha256Hasher`: Default SHA-256 implementation
- `Contentable`: Trait for canonical serialization

## Future Work

- Integrate with DAG-CBOR serialization
- Add Blake3Hasher, PoseidonHasher for ZK compatibility
-/

namespace Rumpsteak.Protocol.ContentId

/-- Typeclass for hash algorithms used in content addressing.

    Implementors must provide a deterministic hash function that maps
    arbitrary byte sequences to fixed-size digests.

    Note: In Lean, we use a placeholder that returns a constant hash.
    The real implementation would use FFI to call a cryptographic library. -/
class Hasher (H : Type) where
  /-- Size of the hash output in bytes -/
  hashSize : Nat
  /-- Compute the hash of the input data.
      This function must be deterministic: the same input always produces
      the same output. -/
  hash : ByteArray → ByteArray
  /-- Name of the hash algorithm (for display/debugging) -/
  algorithmName : String

/-- SHA-256 hasher implementation (default).

    SHA-256 is chosen as the default because:
    - Widely supported and well-understood
    - 256-bit output provides strong collision resistance
    - Compatible with most ZK systems
    - Native hardware acceleration on modern CPUs

    Note: This is a placeholder. Real implementation would use FFI. -/
structure Sha256Hasher where
  mk ::
deriving Repr, DecidableEq, BEq, Inhabited

/-- Placeholder SHA-256 implementation.
    Returns a deterministic hash based on input length and first bytes.
    Real implementation would use cryptographic library via FFI. -/
private def sha256Placeholder (data : ByteArray) : ByteArray :=
  -- Placeholder: create a 32-byte hash from the data
  -- In production, this would call a real SHA-256 implementation
  let rec loop (i : Nat) (acc : ByteArray) : ByteArray :=
    if i >= 32 then acc
    else
      let byte := if i < data.size then data.get! i else (i + data.size).toUInt8
      loop (i + 1) (acc.push byte)
  loop 0 (ByteArray.emptyWithCapacity 32)

instance : Hasher Sha256Hasher where
  hashSize := 32
  hash := sha256Placeholder
  algorithmName := "sha256"

/-- Content identifier parameterized by hash algorithm.

    A `ContentId` is a cryptographic fingerprint of a value's canonical
    serialization. Two values with the same ContentId are considered
    structurally equivalent (modulo α-equivalence for types with binders). -/
structure ContentId (H : Type) [Hasher H] where
  /-- The raw hash bytes -/
  hash : ByteArray
deriving BEq

instance [Hasher H] : DecidableEq (ContentId H) := fun a b =>
  if h : a.hash = b.hash then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (by intro heq; cases heq; exact h rfl)

instance [Hasher H] : Hashable (ContentId H) where
  hash cid := cid.hash.foldl (fun acc b => acc ^^^ b.toUInt64) 0

instance [Hasher H] : Repr (ContentId H) where
  reprPrec cid _ := s!"ContentId({cid.hash.size} bytes)"

/-- Create a ContentId by hashing raw bytes. -/
def ContentId.fromBytes [Hasher H] (data : ByteArray) : ContentId H :=
  ⟨Hasher.hash H data⟩

/-- Get the raw hash bytes. -/
def ContentId.toBytes [Hasher H] (cid : ContentId H) : ByteArray :=
  cid.hash

/-- Convert to a hexadecimal string. -/
def ContentId.toHex [Hasher H] (cid : ContentId H) : String :=
  cid.hash.foldl (fun s b =>
    let hi := b.toNat / 16
    let lo := b.toNat % 16
    let hexChar (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    s.push (hexChar hi) |>.push (hexChar lo)
  ) ""

/-- Get the hash algorithm name. -/
def ContentId.algorithm [Hasher H] (_ : ContentId H) : String :=
  Hasher.algorithmName H

/-- Convenience type alias for SHA-256 content IDs. -/
abbrev ContentIdSha256 := ContentId Sha256Hasher

/-- Trait for types with canonical serialization.

    Types implementing `Contentable` can be serialized to bytes in a
    deterministic way, enabling content addressing and structural comparison.

    Invariants:
    - `fromBytes (toBytes x) ≈ x` (modulo α-equivalence for types with binders)
    - Two α-equivalent values produce identical bytes
    - Byte order is deterministic (independent of insertion order, etc.) -/
class Contentable (α : Type) where
  /-- Serialize to canonical byte representation -/
  toBytes : α → ByteArray
  /-- Deserialize from bytes -/
  fromBytes : ByteArray → Except String α

/-- Compute content ID using specified hasher. -/
def contentId [Hasher H] [Contentable α] (x : α) : ContentId H :=
  ContentId.fromBytes (Contentable.toBytes x)

/-- Compute content ID using default SHA-256 hasher. -/
def contentIdSha256 [Contentable α] (x : α) : ContentIdSha256 :=
  contentId x

/-- Instance for ByteArray (identity) -/
instance : Contentable ByteArray where
  toBytes := id
  fromBytes := Except.ok

/-- Instance for String -/
instance : Contentable String where
  toBytes s := s.toUTF8
  fromBytes ba := Except.ok (String.fromUTF8! ba)

/-- Instance for Nat (simple encoding) -/
instance : Contentable Nat where
  toBytes n := n.toDigits 16 |>.foldl (fun ba d => ba.push d.val.toUInt8) ByteArray.empty
  fromBytes _ := Except.ok 0  -- Simplified; real impl would decode

end Rumpsteak.Protocol.ContentId
