import Rumpsteak.Protocol.ContentId
import Rumpsteak.Protocol.LocalTypeR
import Batteries.Data.RBMap

/-! # Rumpsteak.Protocol.Resource

Resource types for explicit heap-based state management.

## Overview

This module defines content-addressed resources for the protocol heap.
Resources are immutable values identified by their content hash, enabling:
- Replay protection (can't process same message twice)
- Byzantine fault detection (prove protocol violations)
- ZK compatibility (state is a Merkle tree)
- Deterministic execution (heap operations are pure)

## Rust Correspondence

This module corresponds to `rust/choreography/src/heap/resource.rs`:
- `ResourceId` ↔ Rust's `ResourceId`
- `Resource` ↔ Rust's `Resource`
- `HeapError` ↔ Rust's `HeapError`

## Main Definitions

- `ResourceId`: Content-addressed identifier for heap resources
- `Resource`: Sum type for different resource kinds
- `ChannelState`: State of a communication channel
- `Message`: A message in transit
- `HeapError`: Errors that can occur during heap operations
-/

open Rumpsteak.Protocol.ContentId
open Rumpsteak.Protocol.LocalTypeR

namespace Rumpsteak.Protocol.Resource

/-- A message label with payload bytes. -/
structure MessagePayload where
  /-- The message label -/
  label : String
  /-- The serialized payload size (actual bytes stored separately) -/
  payloadSize : Nat
deriving Repr, BEq, Inhabited

/-- Full message payload with bytes (not deriving Repr due to ByteArray). -/
structure MessagePayloadFull where
  /-- The message label -/
  label : String
  /-- The serialized payload -/
  payload : ByteArray
deriving BEq, Inhabited

/-- State of a communication channel between two roles. -/
structure ChannelState where
  /-- The sender role -/
  sender : String
  /-- The receiver role -/
  receiver : String
  /-- Number of pending messages (actual queue stored separately) -/
  queueSize : Nat
deriving Repr, BEq, Inhabited

/-- A message resource representing a message in transit. -/
structure Message where
  /-- Source role -/
  source : String
  /-- Destination role -/
  dest : String
  /-- Message label -/
  label : String
  /-- Sequence number for ordering -/
  seqNo : Nat
deriving Repr, BEq, Inhabited

/-- Unique identifier for heap-allocated resources.

    ResourceId is derived from the content hash of the resource,
    combined with an allocation counter to ensure uniqueness even
    for identical content. -/
structure ResourceId where
  /-- The content hash -/
  hash : ByteArray
  /-- Allocation counter (for uniqueness of identical content) -/
  counter : Nat
deriving BEq, Inhabited

instance : Repr ResourceId where
  reprPrec rid _ := s!"ResourceId({rid.counter})"

instance : DecidableEq ResourceId := fun a b =>
  if h : a.hash = b.hash ∧ a.counter = b.counter then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl⟩)

/-- Comparison for ResourceId (lexicographic on hash, then counter). -/
def ResourceId.compare (a b : ResourceId) : Ordering :=
  match Ord.compare a.hash.toList b.hash.toList with
  | .eq => Ord.compare a.counter b.counter
  | ord => ord

instance : Ord ResourceId where
  compare := ResourceId.compare

instance : Hashable ResourceId where
  hash rid := rid.hash.foldl (fun acc b => acc ^^^ b.toUInt64) rid.counter.toUInt64

/-- Display a ResourceId as a short hex string. -/
def ResourceId.toShortHex (rid : ResourceId) : String :=
  let bytes := rid.hash.toList.take 4
  let hex := bytes.foldl (fun s b =>
    let hi := b.toNat / 16
    let lo := b.toNat % 16
    let hexChar (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    s.push (hexChar hi) |>.push (hexChar lo)
  ) ""
  s!"{hex}:{rid.counter}"

instance : ToString ResourceId := ⟨ResourceId.toShortHex⟩

/-- Resource kinds that can be allocated on the heap.

    All resources are immutable and content-addressed.
    Note: LocalTypeR and ByteArray don't derive Repr/BEq, so we use simplified versions. -/
inductive Resource where
  /-- A communication channel between roles -/
  | channel : ChannelState → Resource
  /-- A message in transit -/
  | message : Message → Resource
  /-- Current session state for a role (stores role name and type hash) -/
  | session : String → Nat → Resource
  /-- An arbitrary value (stores tag and size) -/
  | value : String → Nat → Resource
deriving Repr, BEq, Inhabited

/-- Get the resource kind as a string. -/
def Resource.kind : Resource → String
  | .channel _ => "channel"
  | .message _ => "message"
  | .session _ _ => "session"
  | .value tag _ => s!"value({tag})"

instance : ToString Resource where
  toString r := s!"Resource({r.kind})"

/-- Errors that can occur during heap operations. -/
inductive HeapError where
  /-- Resource not found in heap -/
  | notFound : ResourceId → HeapError
  /-- Resource already consumed (nullified) -/
  | alreadyConsumed : ResourceId → HeapError
  /-- Resource already exists with this ID -/
  | alreadyExists : ResourceId → HeapError
  /-- Invalid resource type for operation -/
  | typeMismatch : String → String → HeapError
  /-- Generic error with message -/
  | other : String → HeapError
deriving Repr, BEq

instance : ToString HeapError where
  toString
    | .notFound rid => s!"Resource not found: {rid}"
    | .alreadyConsumed rid => s!"Resource already consumed: {rid}"
    | .alreadyExists rid => s!"Resource already exists: {rid}"
    | .typeMismatch expected got => s!"Type mismatch: expected {expected}, got {got}"
    | .other msg => msg

/-- Serialize a resource to bytes for content addressing.

    This is a placeholder implementation. A real implementation
    would use DAG-CBOR or similar canonical serialization. -/
def Resource.toBytes : Resource → ByteArray
  | .channel cs =>
    let header := "channel:".toUTF8
    let sender := cs.sender.toUTF8
    let receiver := cs.receiver.toUTF8
    let size := cs.queueSize.toDigits 10 |>.foldl (fun ba d => ba.push d.val.toUInt8) ByteArray.empty
    header ++ sender ++ receiver ++ size
  | .message msg =>
    let header := "message:".toUTF8
    let source := msg.source.toUTF8
    let dest := msg.dest.toUTF8
    let label := msg.label.toUTF8
    let seqNo := msg.seqNo.toDigits 10 |>.foldl (fun ba d => ba.push d.val.toUInt8) ByteArray.empty
    header ++ source ++ dest ++ label ++ seqNo
  | .session role typeHash =>
    let header := "session:".toUTF8
    let roleBytes := role.toUTF8
    let hashBytes := typeHash.toDigits 16 |>.foldl (fun ba d => ba.push d.val.toUInt8) ByteArray.empty
    header ++ roleBytes ++ hashBytes
  | .value tag size =>
    let header := "value:".toUTF8
    let tagBytes := tag.toUTF8
    let sizeBytes := size.toDigits 10 |>.foldl (fun ba d => ba.push d.val.toUInt8) ByteArray.empty
    header ++ tagBytes ++ sizeBytes

/-- Create a ResourceId from a resource and allocation counter. -/
def ResourceId.fromResource [Hasher H] (r : Resource) (counter : Nat) : ResourceId :=
  let contentBytes := r.toBytes
  let counterBytes := counter.toDigits 16 |>.foldl (fun ba d => ba.push d.val.toUInt8) ByteArray.empty
  let combined := contentBytes ++ counterBytes
  ⟨Hasher.hash H combined, counter⟩

/-- Create a ResourceId using default SHA-256 hasher. -/
def ResourceId.create (r : Resource) (counter : Nat) : ResourceId :=
  ResourceId.fromResource (H := Sha256Hasher) r counter

end Rumpsteak.Protocol.Resource
