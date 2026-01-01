import Rumpsteak.Protocol.Resource
import Batteries.Data.RBMap
import Batteries.Data.RBMap.Lemmas

/-! # Rumpsteak.Protocol.Heap

Deterministic heap for explicit resource management.

## Overview

This module provides a pure, deterministic heap for managing protocol resources.
The heap uses RBMap/RBSet for O(log n) operations with deterministic iteration order.

Key properties:
- **Immutable**: All operations return new heaps (no mutation)
- **Deterministic**: Same operations produce identical results
- **Content-addressed**: Resources identified by content hash
- **Nullifier tracking**: Consumed resources are tracked to prevent double-spending

## Rust Correspondence

This module corresponds to `rust/choreography/src/heap/mod.rs`:
- `Heap` ↔ Rust's `Heap`
- `alloc` ↔ Rust's `Heap::alloc`
- `consume` ↔ Rust's `Heap::consume`
- `read` ↔ Rust's `Heap::read`

## Main Definitions

- `Heap`: The deterministic heap structure
- `Heap.empty`: Create an empty heap
- `Heap.alloc`: Allocate a new resource
- `Heap.consume`: Consume (nullify) a resource
- `Heap.read`: Read a resource without consuming
-/

open Rumpsteak.Protocol.Resource

namespace Rumpsteak.Protocol.Heap

/-- Deterministic heap for protocol resources.

    Uses RBMap for O(log n) operations with deterministic iteration order.
    The nullifiers set tracks consumed resources to prevent double-spending. -/
structure Heap where
  /-- Map from ResourceId to Resource -/
  resources : Batteries.RBMap ResourceId Resource ResourceId.compare
  /-- Set of consumed (nullified) resource IDs -/
  nullifiers : Batteries.RBMap ResourceId Unit ResourceId.compare
  /-- Counter for generating unique ResourceIds -/
  counter : Nat
deriving Repr

namespace Heap

/-- Create an empty heap. -/
def empty : Heap := {
  resources := Batteries.RBMap.empty
  nullifiers := Batteries.RBMap.empty
  counter := 0
}

/-- Get the number of active (non-nullified) resources. -/
def size (h : Heap) : Nat :=
  h.resources.size

/-- Get the number of nullified resources. -/
def nullifiedCount (h : Heap) : Nat :=
  h.nullifiers.size

/-- Check if a resource exists in the heap (not necessarily active). -/
def contains (h : Heap) (rid : ResourceId) : Bool :=
  h.resources.contains rid

/-- Check if a resource has been consumed (nullified). -/
def isConsumed (h : Heap) (rid : ResourceId) : Bool :=
  h.nullifiers.contains rid

/-- Check if a resource is active (exists and not consumed). -/
def isActive (h : Heap) (rid : ResourceId) : Bool :=
  h.contains rid && !h.isConsumed rid

/-- Allocate a new resource on the heap.

    Returns the new ResourceId and updated heap.
    The ResourceId is derived from the resource content and allocation counter. -/
def alloc (h : Heap) (r : Resource) : ResourceId × Heap :=
  let rid := ResourceId.create r h.counter
  let resources := h.resources.insert rid r
  let counter := h.counter + 1
  (rid, { h with resources, counter })

/-- Read a resource from the heap.

    Returns an error if the resource doesn't exist or has been consumed. -/
def read (h : Heap) (rid : ResourceId) : Except HeapError Resource :=
  if h.isConsumed rid then
    .error (.alreadyConsumed rid)
  else
    match h.resources.find? rid with
    | some r => .ok r
    | none => .error (.notFound rid)

/-- Consume a resource, adding it to the nullifier set.

    Returns an error if the resource doesn't exist or has already been consumed.
    The resource remains in the heap but is marked as consumed. -/
def consume (h : Heap) (rid : ResourceId) : Except HeapError Heap :=
  if h.isConsumed rid then
    .error (.alreadyConsumed rid)
  else if !h.contains rid then
    .error (.notFound rid)
  else
    let nullifiers := h.nullifiers.insert rid ()
    .ok { h with nullifiers }

/-- Remove a resource from the heap entirely (for cleanup).

    Unlike `consume`, this removes the resource from both maps.
    Returns an error if the resource doesn't exist. -/
def remove (h : Heap) (rid : ResourceId) : Except HeapError Heap :=
  if !h.contains rid then
    .error (.notFound rid)
  else
    let resources := h.resources.erase rid
    let nullifiers := h.nullifiers.erase rid
    .ok { h with resources, nullifiers }

/-- Get all active (non-consumed) resources. -/
def activeResources (h : Heap) : List (ResourceId × Resource) :=
  h.resources.toList.filter fun (rid, _) => !h.isConsumed rid

/-- Get all consumed resource IDs. -/
def consumedIds (h : Heap) : List ResourceId :=
  h.nullifiers.toList.map (·.1)

/-- Allocate multiple resources at once. -/
def allocMany (h : Heap) (rs : List Resource) : List ResourceId × Heap :=
  rs.foldl (fun (rids, heap) r =>
    let (rid, heap') := heap.alloc r
    (rids ++ [rid], heap')
  ) ([], h)

/-- Try to consume multiple resources atomically.

    If any consumption fails, returns the error without modifying the heap. -/
def consumeMany (h : Heap) (rids : List ResourceId) : Except HeapError Heap :=
  rids.foldlM (fun heap rid => heap.consume rid) h

/-- Create a channel resource and allocate it. -/
def allocChannel (h : Heap) (sender receiver : String) : ResourceId × Heap :=
  let channel := Resource.channel {
    sender := sender
    receiver := receiver
    queueSize := 0
  }
  h.alloc channel

/-- Create a message resource and allocate it. -/
def allocMessage (h : Heap) (src dst : String) (label : String) (seqNo : Nat)
    : ResourceId × Heap :=
  let msg := Resource.message {
    source := src
    dest := dst
    label := label
    seqNo := seqNo
  }
  h.alloc msg

/-- Create a session state resource and allocate it. -/
def allocSession (h : Heap) (role : String) (typeHash : Nat) : ResourceId × Heap :=
  let session := Resource.session role typeHash
  h.alloc session

/-- Get the current allocation counter. -/
def getAllocCounter (h : Heap) : Nat :=
  h.counter

/-- Compute a simple hash of the heap state (for debugging).

    A real implementation would compute a Merkle root. -/
def stateHash (h : Heap) : Nat :=
  let resourceHash := h.resources.toList.foldl (fun acc (rid, _) =>
    acc ^^^ rid.counter
  ) 0
  let nullifierHash := h.nullifiers.toList.foldl (fun acc (rid, _) =>
    acc ^^^ rid.counter
  ) 0
  resourceHash ^^^ nullifierHash ^^^ h.counter

end Heap

end Rumpsteak.Protocol.Heap
