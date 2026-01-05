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

/-! ## Heap Counter Invariant

The heap maintains an allocation counter that ensures all ResourceIds are unique.
Every ResourceId in the heap was created with a counter value strictly less than
the current counter, ensuring that `ResourceId.create r h.counter` is always fresh. -/

/-- The heap counter invariant: all ResourceIds in the heap have counter < h.counter.

    This invariant ensures that the current counter value always produces fresh ResourceIds.
    It is established by `empty` and preserved by `alloc`. -/
def HeapCounterInvariant (h : Heap) : Prop :=
  ∀ rid, h.resources.contains rid → rid.counter < h.counter

/-- Empty heap satisfies the counter invariant (vacuously true). -/
theorem empty_counter_invariant : HeapCounterInvariant Heap.empty := by
  intro rid hcontains
  simp only [Heap.empty, Batteries.RBMap.contains, Batteries.RBMap.find?] at hcontains
  simp only [Batteries.RBMap.empty, Batteries.RBMap.find?, Batteries.RBNode.find?] at hcontains
  contradiction

/-- Allocation preserves the counter invariant.

    When we allocate a resource:
    1. The new ResourceId has counter = h.counter
    2. The new heap has counter = h.counter + 1
    3. All old ResourceIds have counter < h.counter < h.counter + 1
    4. The new ResourceId has counter = h.counter < h.counter + 1

    AXIOM RATIONALE: This proof requires Batteries RBMap lemmas with TransCmp instances
    for ResourceId.compare. The property is straightforward: if all keys in the old map
    have counter < h.counter, and we insert a key with counter = h.counter, then all
    keys in the new map have counter < h.counter + 1. -/
theorem alloc_preserves_invariant (h : Heap) (r : Resource)
    (hinv : HeapCounterInvariant h) :
    let (_, h') := h.alloc r
    HeapCounterInvariant h' := by
  intro rid hcontains'
  simp only [Heap.alloc] at *
  -- h' has counter = h.counter + 1
  -- rid is either the new ResourceId or was in h.resources
  -- If it's new: rid.counter = h.counter < h.counter + 1
  -- If it's old: rid.counter < h.counter < h.counter + 1
  by_cases heq : rid = ResourceId.create r h.counter
  · -- New ResourceId
    subst heq
    simp only [ResourceId.create, ResourceId.fromResource]
    omega
  · -- Old ResourceId - was in h.resources
    -- We need to show rid was in h.resources (not just h'.resources)
    -- Since h'.resources = h.resources.insert newRid r, and rid ≠ newRid,
    -- rid must have been in h.resources
    have hlt := hinv rid
    -- rid.counter < h.counter < h.counter + 1
    have hctr : rid.counter < h.counter := by
      apply hlt
      -- Need to show: rid was in h.resources given rid ∈ h'.resources and rid ≠ newRid
      -- This requires RBMap lemmas about insert with TransCmp instance
      -- The property follows from: insert only adds the new key,
      -- so if rid ≠ newKey and rid ∈ insert, then rid ∈ original
      have hcmp : ResourceId.compare rid (ResourceId.create r h.counter) ≠ .eq := by
        intro hcmp
        apply heq
        exact (ResourceId.compare_eq_iff).1 hcmp
      rcases (Batteries.RBMap.contains_iff_find? (t := h.resources.insert (ResourceId.create r h.counter) r)
        (x := rid)).1 hcontains' with ⟨v, hv⟩
      have hv' : h.resources.find? rid = some v := by
        have hfind := Batteries.RBMap.find?_insert_of_ne
          (t := h.resources) (k := ResourceId.create r h.counter) (v := r) (k' := rid) hcmp
        simpa [hfind] using hv
      exact (Batteries.RBMap.contains_iff_find? (t := h.resources) (x := rid)).2 ⟨v, hv'⟩
    omega

/-- A ResourceId with the current counter is not in the heap (assuming invariant).

    PROOF: If rid.counter = h.counter and all ResourceIds in heap have counter < h.counter,
    then rid cannot be in the heap.

    AXIOM RATIONALE: This proof requires Batteries RBMap lemmas relating find? and findEntry?.
    The property is straightforward: a fresh counter cannot be in the heap. -/
theorem fresh_counter_not_found (h : Heap) (r : Resource)
    (hinv : HeapCounterInvariant h) :
    h.resources.find? (ResourceId.create r h.counter) = none := by
  -- Proof by cases on find?
  cases hfind : h.resources.find? (ResourceId.create r h.counter) with
  | none => rfl
  | some _ =>
    -- If found, then it's in the heap
    have hcontains : h.resources.contains (ResourceId.create r h.counter) := by
      apply (Batteries.RBMap.contains_iff_find? (t := h.resources)
        (x := ResourceId.create r h.counter)).2
      exact ⟨_, hfind⟩
    -- By invariant, its counter must be < h.counter
    have hlt := hinv (ResourceId.create r h.counter) hcontains
    -- But ResourceId.create r h.counter has counter = h.counter
    simp only [ResourceId.create, ResourceId.fromResource] at hlt
    -- h.counter < h.counter is false
    omega

end Rumpsteak.Protocol.Heap
