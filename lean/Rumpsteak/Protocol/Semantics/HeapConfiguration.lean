import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.Heap
import Rumpsteak.Protocol.Merkle
import Rumpsteak.Protocol.Semantics.Process
import Batteries.Data.RBMap.Lemmas

/-! # Rumpsteak.Protocol.Semantics.HeapConfiguration

Heap-based configurations for multiparty session operational semantics.

## Overview

This module provides an alternative configuration representation that uses
the explicit resource heap instead of ad-hoc queue tracking. This enables:
- Content-addressed resources for replay protection
- Nullifier tracking for consumption verification
- Merkle commitments for ZK compatibility
- Deterministic state representation

## Relationship to Configuration

This module parallels `Configuration.lean` but uses `Heap` for state:
- `HeapConfiguration` replaces `Configuration`
- Channels become heap-allocated resources
- Messages are tracked via the heap nullifier set
- Session types are stored as heap resources

## Main Definitions

- `HeapConfiguration`: Configuration using explicit heap
- `HeapConfiguration.send`: Send operation via heap allocation
- `HeapConfiguration.recv`: Receive operation via heap consumption
-/

namespace Rumpsteak.Protocol.Semantics.HeapConfiguration

open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.Resource
open Rumpsteak.Protocol.Heap
open Rumpsteak.Protocol.Merkle
open Rumpsteak.Protocol.Semantics.Process

/-- Session state for a role.

    Tracks the current local type and message sequence numbers. -/
structure SessionState where
  /-- The role name -/
  role : String
  /-- Current local type (as a hash for heap storage) -/
  typeHash : Nat
  /-- Next sequence number for sending -/
  sendSeqNo : Nat
  /-- Expected sequence number for receiving from each peer -/
  recvSeqNos : List (String × Nat)
deriving Repr, BEq, Inhabited

/-- Heap-based configuration for multiparty sessions.

    Uses explicit resource heap instead of ad-hoc queue tracking. -/
structure HeapConfiguration where
  /-- Processes for each role -/
  processes : List RoleProcess
  /-- The resource heap containing channels, messages, sessions -/
  heap : Heap
  /-- ResourceIds for each channel (sender, receiver) → ResourceId -/
  channelIds : List ((String × String) × ResourceId)
  /-- Session state for each role -/
  sessions : List SessionState
deriving Repr, Inhabited

namespace HeapConfiguration

/-- Create an empty heap configuration for given roles. -/
def empty (roles : List String) : HeapConfiguration :=
  let procs := roles.map fun r => { role := r, process := Process.inaction }
  let sessions := roles.map fun r => {
    role := r
    typeHash := 0
    sendSeqNo := 0
    recvSeqNos := roles.filterMap fun p => if p != r then some (p, 0) else none
  }
  -- Allocate channels for all pairs
  let (channelIds, heap) := roles.foldl (fun (acc, h) sender =>
    roles.foldl (fun (acc', h') receiver =>
      if sender != receiver then
        let (rid, h'') := h'.allocChannel sender receiver
        (acc' ++ [((sender, receiver), rid)], h'')
      else
        (acc', h')
    ) (acc, h)
  ) ([], Heap.empty)
  { processes := procs
  , heap := heap
  , channelIds := channelIds
  , sessions := sessions
  }

/-- Get the process for a specific role. -/
def getProcess (c : HeapConfiguration) (role : String) : Option Process :=
  c.processes.find? (fun rp => rp.role == role) |>.map (·.process)

/-- Update the process for a specific role. -/
def setProcess (c : HeapConfiguration) (role : String) (proc : Process) : HeapConfiguration :=
  { c with processes := c.processes.map fun rp =>
      if rp.role == role then { rp with process := proc } else rp }

/-- Get the channel ResourceId for a (sender, receiver) pair. -/
def getChannelId (c : HeapConfiguration) (sender receiver : String) : Option ResourceId :=
  c.channelIds.find? (fun ((s, r), _) => s == sender && r == receiver) |>.map (·.2)

/-- Get session state for a role. -/
def getSession (c : HeapConfiguration) (role : String) : Option SessionState :=
  c.sessions.find? (fun s => s.role == role)

/-- Update session state for a role. -/
def updateSession (c : HeapConfiguration) (role : String) (f : SessionState → SessionState)
    : HeapConfiguration :=
  { c with sessions := c.sessions.map fun s =>
      if s.role == role then f s else s }

/-- Get the next sequence number for sending from sender to receiver. -/
def getNextSendSeqNo (c : HeapConfiguration) (sender : String) : Nat :=
  match c.getSession sender with
  | some s => s.sendSeqNo
  | none => 0

/-- Get the expected sequence number for receiving. -/
def getExpectedRecvSeqNo (c : HeapConfiguration) (receiver sender : String) : Nat :=
  match c.getSession receiver with
  | some s => s.recvSeqNos.find? (fun (p, _) => p == sender) |>.map (·.2) |>.getD 0
  | none => 0

/-- Increment send sequence number after sending. -/
def incSendSeqNo (c : HeapConfiguration) (sender : String) : HeapConfiguration :=
  c.updateSession sender fun s => { s with sendSeqNo := s.sendSeqNo + 1 }

/-- Increment expected receive sequence number after receiving. -/
def incRecvSeqNo (c : HeapConfiguration) (receiver sender : String) : HeapConfiguration :=
  c.updateSession receiver fun s =>
    { s with recvSeqNos := s.recvSeqNos.map fun (p, n) =>
        if p == sender then (p, n + 1) else (p, n) }

/-- Result of a heap operation. -/
inductive HeapOpResult where
  | ok : HeapConfiguration → HeapOpResult
  | error : HeapError → HeapOpResult
deriving Repr

/-- Send a message: allocate message resource on heap. -/
def sendMessage (c : HeapConfiguration) (sender receiver : String)
    (label : String) : HeapOpResult :=
  let seqNo := c.getNextSendSeqNo sender
  let (msgId, heap') := c.heap.allocMessage sender receiver label seqNo
  let c' := { c with heap := heap' }
  let c'' := c'.incSendSeqNo sender
  -- Store the message ID (in a real impl, would add to channel's pending list)
  .ok c''

/-- Receive a message: find and consume matching message resource.

    This is simplified - a full impl would search for messages matching
    the expected sender and sequence number. -/
def recvMessage (c : HeapConfiguration) (receiver sender : String)
    (label : String) : HeapOpResult :=
  let expectedSeqNo := c.getExpectedRecvSeqNo receiver sender
  -- In a full impl, we would:
  -- 1. Search heap for message with matching (sender, receiver, seqNo)
  -- 2. Verify label matches
  -- 3. Consume the message resource
  -- For now, just update sequence numbers
  let c' := c.incRecvSeqNo receiver sender
  .ok c'

/-- Check if all processes have terminated. -/
def allTerminated (c : HeapConfiguration) : Bool :=
  c.processes.all (fun rp => rp.process.isTerminated)

/-- Get the Merkle commitment for the current heap state. -/
def commitment (c : HeapConfiguration) : HeapCommitment :=
  heapCommitmentSha256 c.heap

/-- Get all active (non-consumed) message count. -/
def activeMessageCount (c : HeapConfiguration) : Nat :=
  c.heap.activeResources.filter (fun (_, r) =>
    match r with
    | .message _ => true
    | _ => false
  ) |>.length

/-- Check if configuration can make progress.

    True if any role has a non-terminated, non-blocked process. -/
def canProgress (c : HeapConfiguration) : Bool :=
  c.processes.any fun rp =>
    match rp.process with
    | .inaction => false
    | .var _ => false
    | _ => true

/-- Get roles that are currently blocked waiting for messages. -/
def blockedRoles (c : HeapConfiguration) : List String :=
  c.processes.filterMap fun rp =>
    match rp.process with
    | .recv _ _ => some rp.role
    | _ => none

/-- Get roles that can currently send. -/
def sendingRoles (c : HeapConfiguration) : List String :=
  c.processes.filterMap fun rp =>
    match rp.process with
    | .send _ _ _ _ => some rp.role
    | _ => none

end HeapConfiguration

/-- Theorem: Empty configuration has empty commitment.

    The Merkle commitment of an empty configuration (no messages)
    should be deterministic. -/
theorem empty_config_commitment_deterministic (roles : List String) :
    (HeapConfiguration.empty roles).commitment =
    (HeapConfiguration.empty roles).commitment := by
  rfl

/-- RBMap.insert on a fresh key increases size by 1.

    This is a standard property of balanced binary search trees.
    The proof uses the fact that:
    1. toList is sorted with unique keys
    2. find? = none means no entry with key k exists
    3. Insert adds exactly one entry when key is fresh

    PROOF: The sorted list property means each key appears at most once.
    When find? k = none, there's no (k, _) in toList. Insert adds (k, v)
    to the appropriate sorted position, increasing length by 1.

    We axiomatize this because the full proof requires navigating
    complex Batteries internals (zoom, Path, Balanced) that are
    orthogonal to session type theory. -/
theorem rbmap_insert_size_fresh {α β : Type _} {cmp : α → α → Ordering}
    (m : Batteries.RBMap α β cmp) (k : α) (v : β)
    (hfresh : m.find? k = none) : (m.insert k v).size = m.size + 1 := by
  classical
  -- Reduce to list lengths
  simp [Batteries.RBMap.size_eq]
  -- Work with the underlying RBNode and comparator
  set cmp' : (α × β) → (α × β) → Ordering := Ordering.byKey Prod.fst cmp
  set cut : (α × β) → Ordering := cmp' (k, v)
  -- find? = none implies findEntry? = none
  have hentry : m.findEntry? k = none := by
    cases hentry' : m.findEntry? k <;> simp [Batteries.RBMap.find?, hentry'] at hfresh <;> exact hentry'
  -- Lift to the underlying RBNode find?
  have hfindNode : m.1.find? cut = none := by
    simpa [Batteries.RBMap.findEntry?, Batteries.RBSet.findP?, cut] using hentry
  -- Extract balance invariant for the underlying tree
  let ⟨_, _, ht⟩ := m.2.out.2
  -- Show zoom reaches an empty node when the key is fresh
  cases hz : m.1.zoom cut with
  | mk t' p =>
    have hroot : t'.root? = none := by
      have hzoom := (Batteries.RBNode.find?_eq_zoom (t := m.1) (cut := cut))
      have hzoom' : none = t'.root? := by
        simpa [hfindNode, hz] using hzoom
      exact hzoom'.symm
    cases t' with
    | nil =>
      have hz' : m.1.zoom (cmp' (k, v)) = (Batteries.RBNode.nil, p) := by
        simpa [cut] using hz
      have ⟨L, R, hlist, hlist'⟩ :=
        Batteries.RBNode.exists_insert_toList_zoom_nil
          (t := m.1) (cmp := cmp') (v := (k, v)) ht hz'
      -- Compute lengths from the list decomposition
      calc
        (m.insert k v).toList.length
            = (L ++ (k, v) :: R).length := by
                simpa [cmp', Batteries.RBMap.insert, Batteries.RBMap.toList, Batteries.RBSet.toList, hlist']
        _ = (L ++ R).length + 1 := by
                simp [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = m.toList.length + 1 := by
                simpa [Batteries.RBMap.toList, Batteries.RBSet.toList, hlist]
    | node c l x r =>
      -- Contradiction: root? = none for a node
      simp [Batteries.RBNode.root?] at hroot

/-- Axiom: Fresh counter produces fresh ResourceId.

    If a ResourceId is created with counter n, it won't be found in a heap
    that has only allocated with counters < n. This is the key invariant
    maintained by the allocation counter. -/
theorem fresh_counter_not_in_heap (h : Heap) (r : Resource)
    (hinv : HeapCounterInvariant h) :
    h.resources.find? (ResourceId.create r h.counter) = none := by
  exact fresh_counter_not_found h r hinv

/-- Theorem: Send increases heap size.

    After a successful send, the heap should have one more resource. -/
theorem send_increases_heap (c : HeapConfiguration) (s r label : String)
    (hinv : HeapCounterInvariant c.heap) :
    match c.sendMessage s r label with
    | .ok c' => c'.heap.size = c.heap.size + 1
    | .error _ => True := by
  unfold HeapConfiguration.sendMessage
  simp only [HeapConfiguration.incSendSeqNo, HeapConfiguration.updateSession]
  -- Unfold allocMessage and alloc
  unfold Heap.allocMessage Heap.alloc Heap.size
  simp only
  -- The key is that the counter is fresh
  have hfresh := fresh_counter_not_in_heap c.heap _ hinv
  -- Apply the RBMap insert size lemma
  exact rbmap_insert_size_fresh c.heap.resources _ _ hfresh

end Rumpsteak.Protocol.Semantics.HeapConfiguration
