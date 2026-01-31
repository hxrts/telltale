import Std
import Protocol.Environments.Part1
import Runtime.VM.Core
import Runtime.VM.TypeClasses
import Runtime.Compat.RA

/-!
# Task 14: Buffer Resource Algebra

Ghost state for bounded buffers and refinement chain from iris_runtime_2.md §6.

## Definitions

- `BufferRA` — ghost gmap from Edge to buffer state
- `BoundedBuffer`, `enqueue`, `dequeue`
- `BufferConfig` — capacity, backpressure policy
- `bounded_refines_unbounded`
- `shared_refines_reliable` / `reliable_refines_unreliable`

Dependencies: Shim.ResourceAlgebra.
-/

set_option autoImplicit false

/-! ## Buffer backings -/

structure AckState where
  -- Unreliable transport acknowledgment state.
  nextSeqNo : Nat
  unacked : List (Nat × Value)
  retransmitQueue : List Nat
  deriving Repr

def AckState.empty : AckState :=
  -- Empty acknowledgment state for fresh unreliable edges.
  { nextSeqNo := 0, unacked := [], retransmitQueue := [] }

inductive BufferBacking where
  -- Shared memory: zero-copy arena region.
  | shared (region : Addr)
  -- Reliable transport: serialized over an edge.
  | reliable (localAddr : Addr) (edge : Edge)
  -- Unreliable transport: serialized with ack/retransmit.
  | unreliable (localAddr : Addr) (edge : Edge) (ack : AckState)
  -- Handler-backed: effect handler implements transport.
  | handled (handler : HandlerId) (edge : Edge)
  deriving Repr

def selectBacking (topo : Topology)
    (r1 r2 : RoleName) (localAddr : Addr) (edge : Edge)
    (handler : Option HandlerId := none) : BufferBacking :=
  -- Select the backing from the topology unless overridden by a handler.
  match handler with
  | some h => .handled h edge
  | none =>
      if satisfiesBool topo (.colocated r1 r2) then .shared localAddr
      else if satisfiesBool topo (.reliableEdge r1 r2) then .reliable localAddr edge
      else .unreliable localAddr edge AckState.empty

/-! ## Buffer modes and policies -/

inductive BufferMode where
  -- FIFO preserves message order.
  | fifo
  -- Latest value overwrites earlier sends.
  | latestValue
  deriving Repr, DecidableEq

inductive BackpressurePolicy where
  -- Block the sender until space is available.
  | block
  -- Drop the new message on overflow.
  | drop
  -- Signal an error on overflow.
  | error
  -- Resize up to the given maximum capacity.
  | resize (maxCapacity : Nat)
  deriving Repr, DecidableEq

structure BufferConfig where
  -- Mode controls overwrite vs FIFO queueing.
  mode : BufferMode
  -- Initial capacity (ignored for latestValue).
  initialCapacity : Nat
  -- Backpressure policy when full.
  policy : BackpressurePolicy
  deriving Repr

def BufferConfig.capacity (cfg : BufferConfig) : Nat :=
  -- Latest-value buffers always use capacity 1.
  match cfg.mode with
  | .fifo => cfg.initialCapacity
  | .latestValue => 1

/-! ## Bounded buffer state -/

structure BoundedBuffer where
  -- Ring buffer with epoch tracking.
  cfg : BufferConfig
  data : Array (Option Value)
  head : Nat
  tail : Nat
  count : Nat
  epoch : Nat
  deriving Repr

def BoundedBuffer.capacity (buf : BoundedBuffer) : Nat :=
  -- Effective capacity derived from configuration.
  BufferConfig.capacity buf.cfg

def BoundedBuffer.wf (buf : BoundedBuffer) : Prop :=
  -- Well-formed ring buffer invariants.
  buf.data.size = buf.capacity ∧
  buf.count ≤ buf.capacity ∧
  (buf.head < buf.capacity ∨ buf.capacity = 0) ∧
  (buf.tail < buf.capacity ∨ buf.capacity = 0)

def BoundedBuffer.empty (cfg : BufferConfig) : BoundedBuffer :=
  -- Allocate an empty buffer with zeroed indices.
  let cap := BufferConfig.capacity cfg
  { cfg := cfg
  , data := Array.replicate cap none
  , head := 0
  , tail := 0
  , count := 0
  , epoch := 0 }

def BoundedBuffer.isFull (buf : BoundedBuffer) : Bool :=
  -- Full when count reaches capacity.
  buf.count == buf.capacity

def BoundedBuffer.isEmpty (buf : BoundedBuffer) : Bool :=
  -- Empty when count is zero.
  buf.count == 0

def BoundedBuffer.nextIndex (buf : BoundedBuffer) (i : Nat) : Nat :=
  -- Advance a ring index with wraparound.
  if buf.capacity = 0 then 0 else (i + 1) % buf.capacity

def BoundedBuffer.setSlot (buf : BoundedBuffer) (i : Nat) (v : Value) : Array (Option Value) :=
  -- Write a value into the underlying ring storage.
  if h : i < buf.data.size then
    buf.data.set (i := i) (v := some v) (h := h)
  else
    buf.data

def BoundedBuffer.getSlot (buf : BoundedBuffer) (i : Nat) : Option Value :=
  -- Read a value from the ring storage.
  match buf.data[i]? with
  | none => none
  | some ov => ov

inductive EnqueueResult where
  -- Result of attempting to enqueue under backpressure.
  | ok (buf : BoundedBuffer)
  | blocked
  | dropped
  | error
  deriving Repr

def BoundedBuffer.toList (buf : BoundedBuffer) : List Value :=
  -- Linearize the ring buffer into FIFO order.
  let cap := buf.capacity
  let rec go (i : Nat) (n : Nat) (acc : List Value) : List Value :=
    if n = 0 then acc
    else
      let idx := if cap = 0 then 0 else (buf.head + i) % cap
      match buf.getSlot idx with
      | none => go (i + 1) (n - 1) acc
      | some v => go (i + 1) (n - 1) (acc ++ [v])
  go 0 buf.count []

def BoundedBuffer.loadArray (cap : Nat) (vals : List Value) : Array (Option Value) :=
  -- Load values into a fresh array (truncating beyond capacity).
  let data := Array.replicate cap none
  let rec go (i : Nat) (acc : Array (Option Value)) (xs : List Value) : Array (Option Value) :=
    match xs with
    | [] => acc
    | v :: vs =>
        if h : i < acc.size then
          go (i + 1) (acc.set (i := i) (v := some v) (h := h)) vs
        else
          acc
  go 0 data vals

def BoundedBuffer.resize (buf : BoundedBuffer) (newCap : Nat) : BoundedBuffer :=
  -- Resize by linearizing and reloading into a larger array.
  let cap := Nat.max newCap buf.capacity
  let values := buf.toList
  let used := Nat.min values.length cap
  let data' := BoundedBuffer.loadArray cap values
  { buf with data := data', head := 0, tail := used, count := used }

def BoundedBuffer.enqueueFIFO_noResize (buf : BoundedBuffer) (v : Value) : EnqueueResult :=
  -- FIFO enqueue without resizing (single attempt).
  if buf.count < buf.capacity then
    let data' := buf.setSlot buf.tail v
    let tail' := buf.nextIndex buf.tail
    .ok { buf with data := data', tail := tail', count := buf.count + 1 }
  else
    .blocked

def BoundedBuffer.enqueueFIFO (buf : BoundedBuffer) (v : Value) : EnqueueResult :=
  -- FIFO enqueue with policy-aware overflow handling.
  if buf.count < buf.capacity then
    BoundedBuffer.enqueueFIFO_noResize buf v
  else
    match buf.cfg.policy with
    | .block => .blocked
    | .drop => .dropped
    | .error => .error
    | .resize maxCap =>
        if buf.capacity < maxCap then
          let buf' := BoundedBuffer.resize buf maxCap
          BoundedBuffer.enqueueFIFO_noResize buf' v
        else
          .blocked

def BoundedBuffer.enqueueLatest (buf : BoundedBuffer) (v : Value) : EnqueueResult :=
  -- Latest-value enqueue overwrites slot 0.
  let data' := buf.setSlot 0 v
  let count' := if buf.capacity = 0 then 0 else 1
  .ok { buf with data := data', head := 0, tail := 0, count := count' }

def BoundedBuffer.enqueue (buf : BoundedBuffer) (v : Value) : EnqueueResult :=
  -- Mode dispatch for enqueue.
  match buf.cfg.mode with
  | .fifo => BoundedBuffer.enqueueFIFO buf v
  | .latestValue => BoundedBuffer.enqueueLatest buf v

def BoundedBuffer.dequeue (buf : BoundedBuffer) : Option (BoundedBuffer × Value) :=
  -- FIFO dequeue; latest-value uses the same interface.
  if buf.count = 0 then
    none
  else
    match buf.getSlot buf.head with
    | none => none
    | some v =>
        let head' := buf.nextIndex buf.head
        let buf' := { buf with head := head', count := buf.count - 1 }
        some (buf', v)

def BoundedBuffer.drainEpoch (buf : BoundedBuffer) (newEpoch : Nat) : BoundedBuffer :=
  -- Clear the buffer and bump the epoch.
  { buf with data := Array.replicate buf.capacity none, head := 0, tail := 0, count := 0, epoch := newEpoch }

/-! ## Refinement stubs -/

abbrev BufferRA := GMap Edge BoundedBuffer -- Ghost map for edge buffers.

def IsSharedTrace (_trace : List Value) : Prop :=
  -- Placeholder shared-memory trace predicate.
  True

def IsReliableTrace (_trace : List Value) : Prop :=
  -- Placeholder reliable transport trace predicate.
  True

def IsUnreliableTrace (_trace : List Value) : Prop :=
  -- Placeholder unreliable transport trace predicate.
  True

def IsHandledTrace (_handler : HandlerId) (_trace : List Value) : Prop :=
  -- Placeholder handler-backed trace predicate.
  True

def SameMessages (t1 t2 : List Value) : Prop :=
  -- Observational equality over message sequences.
  t1 = t2

def shared_refines_reliable : Prop :=
  -- Shared backing refines reliable backing.
  ∀ trace, IsSharedTrace trace → IsReliableTrace trace

def reliable_refines_unreliable : Prop :=
  -- Reliable backing refines unreliable backing.
  ∀ trace, IsReliableTrace trace → IsUnreliableTrace trace

def handled_refines_any : Prop :=
  -- Handler-backed traces refine any backing satisfying the transport spec.
  ∀ handler trace, IsHandledTrace handler trace → ∃ backingTrace, SameMessages trace backingTrace

def spatial_le_backing_refines : Prop :=
  -- Spatial subtyping lifts to buffer backing refinement.
  True

def bounded_refines_unbounded : Prop :=
  -- Bounded FIFO refines unbounded FIFO at the message level.
  True

def latest_value_refines_unbounded : Prop :=
  -- Latest-value buffers refine unbounded FIFO by dropping intermediates.
  True
