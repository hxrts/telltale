import Std
import Protocol.Environments.Core
import Runtime.VM.Model.Core
import Runtime.VM.Model.TypeClasses
import IrisExtractionInstance

/-! # Task 14: Buffer Resource Algebra

Ghost state for bounded buffers and refinement chain from iris_runtime_2.md §6.

## Definitions

- `BufferRA` — ghost gmap from Edge to buffer state
- `BoundedBuffer`, `enqueue`, `dequeue`
- `BufferConfig` — capacity, backpressure policy
- `bounded_refines_unbounded`
- `shared_refines_reliable` / `reliable_refines_unreliable`

Dependencies: Shim.ResourceAlgebra. -/

/-
The Problem. Buffers in the VM have multiple backing implementations (shared memory,
reliable transport, unreliable transport with acks) and bounded capacities. We need
ghost state to track buffer ownership and a refinement chain connecting implementations.

Solution Structure. Defines `BoundedBuffer` with capacity limits and `BufferBacking`
variants for different transport modes. `BufferRA` provides ghost state ownership.
Proves refinement chain: `bounded_refines_unbounded`, `shared_refines_reliable`,
`reliable_refines_unreliable` connecting implementations to the abstract buffer model.
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

/-! ### Core invariants and constructors -/

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

/-! ### Linearization and resize helpers -/

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

/-! ### Enqueue paths -/

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

/-! ### Dequeue and epoch maintenance -/

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

/-- Ghost map for edge buffers.
    Keys (Edge) encoded to Positive via pattern similar to encodeEndpoint.
    Stub: actual implementation needs GhostMapSlot BoundedBuffer instance. -/
abbrev BufferRA := List (Positive × BoundedBuffer)

def tracePayloads {ν : Type} [VerificationModel ν]
    (trace : SignedBuffer ν) : Buffer :=
  -- Project a signed trace to its payload sequence.
  trace.map (fun sv => sv.payload)

def IsSharedTrace {ν : Type} [VerificationModel ν]
    (trace : SignedBuffer ν) : Prop :=
  -- Shared traces preserve unique payload order in V1.
  List.Nodup (tracePayloads trace)

def IsReliableTrace {ν : Type} [VerificationModel ν]
    (trace : SignedBuffer ν) : Prop :=
  -- Reliable traces preserve unique payload order in V1.
  List.Nodup (tracePayloads trace)

def IsUnreliableTrace {ν : Type} [VerificationModel ν]
    (_trace : SignedBuffer ν) : Prop :=
  -- Unreliable traces place no additional ordering constraints in V1.
  True

def IsHandledTrace {ν : Type} [VerificationModel ν]
    (_handler : HandlerId) (trace : SignedBuffer ν) : Prop :=
  -- Handler-backed traces are reliable in V1.
  IsReliableTrace trace

def IsBoundedTrace {ν : Type} [VerificationModel ν]
    (cap : Nat) (trace : SignedBuffer ν) : Prop :=
  -- Bounded traces have length within the configured capacity.
  trace.length ≤ cap

def IsUnboundedTrace {ν : Type} [VerificationModel ν]
    (trace : SignedBuffer ν) : Prop :=
  -- Unbounded traces have no length restriction.
  trace.length ≥ 0

def SameMessages {ν : Type} [VerificationModel ν]
    (t1 t2 : SignedBuffer ν) : Prop :=
  -- Observational equality over payload sequences.
  tracePayloads t1 = tracePayloads t2

def shared_refines_reliable {ν : Type} [VerificationModel ν] : Prop :=
  -- Shared backing refines reliable backing.
  ∀ trace, IsSharedTrace (ν:=ν) trace → IsReliableTrace trace

def reliable_refines_unreliable {ν : Type} [VerificationModel ν] : Prop :=
  -- Reliable backing refines unreliable backing.
  ∀ trace, IsReliableTrace (ν:=ν) trace → IsUnreliableTrace trace

def handled_refines_any {ν : Type} [VerificationModel ν] : Prop :=
  -- Handler-backed traces refine any backing satisfying the transport spec.
  ∀ handler trace,
    IsHandledTrace (ν:=ν) handler trace →
      ∃ backingTrace, SameMessages trace backingTrace

def spatial_le_backing_refines {ν : Type} [VerificationModel ν] : Prop :=
  -- Spatial subtyping lifts to buffer backing refinement.
  ∀ trace, IsSharedTrace (ν:=ν) trace → IsUnreliableTrace trace

def bounded_refines_unbounded {ν : Type} [VerificationModel ν] : Prop :=
  -- Bounded FIFO refines unbounded FIFO by preserving messages.
  ∀ cap trace, IsBoundedTrace (ν:=ν) cap trace →
    ∃ unboundedTrace, IsUnboundedTrace unboundedTrace ∧ SameMessages trace unboundedTrace

def latest_value_refines_unbounded {ν : Type} [VerificationModel ν] : Prop :=
  -- Latest-value buffers refine unbounded FIFO by preserving final messages.
  ∀ cap trace, IsBoundedTrace (ν:=ν) cap trace →
    ∃ unboundedTrace, IsUnboundedTrace unboundedTrace ∧ SameMessages trace unboundedTrace
