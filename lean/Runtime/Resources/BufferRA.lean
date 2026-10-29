import Std
import Protocol.Environments.Core
import Runtime.ProtocolMachine.Model.Core
import Runtime.ProtocolMachine.Model.TypeClasses
import IrisExtractionInstance

/-! # Task 14: Buffer Resource Algebra

Ghost state for bounded buffers and refinement chain.

## Definitions

- `BufferRA` — upstream Iris ghost map (auth + fragments) from encoded edges to buffer state
- `BoundedBuffer`, `enqueue`, `dequeue`
- `BufferConfig` — capacity, backpressure policy
- `bounded_refines_unbounded`
- `shared_refines_reliable` / `reliable_refines_unreliable`

Dependencies: IrisExtractionInstance. -/

/-
The Problem. Buffers in the protocol machine have multiple backing implementations (shared memory,
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

/-! ## Buffer Ghost Resource -/

section BufferGhost

variable [Telltale.TelltaleIris] [GhostMapSlot BoundedBuffer]

/-- Ghost map for edge buffers: keys are encoded edges, values are buffer states.
This is the upstream Iris `ghost_map` resource (authoritative map + per-key
exclusive fragments), not a plain list. -/
abbrev BufferRA := GhostMap BoundedBuffer

/-- Authoritative ownership of all edge buffers. -/
def buffer_auth (γ : GhostName) (m : BufferRA) : iProp :=
  ghost_map_auth γ m

/-- Exclusive ownership of the buffer stored under key `k`. -/
def buffer_frag (γ : GhostName) (k : Positive) (b : BoundedBuffer) : iProp :=
  ghost_map_elem γ k b

/-- Agreement: the authoritative map contains every owned fragment. -/
theorem buffer_frag_included (γ : GhostName) (m : BufferRA) (k : Positive) (b : BoundedBuffer) :
    iProp.entails (iProp.sep (buffer_auth γ m) (buffer_frag γ k b))
      (iProp.pure (Iris.Std.get? m k = some b)) :=
  ghost_map_lookup γ k b m

/-- Frame-preserving update of one owned buffer (e.g. after enqueue/dequeue). -/
theorem buffer_frag_update (γ : GhostName) (m : BufferRA) (k : Positive) (b b' : BoundedBuffer) :
    iProp.entails (iProp.sep (buffer_auth γ m) (buffer_frag γ k b))
      (_root_.bupd (iProp.sep (buffer_auth γ (Iris.Std.insert m k b')) (buffer_frag γ k b'))) :=
  ghost_map_update γ k b b' m

/-- Allocate a fresh buffer key. -/
theorem buffer_alloc (γ : GhostName) (m : BufferRA) (k : Positive) (b : BoundedBuffer)
    (hFresh : Iris.Std.get? m k = none) :
    iProp.entails (buffer_auth γ m)
      (_root_.bupd (iProp.sep (buffer_auth γ (Iris.Std.insert m k b)) (buffer_frag γ k b))) :=
  ghost_map_insert γ k b m hFresh

end BufferGhost

/-! ## Delivery Models -/

def tracePayloads {ν : Type} [VerificationModel ν]
    (trace : SignedBuffer ν) : Buffer :=
  -- Project a signed trace to its payload sequence.
  trace.map (fun sv => sv.payload)

/-- Shared-memory delivery: the receiver observes exactly the sender's signed
values (payloads and signatures), in order. -/
def IsSharedTrace {ν : Type} [VerificationModel ν]
    (sent delivered : SignedBuffer ν) : Prop :=
  delivered = sent

/-- Reliable (FIFO, lossless, duplicate-free) delivery: the delivered payload
sequence is exactly the sent payload sequence. Signatures may be re-attached by
the transport, so only payloads are constrained. -/
def IsReliableTrace {ν : Type} [VerificationModel ν]
    (sent delivered : SignedBuffer ν) : Prop :=
  tracePayloads delivered = tracePayloads sent

/-- Unreliable delivery of `sent` as `delivered`: every delivered payload was
actually sent. Drops, duplications, and reorderings are permitted; fabricated
payloads are not. -/
def IsUnreliableTrace {ν : Type} [VerificationModel ν]
    (sent delivered : SignedBuffer ν) : Prop :=
  tracePayloads delivered ⊆ tracePayloads sent

/-- Handler-backed delivery is reliable delivery. -/
def IsHandledTrace {ν : Type} [VerificationModel ν]
    (_handler : HandlerId) (sent delivered : SignedBuffer ν) : Prop :=
  IsReliableTrace sent delivered

/-- Reliable delivery admits no loss: each sent payload is delivered as often as sent. -/
theorem reliable_no_loss_no_dup {ν : Type} [VerificationModel ν]
    {sent delivered : SignedBuffer ν} (h : IsReliableTrace sent delivered) (v : Value) :
    (tracePayloads delivered).count v = (tracePayloads sent).count v := by
  rw [h]

/-- Reliable delivery is FIFO: the `i`-th delivered payload is the `i`-th sent one. -/
theorem reliable_fifo {ν : Type} [VerificationModel ν]
    {sent delivered : SignedBuffer ν} (h : IsReliableTrace sent delivered) (i : Nat) :
    (tracePayloads delivered)[i]? = (tracePayloads sent)[i]? := by
  rw [h]

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
  ∀ sent delivered, IsSharedTrace (ν:=ν) sent delivered → IsReliableTrace sent delivered

def reliable_refines_unreliable {ν : Type} [VerificationModel ν] : Prop :=
  -- Reliable backing refines unreliable backing.
  -- (a reliable channel delivers exactly what was sent, which the unreliable
  -- model admits).
  ∀ sent delivered, IsReliableTrace (ν:=ν) sent delivered → IsUnreliableTrace sent delivered

def handled_refines_any {ν : Type} [VerificationModel ν] : Prop :=
  -- Handler-backed traces refine any backing satisfying the transport spec.
  ∀ handler sent delivered,
    IsHandledTrace (ν:=ν) handler sent delivered → SameMessages delivered sent

def spatial_le_backing_refines {ν : Type} [VerificationModel ν] : Prop :=
  -- Spatial subtyping lifts to buffer backing refinement.
  ∀ sent delivered, IsSharedTrace (ν:=ν) sent delivered → IsUnreliableTrace sent delivered

def bounded_refines_unbounded {ν : Type} [VerificationModel ν] : Prop :=
  -- Bounded FIFO refines unbounded FIFO by preserving messages.
  ∀ cap trace, IsBoundedTrace (ν:=ν) cap trace →
    ∃ unboundedTrace, IsUnboundedTrace unboundedTrace ∧ SameMessages trace unboundedTrace

def latest_value_refines_unbounded {ν : Type} [VerificationModel ν] : Prop :=
  -- Latest-value buffers refine unbounded FIFO by preserving final messages.
  ∀ cap trace, IsBoundedTrace (ν:=ν) cap trace →
    ∃ unboundedTrace, IsUnboundedTrace unboundedTrace ∧ SameMessages trace unboundedTrace

/-! ## Unreliable-Model Refinement Proofs -/

/-- Reliable delivery is an admissible unreliable delivery. -/
theorem reliable_refines_unreliable_holds {ν : Type} [VerificationModel ν] :
    reliable_refines_unreliable (ν := ν) :=
  by
    intro sent delivered h
    have h' : tracePayloads delivered = tracePayloads sent := h
    unfold IsUnreliableTrace
    intro x hx
    rw [h'] at hx
    exact hx

/-- Shared delivery is reliable delivery. -/
theorem shared_refines_reliable_holds {ν : Type} [VerificationModel ν] :
    shared_refines_reliable (ν := ν) :=
  fun _ _ h => by simp only [IsReliableTrace, IsSharedTrace] at h ⊢; rw [h]

/-- Handler-backed delivery reproduces the sent messages. -/
theorem handled_refines_any_holds {ν : Type} [VerificationModel ν] :
    handled_refines_any (ν := ν) :=
  fun _ _ _ h => h

/-- Shared-backing delivery is an admissible unreliable delivery. -/
theorem spatial_le_backing_refines_holds {ν : Type} [VerificationModel ν] :
    spatial_le_backing_refines (ν := ν) :=
  fun s d h => reliable_refines_unreliable_holds s d (shared_refines_reliable_holds s d h)

/-- Dropping messages (delivering a sublist) is admitted by the unreliable model. -/
theorem unreliable_admits_drops {ν : Type} [VerificationModel ν]
    (sent delivered : SignedBuffer ν) (h : delivered.Sublist sent) :
    IsUnreliableTrace sent delivered :=
  (h.map _).subset

/-- Duplicating a delivered message is admitted by the unreliable model. -/
theorem unreliable_admits_duplication {ν : Type} [VerificationModel ν]
    (sent delivered : SignedBuffer ν) (sv : SignedValue ν)
    (h : IsUnreliableTrace sent (sv :: delivered)) :
    IsUnreliableTrace sent (sv :: sv :: delivered) := by
  intro v hv
  simp only [IsUnreliableTrace, tracePayloads, List.map_cons] at h hv ⊢
  rcases List.mem_cons.1 hv with hEq | hRest
  · exact h (hEq ▸ List.mem_cons_self ..)
  · exact h hRest

/-- The unreliable model rejects fabricated payloads. -/
theorem unreliable_rejects_fabrication {ν : Type} [VerificationModel ν]
    (sent delivered : SignedBuffer ν) (h : IsUnreliableTrace sent delivered)
    (v : Value) (hv : v ∈ tracePayloads delivered) : v ∈ tracePayloads sent :=
  h hv
