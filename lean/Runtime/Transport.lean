import Std
import Runtime.Resources.BufferRA

/-
The Problem. The runtime needs a transport abstraction that can be backed
by buffers or by effect handlers, while providing FIFO/no-dup/no-create
specifications for session typing.

Solution Structure. Define transport results and specs, add a simple
serialization format with roundtrip property, and expose refinement
stubs for handler-backed transports.
-/

/-!
# Transport Abstraction

Transport interface, specification, and refinement from iris_runtime_2.md §8.

## Definitions

- `Transport` — abstract interface (send/recv/connected)
- `TransportSpec` — specification (FIFO, no-dup, no-create)
- `serialize` / `deserialize`
- `serialize_roundtrip`
- `transport_refines_buffers`
- `InMemoryTransport` — reference implementation
-/

set_option autoImplicit false

universe u

/-! ## Transport interface -/

inductive TransportResult (ν : Type u) [VerificationModel ν] where
  -- Transport outcomes for send/recv.
  | ok (v : SignedValue ν)
  | blocked
  | disconnected
  | timeout
  | error (msg : String)

structure Transport (ν : Type u) [VerificationModel ν] where
  -- Abstract send/recv over directed edges.
  send : Edge → SignedValue ν → TransportResult ν
  recv : Edge → TransportResult ν
  connected : Edge → Bool

/-! ## Transport specification -/

inductive TransportEvent (ν : Type u) [VerificationModel ν] where
  -- Transport events distinguish sends from receives.
  | sent (edge : Edge) (val : SignedValue ν)
  | received (edge : Edge) (val : SignedValue ν)

abbrev TransportTrace (ν : Type u) [VerificationModel ν] :=
  -- Trace of transport events (signed payloads).
  List (TransportEvent ν)

private def listGet? {α : Type} : List α → Nat → Option α
  -- Total list lookup by index.
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

def EventAt {ν : Type u} [VerificationModel ν]
    (trace : TransportTrace ν) (idx : Nat) (ev : TransportEvent ν) : Prop :=
  -- Locate an event at a given index in the trace.
  listGet? trace idx = some ev

def SendBefore {ν : Type u} [VerificationModel ν]
    (trace : TransportTrace ν) (e : Edge) (v1 v2 : Value) : Prop :=
  -- Send ordering: v1 is sent before v2 on edge e.
  ∃ i j sv1 sv2, i < j ∧
    EventAt trace i (.sent e sv1) ∧ sv1.payload = v1 ∧
    EventAt trace j (.sent e sv2) ∧ sv2.payload = v2

def RecvBefore {ν : Type u} [VerificationModel ν]
    (trace : TransportTrace ν) (e : Edge) (v1 v2 : Value) : Prop :=
  -- Receive ordering: v1 is received before v2 on edge e.
  ∃ i j sv1 sv2, i < j ∧
    EventAt trace i (.received e sv1) ∧ sv1.payload = v1 ∧
    EventAt trace j (.received e sv2) ∧ sv2.payload = v2

def countSent {ν : Type u} [VerificationModel ν]
    (trace : TransportTrace ν) (e : Edge) (v : Value) : Nat :=
  -- Count how many times payload v was sent on edge e.
  trace.foldl
    (fun acc ev =>
      match ev with
      | .sent e' sv =>
          if decide (e' = e ∧ sv.payload = v) then acc + 1 else acc
      | .received _ _ => acc)
    0

def countRecv {ν : Type u} [VerificationModel ν]
    (trace : TransportTrace ν) (e : Edge) (v : Value) : Nat :=
  -- Count how many times payload v was received on edge e.
  trace.foldl
    (fun acc ev =>
      match ev with
      | .received e' sv =>
          if decide (e' = e ∧ sv.payload = v) then acc + 1 else acc
      | .sent _ _ => acc)
    0

def SendCount {ν : Type u} [VerificationModel ν]
    (trace : TransportTrace ν) (e : Edge) (v : Value) : Nat :=
  -- Send multiplicity for payload v.
  countSent trace e v

def RecvCount {ν : Type u} [VerificationModel ν]
    (trace : TransportTrace ν) (e : Edge) (v : Value) : Nat :=
  -- Receive multiplicity for payload v.
  countRecv trace e v

structure TransportSpec (ν : Type u) [VerificationModel ν] where
  -- FIFO and reliability requirements for a transport trace.
  fifo : TransportTrace ν → Prop
  noDup : TransportTrace ν → Prop
  noCreate : TransportTrace ν → Prop

def TransportSpec.default {ν : Type u} [VerificationModel ν] : TransportSpec ν :=
  -- Standard FIFO/no-dup/no-create spec derived from the trace order.
  { fifo := fun trace =>
      ∀ e v1 v2, SendBefore trace e v1 v2 → RecvBefore trace e v1 v2
  , noDup := fun trace =>
      ∀ e v, SendCount trace e v = RecvCount trace e v
  , noCreate := fun trace =>
      ∀ e v, RecvCount trace e v ≤ SendCount trace e v }

def traceOfBuffers {ν : Type u} [VerificationModel ν]
    (bufs : SignedBuffers ν) : TransportTrace ν :=
  -- Interpret each buffer entry as a send event.
  bufs.flatMap (fun p => p.snd.map (fun sv => TransportEvent.sent p.fst sv))

def handlerEdges (handlers : List (Edge × HandlerId)) (handler : HandlerId) : List Edge :=
  -- Collect edges bound to a specific handler.
  handlers.foldl
    (fun acc p => if decide (p.snd = handler) then acc ++ [p.fst] else acc)
    []

def handlerTraceOf {ν : Type u} [VerificationModel ν]
    (handler : HandlerId) (handlers : List (Edge × HandlerId))
    (bufs : SignedBuffers ν) : TransportTrace ν :=
  -- Handler-backed traces are derived from the handler's bound edges.
  let edges := handlerEdges handlers handler
  let bufs' := bufs.filter (fun p => edges.contains p.fst)
  traceOfBuffers bufs'

def IsHandlerTrace {ν : Type u} [VerificationModel ν]
    (handler : HandlerId) (handlers : List (Edge × HandlerId))
    (trace : TransportTrace ν) : Prop :=
  -- Handler traces are those induced by the handler's bound edges.
  ∃ bufs, trace = handlerTraceOf (ν:=ν) handler handlers bufs

def SpecSatisfied {ν : Type u} [VerificationModel ν]
    (spec : TransportSpec ν) (trace : TransportTrace ν) : Prop :=
  -- The trace satisfies the specification predicates.
  spec.fifo trace ∧ spec.noDup trace ∧ spec.noCreate trace

class HandlerSatisfiesTransportSpec (ν : Type u) [VerificationModel ν]
    (handler : HandlerId) where
  -- Handler-level proof of the transport spec.
  spec : TransportSpec ν
  proof : ∀ handlers trace, IsHandlerTrace handler handlers trace → SpecSatisfied spec trace

/-! ## Serialization -/

def serializeNat (v : Value) : List Nat :=
  -- Encode values into a simple tagged list of naturals.
  match v with
  | .unit => [0]
  | .bool b => [1, if b then 1 else 0]
  | .nat n => [2, n]
  | .string s => 3 :: (s.toList.map Char.toNat)
  | .prod v1 v2 =>
      let s1 := serializeNat v1
      let s2 := serializeNat v2
      4 :: s1.length :: s1 ++ s2
  | .chan e => 5 :: e.sid :: (e.role.toList.map Char.toNat)

def serialize (v : Value) : ByteArray :=
  -- Serialize into a byte array via UInt8 tags.
  let bytes := (serializeNat v).map UInt8.ofNat
  ByteArray.mk bytes.toArray

def deserializeAux (fuel : Nat) (bytes : List Nat) : Option Value :=
  -- Fuel-bounded decoder for tagged values.
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match bytes with
      | [] => none
      | 0 :: _ => some .unit
      | 1 :: b :: _ => some (.bool (b == 1))
      | 2 :: n :: _ => some (.nat n)
      | 3 :: rest =>
          let chars := rest.map Char.ofNat
          some (.string (String.ofList chars))
      | 4 :: n :: rest =>
          let s1 := rest.take n
          let s2 := rest.drop n
          match deserializeAux fuel s1, deserializeAux fuel s2 with
          | some v1, some v2 => some (.prod v1 v2)
          | _, _ => none
      | 5 :: sid :: rest =>
          let chars := rest.map Char.ofNat
          some (.chan { sid := sid, role := String.ofList chars })
      | _ => none

def deserialize (bytes : ByteArray) : Option Value :=
  -- Decode from a byte array using bounded recursion.
  let ns := bytes.data.toList.map UInt8.toNat
  deserializeAux ns.length ns

def serialize_roundtrip (v : Value) : Prop :=
  -- Roundtrip property for serialization.
  deserialize (serialize v) = some v

def transport_refines_buffers {ν : Type u} [VerificationModel ν]
    (_t : Transport ν) (spec : TransportSpec ν) (bufs : SignedBuffers ν) : Prop :=
  -- Transport traces satisfy their declared specification.
  SpecSatisfied spec (traceOfBuffers bufs)

def InMemoryTransport {ν : Type u} [VerificationModel ν] : Transport ν :=
  -- Simple in-memory transport stub.
  { send := fun _ _ => .blocked
  , recv := fun _ => .blocked
  , connected := fun _ => true }
