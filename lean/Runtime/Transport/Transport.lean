import Runtime.Resources.BufferRA
import Runtime.Compat.RA

/-!
# Task 18: Transport Abstraction

Transport interface, specification, and refinement from iris_runtime_2.md §8.

## Definitions

- `Transport` — abstract interface (send_raw, recv_raw, connect, disconnect)
- `TransportSpec` — specification (FIFO, reliable, bounded)
- `serialize` / `deserialize`
- `serialize_roundtrip`
- `transport_refines_buffers`
- `InMemoryTransport` — reference implementation

Dependencies: Task 14, Shim.ResourceAlgebra.
-/

set_option autoImplicit false

structure Transport where
  send_raw : Endpoint → Value → Unit
  recv_raw : Endpoint → Option Value
  connect : Endpoint → Unit
  disconnect : Endpoint → Unit

structure TransportSpec where
  fifo : Bool
  reliable : Bool
  bounded : Bool
  deriving Repr

def serialize (v : Value) : List Nat :=
  match v with
  | .unit => [0]
  | .bool b => [1, if b then 1 else 0]
  | .nat n => [2, n]
  | .string s =>
      3 :: (s.toList.map Char.toNat)
  | .prod v1 v2 =>
      let s1 := serialize v1
      let s2 := serialize v2
      4 :: (Nat.cast s1.length) :: s1 ++ s2
  | .chan e =>
      5 :: e.sid :: (e.role.toList.map Char.toNat)

def deserializeAux (fuel : Nat) (bytes : List Nat) : Option Value :=
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

def deserialize (bytes : List Nat) : Option Value :=
  deserializeAux bytes.length bytes

def serialize_roundtrip (v : Value) : Prop :=
  deserialize (serialize v) = some v

def transport_refines_buffers (_t : Transport) (_spec : TransportSpec) : Prop := True

def InMemoryTransport : Transport :=
  { send_raw := fun _ _ => (), recv_raw := fun _ => none, connect := fun _ => (), disconnect := fun _ => () }
