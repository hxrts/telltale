import Runtime.VM.TypeClasses
import Runtime.Compat.RA

/-!
# Task 15: Arena and Session Store

Physical backing model for session state from iris_runtime_2.md §5.3–5.5.

## Definitions

- `Arena` — contiguous memory region with typed slots
- `ArenaSlot` — tagged union of value types
- `SessionState` — per-session metadata
- `SessionStore` — map from SessionId to SessionState
- `SessionPhase` — opening, active, closing, closed
- `sessionStore_refines_envs`
- `arena_lookup_typed`

Dependencies: Task 10, Shim.ResourceAlgebra.
-/

set_option autoImplicit false

inductive SessionPhase where
  | opening
  | active
  | closing
  | closed
  deriving Repr

structure ArenaSlot where
  ty : ValType
  val : Value
  deriving Repr

structure Arena where
  slots : List ArenaSlot
  deriving Repr

structure SessionState where
  endpoints : List Endpoint
  localTypes : List (Endpoint × LocalType)
  buffers : List (Edge × List Value)
  phase : SessionPhase
  deriving Repr

abbrev SessionStore := List (SessionId × SessionState)

def sessionStore_refines_envs (_store : SessionStore) : Prop :=
  True

def arena_lookup_typed (_arena : Arena) (_idx : Nat) : Prop :=
  True
