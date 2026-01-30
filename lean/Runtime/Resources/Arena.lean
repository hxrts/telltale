import Runtime.VM.TypeClasses
import Runtime.Shim.ResourceAlgebra

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

-- TODO: implement Task 15
