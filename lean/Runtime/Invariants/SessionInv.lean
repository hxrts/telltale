import Runtime.Resources.SessionRA
import Runtime.Shim.Invariants
import Runtime.Shim.SavedProp

/-!
# Task 16: Session Cancelable Invariants

Per-session cancelable invariant from iris_runtime_2.md §7.

## Definitions

- `sessionNs sid` — namespace per session
- `session_inv γ sid ct` — cancelable invariant body
- `session_ns_disjoint`
- `session_inv_alloc` / `session_inv_open` / `session_inv_close`
- `Participation` — per-endpoint lifecycle token
- `LifecycleEvent` — open, join, leave, close
- `open_coherent`, `leave_preserves_coherent`, `close_empty`

Dependencies: Task 13, Shim.Invariants + Shim.SavedProp.
-/

set_option autoImplicit false

-- TODO: implement Task 16
