import Runtime.VM.Definition
import Runtime.Invariants.SessionInv
import Runtime.Shim.Invariants
import Runtime.Shim.WeakestPre

/-!
# Task 21: Code Loading and Hot-Swap

Dynamic code loading and safe protocol update from iris_runtime_2.md §10.

## Definitions

- `loadTrusted` / `loadUntrusted`
- `SafeUpdate` — view shift for protocol replacement
- `hotSwap_preserves_coherent`
- `code_signature_check`

Dependencies: Task 11, Task 16, Shim.Invariants + Shim.WeakestPre.
-/

set_option autoImplicit false

-- TODO: implement Task 21
