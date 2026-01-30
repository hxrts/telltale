import Runtime.VM.LanguageInstance
import Runtime.Invariants.SessionInv
import Runtime.Shim.Invariants
import Runtime.Shim.WeakestPre

/-!
# Task 19: Session WP Rules

Weakest precondition rules for each bytecode instruction from iris_runtime_2.md §7.

## Rules

- `wp_send`, `wp_recv`, `wp_offer`, `wp_choose`
- `wp_open`, `wp_close`
- `wp_acquire`, `wp_release`
- `wp_invoke`, `wp_fork`, `wp_join`, `wp_abort`
- `wp_transfer`, `wp_tag`, `wp_check`
- `wp_loadImm`, `wp_mov`, `wp_jmp`, `wp_spawn`, `wp_yield`, `wp_halt`

Dependencies: Task 12, Task 16, Shim.Invariants + Shim.WeakestPre.
-/

set_option autoImplicit false

-- TODO: implement Task 19
