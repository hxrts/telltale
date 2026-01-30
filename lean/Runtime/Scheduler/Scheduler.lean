import Runtime.VM.Definition
import Runtime.Shim.WeakestPre

/-!
# Task 17: Cooperative Scheduler

Cooperative coroutine scheduler from iris_runtime_2.md §4.

## Definitions

- `SchedPolicy` — round-robin, priority, work-stealing
- `schedule` — select next runnable coroutine
- `schedStep` — scheduler + VM step composed
- `schedule_confluence` — diamond property
- `cooperative_refines_concurrent`
- `CoroutinePool` — ready/blocked/halted partition

Dependencies: Task 11, Shim.WeakestPre.
-/

set_option autoImplicit false

-- TODO: implement Task 17
