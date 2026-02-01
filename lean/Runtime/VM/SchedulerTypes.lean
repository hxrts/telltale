import Std

/-!
# Scheduler Policy Types

`SchedPolicy`, the scheduling strategy enum referenced by `VMConfig`. Defined in
its own file to avoid circular imports: `Config.lean` needs the policy type, but the
full scheduler implementation (`Runtime/Scheduler/Scheduler.lean`) needs the config.

The `progressAware` policy is the session-type-aware variant that prefers coroutines
holding progress tokens, connecting to the liveness reasoning in `runtime.md` §18.
-/

set_option autoImplicit false

/-! ## Scheduler policies -/

inductive SchedPolicy where
  -- Round-robin over runnable coroutines.
  | roundRobin
  -- Work stealing with a fixed number of workers.
  | workStealing (workers : Nat)
  -- Cooperative single-threaded scheduling.
  | cooperative
  -- Priority policy from coroutine id to priority.
  | priority (f : Nat → Nat)
  -- Prefer coroutines holding progress tokens (§18).
  | progressAware
