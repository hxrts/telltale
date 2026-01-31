import Std

/-
The Problem. Scheduler policy should be part of the runtime spec so it can
be referenced by VM configuration without importing proof-heavy modules.

Solution Structure. Define a small policy enum that later scheduler code can
interpret without changing the VM-facing interface.
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
