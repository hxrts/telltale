import Std


/-! # Violations and Policy

`Violation` and `ViolationPolicy`, spec-level types for safety and liveness
violations. A `Violation` is either a safety violation (should never occur in
well-typed runs) or a liveness violation (progress failure). The `ViolationPolicy`
in `VMConfig` decides whether to allow or reject each violation, letting the
deployment choose between strict abort-on-violation and lenient logging modes.

Referenced by both `Config.lean` (stores the policy) and the adequacy layer
(uses violations in correctness statements).
-/

set_option autoImplicit false

/-! ## Violations and policy -/

inductive Violation where
  -- Safety violations should never happen in well-typed runs.
  | safety (msg : String)
  -- Liveness violations indicate progress failure.
  | liveness (msg : String)
  deriving Repr

structure ViolationPolicy where
  -- Decide whether to allow or reject a violation.
  allow : Violation → Bool
