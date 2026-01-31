import Std

/-
The Problem. The runtime needs a spec-level notion of violations and a
policy hook for how they are handled (log, drop, abort).

Solution Structure. Provide minimal data types for violations and policies
so both the VM config and adequacy layer can reference them.
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
