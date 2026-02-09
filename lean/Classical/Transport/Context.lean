import Mathlib

set_option autoImplicit false

/-! # Classical.Transport.Context

Core transport context shared by transported theorem families.
-/

namespace Classical
namespace Transport

universe u

/-- Core transport context shared by all theorem families. -/
structure TransportCtx (State : Type u) where
  step : State → State
  coherent : State → Prop
  harmony : Prop
  finiteState : Prop

/-- Naming-normalized alias: shared assumptions required by transported
classical theorem families. -/
abbrev TransportAssumptions (State : Type u) := TransportCtx State

end Transport
end Classical
