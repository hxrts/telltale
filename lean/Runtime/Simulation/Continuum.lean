import Runtime.Simulation.Core

set_option autoImplicit false

namespace Runtime.Simulation

structure ContinuumFieldParams where
  coupling : Scalar
  stepSize : Scalar

/-- One continuum-field step over `[field]`, gated to the receive-complete phase. -/
def continuumStep
    (params : ContinuumFieldParams)
    (phase : Nat)
    (peerField : Scalar)
    (state : List Scalar) : Except String (List Scalar) := do
  match state with
  | [field] =>
      if phase % 2 != 1 then
        pure [field]
      else
        let drift := params.coupling * (peerField - field)
        pure [field + drift * params.stepSize]
  | _ =>
      throw "continuum field expects exactly 1 state entry"

end Runtime.Simulation
