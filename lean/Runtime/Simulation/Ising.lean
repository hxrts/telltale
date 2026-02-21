import Runtime.Simulation.Core

set_option autoImplicit false

namespace Runtime.Simulation

structure MeanFieldParams where
  beta : Scalar
  stepSize : Scalar

/-- One mean-field Ising Euler step over `[x_up, x_down]`. -/
def isingStep (params : MeanFieldParams) (state : List Scalar) : Except String (List Scalar) := do
  match state with
  | [up, down] =>
      let m := up - down
      let drift := tanhApprox (params.beta * m) - m
      let up' := up + drift * params.stepSize
      let down' := down - drift * params.stepSize
      let upClamped := clamp up' 0 1
      let downClamped := clamp down' 0 1
      let sum := upClamped + downClamped
      if sum = 0 then
        pure [upClamped, downClamped]
      else
        pure [upClamped / sum, downClamped / sum]
  | _ =>
      throw "mean-field Ising expects exactly 2 state entries"

end Runtime.Simulation
