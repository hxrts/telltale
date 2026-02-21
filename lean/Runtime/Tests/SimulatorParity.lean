import Runtime.Simulation

set_option autoImplicit false

open Runtime.Simulation

private def expect (ok : Bool) (msg : String) : IO Unit :=
  if ok then pure () else throw (IO.userError msg)

private def listApproxEq (eps : Scalar) (xs ys : List Scalar) : Bool :=
  xs.length == ys.length &&
    (List.zip xs ys).all (fun p => approxEq eps p.1 p.2)

private def unwrapResult (r : Except String (List Scalar)) : IO (List Scalar) :=
  match r with
  | .ok vals => pure vals
  | .error err => throw (IO.userError err)

private def eps : Scalar :=
  (1 : Scalar) / 1_000_000

/-- Executable parity fixtures mirroring Rust material-handler parity tests. -/
def main : IO Unit := do
  let isingEqParams : MeanFieldParams :=
    { beta := (3 : Scalar) / 2, stepSize := (1 : Scalar) / 100 }
  let isingEqOut ← unwrapResult (isingStep isingEqParams [1 / 2, 1 / 2])
  expect (listApproxEq eps isingEqOut [1 / 2, 1 / 2])
    "ising equilibrium fixture mismatch"

  let isingZeroBeta : MeanFieldParams :=
    { beta := 0, stepSize := (1 : Scalar) / 10 }
  let isingZeroOut ← unwrapResult (isingStep isingZeroBeta [3 / 5, 2 / 5])
  expect (listApproxEq eps isingZeroOut [29 / 50, 21 / 50])
    "ising zero-beta drift fixture mismatch"

  let hamParams : HamiltonianParams :=
    { springConstant := 1, mass := 1, stepSize := (1 : Scalar) / 100 }
  let hamPhase0 ← unwrapResult (hamiltonianStep hamParams 0 (-1) [1, 0])
  expect (decide (hamPhase0 = [1, 0]))
    "hamiltonian phase-gate fixture mismatch"

  let hamPhase3 ← unwrapResult (hamiltonianStep hamParams 3 (-1) [1, 0])
  expect (listApproxEq eps hamPhase3 [9999 / 10000, (-39999 : Scalar) / 2_000_000])
    "hamiltonian leapfrog fixture mismatch"

  let continuumParams : ContinuumFieldParams :=
    { coupling := 1, stepSize := (1 : Scalar) / 10 }
  let contPhase0 ← unwrapResult (continuumStep continuumParams 0 0 [1])
  expect (decide (contPhase0 = [1]))
    "continuum phase-gate fixture mismatch"

  let contPhase1 ← unwrapResult (continuumStep continuumParams 1 0 [1])
  expect (listApproxEq eps contPhase1 [9 / 10])
    "continuum diffusion fixture mismatch"
