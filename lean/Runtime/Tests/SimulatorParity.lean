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

private def unwrapStates (r : Except String InitialStates) : IO InitialStates :=
  match r with
  | .ok vals => pure vals
  | .error err => throw (IO.userError err)

private def lookupState (states : InitialStates) (role : String) : IO (List Scalar) :=
  match states.lookup role with
  | some vals => pure vals
  | none => throw (IO.userError s!"missing state for role {role}")

private def eps : Scalar :=
  (1 : Scalar) / 1_000_000

/-- Executable parity fixtures mirroring Rust material-handler parity tests. -/
def main : IO Unit := do
  let meanFieldCatalog : MaterialParams :=
    .meanField
      { beta := (3 : Scalar) / 2
      , species := ["up", "down"]
      , initialState := [1 / 2, 1 / 2]
      , stepSize := (1 : Scalar) / 100
      }
  let isingEqOut ← unwrapResult <|
    (handlerFromMaterial meanFieldCatalog).step {} [1 / 2, 1 / 2]
  expect (listApproxEq eps isingEqOut [1 / 2, 1 / 2])
    "ising equilibrium fixture mismatch"

  let isingZeroBeta : MaterialParams :=
    .meanField
      { beta := 0
      , species := ["up", "down"]
      , initialState := [3 / 5, 2 / 5]
      , stepSize := (1 : Scalar) / 10
      }
  let isingZeroOut ← unwrapResult <|
    (handlerFromMaterial isingZeroBeta).step {} [3 / 5, 2 / 5]
  expect (listApproxEq eps isingZeroOut [29 / 50, 21 / 50])
    "ising zero-beta drift fixture mismatch"

  let hamCatalog : MaterialParams :=
    .hamiltonian
      { springConstant := 1
      , mass := 1
      , dimensions := 1
      , initialPositions := [1, -1]
      , initialMomenta := [0, 0]
      , stepSize := (1 : Scalar) / 100
      }
  let hamHandler := handlerFromMaterial hamCatalog
  let hamPhase0 ← unwrapResult <|
    hamHandler.step { phase := 0, peerState := [-1] } [1, 0]
  expect (decide (hamPhase0 = [1, 0]))
    "hamiltonian phase-gate fixture mismatch"

  let hamPhase3 ← unwrapResult <|
    hamHandler.step { phase := 3, peerState := [-1] } [1, 0]
  expect (listApproxEq eps hamPhase3 [9999 / 10000, (-39999 : Scalar) / 2_000_000])
    "hamiltonian leapfrog fixture mismatch"

  let continuumCatalog : MaterialParams :=
    .continuumField
      { coupling := 1
      , components := 1
      , initialFields := [1, 0]
      , stepSize := (1 : Scalar) / 10
      }
  let continuumHandler := handlerFromMaterial continuumCatalog
  let contPhase0 ← unwrapResult <|
    continuumHandler.step { phase := 0, peerState := [0] } [1]
  expect (decide (contPhase0 = [1]))
    "continuum phase-gate fixture mismatch"

  let contPhase1 ← unwrapResult <|
    continuumHandler.step { phase := 1, peerState := [0] } [1]
  expect (listApproxEq eps contPhase1 [9 / 10])
    "continuum diffusion fixture mismatch"

  expect (meanFieldCatalog.layerName = "mean_field")
    "mean-field layer name mismatch"
  expect (hamCatalog.layerName = "hamiltonian")
    "hamiltonian layer name mismatch"
  expect (continuumCatalog.layerName = "continuum_field")
    "continuum layer name mismatch"

  let derivedStates ← unwrapStates <|
    deriveInitialStatesFromMaterial hamCatalog ["A", "B"]
  let stateA ← lookupState derivedStates "A"
  let stateB ← lookupState derivedStates "B"
  expect (decide (stateA = [1, 0]))
    "hamiltonian initial state for A mismatch"
  expect (decide (stateB = [-1, 0]))
    "hamiltonian initial state for B mismatch"
