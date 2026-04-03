import Runtime.Simulation.Core
import Runtime.Simulation.Ising
import Runtime.Simulation.Hamiltonian
import Runtime.Simulation.Continuum

set_option autoImplicit false

namespace Runtime.Simulation

/-- Lean mirror of simulator role names. -/
abbrev RoleName := String

/-- Lean mirror of simulator register-backed material state. -/
abbrev StateVector := List Scalar

/-- Default initial states keyed by role. -/
abbrev InitialStates := List (RoleName × StateVector)

/-- Execution context supplied to a material handler step. -/
structure MaterialStepContext where
  role : RoleName := ""
  phase : Nat := 0
  peerState : StateVector := []

/-- Lean mirror of the simulator's material-specific step handler. -/
structure MaterialHandler where
  step : MaterialStepContext → StateVector → Except String StateVector

/-- Lean mirror of the simulator-facing material-model boundary. -/
structure MaterialModel where
  layerName : String
  buildHandler : MaterialHandler
  deriveInitialStates : List RoleName → Except String InitialStates

/-- Built-in mean-field catalog parameters mirrored from Rust. -/
structure MeanFieldMaterialParams where
  beta : Scalar
  species : List String
  initialState : List Scalar
  stepSize : Scalar

/-- Built-in Hamiltonian catalog parameters mirrored from Rust. -/
structure HamiltonianMaterialParams where
  springConstant : Scalar
  mass : Scalar
  dimensions : Nat
  initialPositions : List Scalar
  initialMomenta : List Scalar
  stepSize : Scalar

/-- Built-in continuum catalog parameters mirrored from Rust. -/
structure ContinuumFieldMaterialParams where
  coupling : Scalar
  components : Nat
  initialFields : List Scalar
  stepSize : Scalar

/-- Built-in material catalog mirrored from Rust's serde-tagged enum. -/
inductive MaterialParams where
  | meanField (params : MeanFieldMaterialParams)
  | hamiltonian (params : HamiltonianMaterialParams)
  | continuumField (params : ContinuumFieldMaterialParams)

private def broadcastInitialStates
    (roles : List RoleName)
    (state : StateVector) : InitialStates :=
  roles.map (fun role => (role, state))

private def deriveHamiltonianStates
    (roles : List RoleName)
    (positions momenta : List Scalar) : Except String InitialStates := do
  match roles, positions, momenta with
  | [], _, _ => pure []
  | _ :: _, [], _ =>
      throw s!"hamiltonian material requires at least {roles.length} positions and momenta"
  | _ :: _, _, [] =>
      throw s!"hamiltonian material requires at least {roles.length} positions and momenta"
  | role :: roles', position :: positions', momentum :: momenta' =>
      let rest ← deriveHamiltonianStates roles' positions' momenta'
      pure ((role, [position, momentum]) :: rest)

private def deriveContinuumStates
    (roles : List RoleName)
    (fields : List Scalar) : Except String InitialStates := do
  match roles, fields with
  | [], _ => pure []
  | _ :: _, [] =>
      throw s!"continuum_field material requires at least {roles.length} initial field values"
  | role :: roles', field :: fields' =>
      let rest ← deriveContinuumStates roles' fields'
      pure ((role, [field]) :: rest)

def meanFieldModel (params : MeanFieldMaterialParams) : MaterialModel where
  layerName := "mean_field"
  buildHandler := {
    step := fun _ctx state =>
      isingStep
        { beta := params.beta, stepSize := params.stepSize }
        state
  }
  deriveInitialStates := fun roles =>
    if params.initialState.isEmpty then
      throw "mean_field material requires at least one state component"
    else
      pure (broadcastInitialStates roles params.initialState)

def hamiltonianModel (params : HamiltonianMaterialParams) : MaterialModel where
  layerName := "hamiltonian"
  buildHandler := {
    step := fun ctx state =>
      hamiltonianStep
        { springConstant := params.springConstant
        , mass := params.mass
        , stepSize := params.stepSize
        }
        ctx.phase
        (ctx.peerState.headD 0)
        state
  }
  deriveInitialStates := fun roles =>
    deriveHamiltonianStates roles params.initialPositions params.initialMomenta

def continuumFieldModel (params : ContinuumFieldMaterialParams) : MaterialModel where
  layerName := "continuum_field"
  buildHandler := {
    step := fun ctx state =>
      let peerField :=
        match state with
        | field :: _ => ctx.peerState.headD field
        | [] => ctx.peerState.headD 0
      continuumStep
        { coupling := params.coupling, stepSize := params.stepSize }
        ctx.phase
        peerField
        state
  }
  deriveInitialStates := fun roles =>
    deriveContinuumStates roles params.initialFields

def MaterialParams.toModel : MaterialParams → MaterialModel
  | .meanField params => meanFieldModel params
  | .hamiltonian params => hamiltonianModel params
  | .continuumField params => continuumFieldModel params

def MaterialParams.layerName (params : MaterialParams) : String :=
  params.toModel.layerName

def handlerFromModel (model : MaterialModel) : MaterialHandler :=
  model.buildHandler

def handlerFromMaterial (params : MaterialParams) : MaterialHandler :=
  handlerFromModel params.toModel

def deriveInitialStates
    (model : MaterialModel)
    (roles : List RoleName) : Except String InitialStates :=
  model.deriveInitialStates roles

def deriveInitialStatesFromMaterial
    (params : MaterialParams)
    (roles : List RoleName) : Except String InitialStates :=
  deriveInitialStates params.toModel roles

end Runtime.Simulation
