import Runtime.Simulation.Core
import Runtime.Simulation.Ising
import Runtime.Simulation.Hamiltonian
import Runtime.Simulation.Continuum

set_option autoImplicit false

namespace Runtime.Simulation

/-- Lean mirror of simulator role names. -/
abbrev RoleName := String

/-- Lean mirror of simulator register-backed field state. -/
abbrev StateVector := List Scalar

/-- Default initial states keyed by role. -/
abbrev InitialStates := List (RoleName × StateVector)

/-- Execution context supplied to a field handler step. -/
structure FieldStepContext where
  role : RoleName := ""
  phase : Nat := 0
  peerState : StateVector := []

/-- Lean mirror of the simulator's field-specific step handler. -/
structure FieldHandler where
  step : FieldStepContext → StateVector → Except String StateVector

/-- Lean mirror of the simulator-facing field-model boundary. -/
structure FieldModel where
  layerName : String
  buildHandler : FieldHandler
  deriveInitialStates : List RoleName → Except String InitialStates

/-- Built-in mean-field catalog parameters mirrored from Rust. -/
structure MeanFieldCatalogParams where
  beta : Scalar
  species : List String
  initialState : List Scalar
  stepSize : Scalar

/-- Built-in Hamiltonian catalog parameters mirrored from Rust. -/
structure HamiltonianCatalogParams where
  springConstant : Scalar
  mass : Scalar
  dimensions : Nat
  initialPositions : List Scalar
  initialMomenta : List Scalar
  stepSize : Scalar

/-- Built-in continuum catalog parameters mirrored from Rust. -/
structure ContinuumFieldCatalogParams where
  coupling : Scalar
  components : Nat
  initialFields : List Scalar
  stepSize : Scalar

/-- Built-in field catalog mirrored from Rust's serde-tagged enum. -/
inductive FieldParams where
  | meanField (params : MeanFieldCatalogParams)
  | hamiltonian (params : HamiltonianCatalogParams)
  | continuumField (params : ContinuumFieldCatalogParams)

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
      throw s!"hamiltonian field layer requires at least {roles.length} positions and momenta"
  | _ :: _, _, [] =>
      throw s!"hamiltonian field layer requires at least {roles.length} positions and momenta"
  | role :: roles', position :: positions', momentum :: momenta' =>
      let rest ← deriveHamiltonianStates roles' positions' momenta'
      pure ((role, [position, momentum]) :: rest)

private def deriveContinuumStates
    (roles : List RoleName)
    (fields : List Scalar) : Except String InitialStates := do
  match roles, fields with
  | [], _ => pure []
  | _ :: _, [] =>
      throw s!"continuum_field field layer requires at least {roles.length} initial field values"
  | role :: roles', field :: fields' =>
      let rest ← deriveContinuumStates roles' fields'
      pure ((role, [field]) :: rest)

def meanFieldModel (params : MeanFieldCatalogParams) : FieldModel where
  layerName := "mean_field"
  buildHandler := {
    step := fun _ctx state =>
      isingStep
        { beta := params.beta, stepSize := params.stepSize }
        state
  }
  deriveInitialStates := fun roles =>
    if params.initialState.isEmpty then
      throw "mean_field field layer requires at least one state component"
    else
      pure (broadcastInitialStates roles params.initialState)

def hamiltonianModel (params : HamiltonianCatalogParams) : FieldModel where
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

def continuumFieldModel (params : ContinuumFieldCatalogParams) : FieldModel where
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

def FieldParams.toModel : FieldParams → FieldModel
  | .meanField params => meanFieldModel params
  | .hamiltonian params => hamiltonianModel params
  | .continuumField params => continuumFieldModel params

def FieldParams.layerName (params : FieldParams) : String :=
  params.toModel.layerName

def handlerFromFieldModel (model : FieldModel) : FieldHandler :=
  model.buildHandler

def handlerFromField (params : FieldParams) : FieldHandler :=
  handlerFromFieldModel params.toModel

def deriveInitialStates
    (model : FieldModel)
    (roles : List RoleName) : Except String InitialStates :=
  model.deriveInitialStates roles

def deriveInitialStatesFromField
    (params : FieldParams)
    (roles : List RoleName) : Except String InitialStates :=
  deriveInitialStates params.toModel roles

end Runtime.Simulation
