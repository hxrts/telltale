import Runtime.Proofs.Search.Core
import Runtime.Proofs.Search.Executable
import Runtime.Proofs.Search.FullMachine
import Runtime.Proofs.Search.Problem
import Runtime.Proofs.Search.Liveness

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.SelectedResults

Generic selected-result and observable vocabulary layered over the historical
incumbent/path field names used by the original proof lane.

This module does not replace the legacy definitions. It provides a generic
selected-result view so the proof API can talk about result identity,
result cost, and optional witness/path refinements without making path search
the only machine shape.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Generic reduced selected-result view of one reduced state slice. -/
def StateSlice.selectedResult (slice : StateSlice) : Option NormalizedCommit :=
  slice.incumbent

/-- Generic reduced selected-result cost observable. -/
def ObservationSlice.selectedResultCost (obs : ObservationSlice) : Option Nat :=
  obs.incumbentCost

/-- Generic reduced selected-result identity observable. -/
def ObservationSlice.selectedResultIdentity (obs : ObservationSlice) : Option Nat :=
  obs.incumbentNode

/-- Generic selected-result cost observable on the reduced exported artifact. -/
def StateArtifactSchema.selectedResultCost (artifact : StateArtifactSchema) : Option Nat :=
  artifact.incumbentCost

/-- Generic selected-result witness observable on the reduced exported artifact.
For the built-in path-search specialization, the witness is a singleton-node
path at the reduced boundary. -/
def StateArtifactSchema.selectedResultWitness
    (artifact : StateArtifactSchema) : Option (List Nat) :=
  artifact.incumbentNodePath

/-- Generic selected-result cost observable on the full exported artifact. -/
def FullStateArtifactSchema.selectedResultCost
    (artifact : FullStateArtifactSchema) : Option Nat :=
  artifact.incumbentCost

/-- Generic selected-result witness observable on the full exported artifact. -/
def FullStateArtifactSchema.selectedResultWitness
    (artifact : FullStateArtifactSchema) : Option (List Nat) :=
  artifact.incumbentPath

/-- Generic selected-result publication trace observable on the full exported
artifact. -/
def FullStateArtifactSchema.selectedResultPublicationTrace
    (artifact : FullStateArtifactSchema) : List NormalizedCommit :=
  artifact.incumbentPublicationTrace

/-- Generic reduced selected-result coherence alias. -/
abbrev ReducedSelectedResultInvariant
    (problem : SearchProblem)
    (state : SearchMachineState) : Prop :=
  ReducedSelectedResultCoherent problem state

/-- Generic full-machine selected-result coherence alias. -/
abbrev FullSelectedResultInvariant
    (problem : FullSearchProblem)
    (state : FullSearchMachineState) : Prop :=
  FullSelectedResultCoherent problem state

/-- One generic reduced selected-result observation slice. -/
structure SelectedResultObservationSlice where
  selectedResultCost : Option Nat
  selectedResultIdentity : Option Nat
  normalizedCommits : List NormalizedCommit
  productiveSteps : Nat
  totalSchedulerSteps : Nat
  deriving DecidableEq, Repr

/-- Generic reduced selected-result observation derived from one step artifact. -/
def selectedResultObservationSliceOfStepArtifact
    (artifact : StepArtifact) : SelectedResultObservationSlice :=
  { selectedResultCost := (observationSliceOfStepArtifact artifact).selectedResultCost
  , selectedResultIdentity := (observationSliceOfStepArtifact artifact).selectedResultIdentity
  , normalizedCommits := (observationSliceOfStepArtifact artifact).normalizedCommits
  , productiveSteps := (observationSliceOfStepArtifact artifact).productiveSteps
  , totalSchedulerSteps := (observationSliceOfStepArtifact artifact).totalSchedulerSteps
  }

/-- The generic selected-result observation view is definitionally equal to the
legacy reduced observation fields. -/
theorem selected_result_observation_slice_of_step_artifact_refines_legacy
    (artifact : StepArtifact) :
    selectedResultObservationSliceOfStepArtifact artifact =
      { selectedResultCost := (observationSliceOfStepArtifact artifact).incumbentCost
      , selectedResultIdentity := (observationSliceOfStepArtifact artifact).incumbentNode
      , normalizedCommits := (observationSliceOfStepArtifact artifact).normalizedCommits
      , productiveSteps := (observationSliceOfStepArtifact artifact).productiveSteps
      , totalSchedulerSteps := (observationSliceOfStepArtifact artifact).totalSchedulerSteps
      } :=
  rfl

/-- Release-facing generic selected-result theorem row stating that the
selected-result observation slice is definitionally the legacy reduced
observation payload under the current executable artifact boundary. -/
theorem search_selected_result_observation_slice_refines_legacy_fields
    (artifact : StepArtifact) :
    selectedResultObservationSliceOfStepArtifact artifact =
      { selectedResultCost := (observationSliceOfStepArtifact artifact).incumbentCost
      , selectedResultIdentity := (observationSliceOfStepArtifact artifact).incumbentNode
      , normalizedCommits := (observationSliceOfStepArtifact artifact).normalizedCommits
      , productiveSteps := (observationSliceOfStepArtifact artifact).productiveSteps
      , totalSchedulerSteps := (observationSliceOfStepArtifact artifact).totalSchedulerSteps
      } :=
  selected_result_observation_slice_of_step_artifact_refines_legacy artifact

/-- Generic machine-level notion that some selected result is published,
independent of any one distinguished goal node. -/
def SelectedResultPublished (state : SearchMachineState) : Prop :=
  ∃ commit, state.incumbent = some commit

/-- Goal publication is one specialization of generic selected-result
publication. -/
theorem goal_publication_specializes_selected_result_publication
    {goal : Nat} {state : SearchMachineState}
    (hGoal : GoalIncumbentPublished goal state) :
    SelectedResultPublished state := by
  rcases hGoal with ⟨commit, hInc, _hGoal⟩
  exact ⟨commit, hInc⟩

end Search
end Proofs
end Runtime
