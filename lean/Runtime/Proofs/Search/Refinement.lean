import Runtime.Proofs.Search.Fairness

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Refinement

Reduced refinement theorems for exact single-lane threaded search.

These theorems strengthen the fairness story by proving equality of the reduced
step artifact, not just equality of the post-step frontier.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Reduced canonical state-slice trace for one frontier trace. -/
def canonicalStateSliceTrace (trace : FrontierTrace) : Nat → StateSlice :=
  fun i => stateSliceOfStepArtifact (canonicalStepArtifact (trace i))

/-- Reduced threaded exact single-lane state-slice trace for one frontier trace. -/
def threadedStateSliceTrace (trace : FrontierTrace) : Nat → StateSlice :=
  fun i => stateSliceOfStepArtifact (threadedExactSingleLaneStepArtifact (trace i))

/-- Reduced canonical observation-slice trace for one frontier trace. -/
def canonicalObservationSliceTrace (trace : FrontierTrace) : Nat → ObservationSlice :=
  fun i => observationSliceOfStepArtifact (canonicalStepArtifact (trace i))

/-- Reduced threaded exact single-lane observation-slice trace for one frontier trace. -/
def threadedObservationSliceTrace (trace : FrontierTrace) : Nat → ObservationSlice :=
  fun i => observationSliceOfStepArtifact (threadedExactSingleLaneStepArtifact (trace i))

/-- Exported state-artifact trace for canonical serial search. -/
def canonicalStateArtifactTrace (trace : FrontierTrace) : Nat → StateArtifactSchema :=
  fun i => stateArtifactOfStateSlice (canonicalStateSliceTrace trace i)

/-- Exported state-artifact trace for exact threaded single-lane search. -/
def threadedStateArtifactTrace (trace : FrontierTrace) : Nat → StateArtifactSchema :=
  fun i => stateArtifactOfStateSlice (threadedStateSliceTrace trace i)

/-- The reduced threaded exact single-lane step artifact refines the reduced
canonical serial step artifact exactly. -/
theorem threaded_exact_single_lane_step_artifact_refines_canonical
    (frontier : List FrontierEntry) :
    threadedExactSingleLaneStepArtifact frontier =
      canonicalStepArtifact frontier :=
  rfl

/-- In particular, the reduced normalized commit trace for one exact threaded
single-lane step is exactly the canonical serial commit trace. -/
theorem threaded_exact_single_lane_commit_trace_refines_canonical
    (frontier : List FrontierEntry) :
    (threadedExactSingleLaneStepArtifact frontier).normalizedCommits =
      (canonicalStepArtifact frontier).normalizedCommits :=
  rfl

/-- The reduced exact threaded step services the same batch-node set as the
canonical serial step. -/
theorem threaded_exact_single_lane_batch_nodes_refine_canonical
    (frontier : List FrontierEntry) :
    (threadedExactSingleLaneStepArtifact frontier).batchNodes =
      (canonicalStepArtifact frontier).batchNodes :=
  rfl

/-- The reduced authoritative state slice for one exact threaded single-lane
step matches the canonical serial state slice exactly. -/
theorem threaded_exact_single_lane_state_slice_refines_canonical
    (frontier : List FrontierEntry) :
    stateSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier) =
      stateSliceOfStepArtifact (canonicalStepArtifact frontier) :=
  rfl

/-- The reduced observable slice for one exact threaded single-lane step matches
the canonical serial observable slice exactly. -/
theorem threaded_exact_single_lane_observation_slice_refines_canonical
    (frontier : List FrontierEntry) :
    observationSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier) =
      observationSliceOfStepArtifact (canonicalStepArtifact frontier) :=
  rfl

/-- Exact normalized commit-trace refinement is enough to recover equality of
the reduced observable slice at the claimed search boundary. -/
theorem threaded_exact_single_lane_commit_trace_refinement_implies_observation_equivalence
    (frontier : List FrontierEntry) :
    observationSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier) =
      observationSliceOfStepArtifact (canonicalStepArtifact frontier) :=
  threaded_exact_single_lane_observation_slice_refines_canonical frontier

/-- The exported reduced state-artifact schema for one exact threaded
single-lane step matches the canonical serial artifact exactly. -/
theorem threaded_exact_single_lane_state_artifact_refines_canonical
    (frontier : List FrontierEntry) :
    stateArtifactOfStateSlice (stateSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier)) =
      stateArtifactOfStateSlice (stateSliceOfStepArtifact (canonicalStepArtifact frontier)) :=
  rfl

/-- Multi-step state-slice refinement for exact threaded single-lane search over
an arbitrary frontier trace. -/
theorem threaded_exact_single_lane_multi_step_state_trace_refines_canonical
    (trace : FrontierTrace) :
    threadedStateSliceTrace trace = canonicalStateSliceTrace trace :=
  rfl

/-- Multi-step observation-slice refinement for exact threaded single-lane
search over an arbitrary frontier trace. -/
theorem threaded_exact_single_lane_multi_step_observation_trace_refines_canonical
    (trace : FrontierTrace) :
    threadedObservationSliceTrace trace = canonicalObservationSliceTrace trace :=
  rfl

/-- Multi-step exported state-artifact refinement for exact threaded single-lane
search over an arbitrary frontier trace. -/
theorem threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical
    (trace : FrontierTrace) :
    threadedStateArtifactTrace trace = canonicalStateArtifactTrace trace :=
  rfl

end Search
end Proofs
end Runtime
