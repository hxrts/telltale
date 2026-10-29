import Runtime.Proofs.Search.Fairness
import Runtime.Proofs.Search.Threaded

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Refinement

Reduced refinement theorems for exact single-lane threaded search.

The threaded step is modeled in `Runtime.Proofs.Search.Threaded` as lane-partitioned
batch processing with arbitrary lane completion order followed by a deterministic
merge by batch index. These theorems prove that, for every lane width and every
completion order, the merged step artifact (and every projection of it) equals
the canonical serial step artifact.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Reduced canonical state-slice trace for one frontier trace. -/
def canonicalStateSliceTrace (trace : FrontierTrace) : Nat → StateSlice :=
  fun i => stateSliceOfStepArtifact (canonicalStepArtifact (trace i))

/-- Reduced threaded exact single-lane state-slice trace for one frontier trace. -/
def threadedStateSliceTrace (trace : FrontierTrace)
    (schedules : ∀ i, LaneSchedule (trace i)) : Nat → StateSlice :=
  fun i => stateSliceOfStepArtifact (threadedExactSingleLaneStepArtifact (trace i) (schedules i))

/-- Reduced canonical observation-slice trace for one frontier trace. -/
def canonicalObservationSliceTrace (trace : FrontierTrace) : Nat → ObservationSlice :=
  fun i => observationSliceOfStepArtifact (canonicalStepArtifact (trace i))

/-- Reduced threaded exact single-lane observation-slice trace for one frontier trace. -/
def threadedObservationSliceTrace (trace : FrontierTrace)
    (schedules : ∀ i, LaneSchedule (trace i)) : Nat → ObservationSlice :=
  fun i => observationSliceOfStepArtifact (threadedExactSingleLaneStepArtifact (trace i) (schedules i))

/-- Exported state-artifact trace for canonical serial search. -/
def canonicalStateArtifactTrace (trace : FrontierTrace) : Nat → StateArtifactSchema :=
  fun i => stateArtifactOfStateSlice (canonicalStateSliceTrace trace i)

/-- Exported state-artifact trace for exact threaded single-lane search. -/
def threadedStateArtifactTrace (trace : FrontierTrace)
    (schedules : ∀ i, LaneSchedule (trace i)) : Nat → StateArtifactSchema :=
  fun i => stateArtifactOfStateSlice (threadedStateSliceTrace trace schedules i)

/-- The reduced threaded exact single-lane step artifact refines the reduced
canonical serial step artifact exactly. -/
theorem threaded_exact_single_lane_step_artifact_refines_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    threadedExactSingleLaneStepArtifact frontier schedule =
      canonicalStepArtifact frontier :=
  threaded_step_artifact_eq_canonical frontier schedule

/-- In particular, the reduced normalized commit trace for one exact threaded
single-lane step is exactly the canonical serial commit trace. -/
theorem threaded_exact_single_lane_commit_trace_refines_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    (threadedExactSingleLaneStepArtifact frontier schedule).normalizedCommits =
      (canonicalStepArtifact frontier).normalizedCommits := by
  rw [threaded_step_artifact_eq_canonical]

/-- The reduced exact threaded step services the same batch-node set as the
canonical serial step. -/
theorem threaded_exact_single_lane_batch_nodes_refine_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    (threadedExactSingleLaneStepArtifact frontier schedule).batchNodes =
      (canonicalStepArtifact frontier).batchNodes := by
  rw [threaded_step_artifact_eq_canonical]

/-- The reduced authoritative state slice for one exact threaded single-lane
step matches the canonical serial state slice exactly. -/
theorem threaded_exact_single_lane_state_slice_refines_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    stateSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier schedule) =
      stateSliceOfStepArtifact (canonicalStepArtifact frontier) := by
  rw [threaded_step_artifact_eq_canonical]

/-- The reduced observable slice for one exact threaded single-lane step matches
the canonical serial observable slice exactly. -/
theorem threaded_exact_single_lane_observation_slice_refines_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    observationSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier schedule) =
      observationSliceOfStepArtifact (canonicalStepArtifact frontier) := by
  rw [threaded_step_artifact_eq_canonical]

/-- Exact normalized commit-trace refinement is enough to recover equality of
the reduced observable slice at the claimed search boundary. -/
theorem threaded_exact_single_lane_commit_trace_refinement_implies_observation_equivalence
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    observationSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier schedule) =
      observationSliceOfStepArtifact (canonicalStepArtifact frontier) :=
  threaded_exact_single_lane_observation_slice_refines_canonical frontier schedule

/-- The exported reduced state-artifact schema for one exact threaded
single-lane step matches the canonical serial artifact exactly. -/
theorem threaded_exact_single_lane_state_artifact_refines_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    stateArtifactOfStateSlice (stateSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier schedule)) =
      stateArtifactOfStateSlice (stateSliceOfStepArtifact (canonicalStepArtifact frontier)) := by
  rw [threaded_step_artifact_eq_canonical]

/-- Multi-step state-slice refinement for exact threaded single-lane search over
an arbitrary frontier trace. -/
theorem threaded_exact_single_lane_multi_step_state_trace_refines_canonical
    (trace : FrontierTrace) (schedules : ∀ i, LaneSchedule (trace i)) :
    threadedStateSliceTrace trace schedules = canonicalStateSliceTrace trace := by
  funext i
  simp only [threadedStateSliceTrace, canonicalStateSliceTrace, threaded_step_artifact_eq_canonical]

/-- Multi-step observation-slice refinement for exact threaded single-lane
search over an arbitrary frontier trace. -/
theorem threaded_exact_single_lane_multi_step_observation_trace_refines_canonical
    (trace : FrontierTrace) (schedules : ∀ i, LaneSchedule (trace i)) :
    threadedObservationSliceTrace trace schedules = canonicalObservationSliceTrace trace := by
  funext i
  simp only [threadedObservationSliceTrace, canonicalObservationSliceTrace,
    threaded_step_artifact_eq_canonical]

/-- Multi-step exported state-artifact refinement for exact threaded single-lane
search over an arbitrary frontier trace. -/
theorem threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical
    (trace : FrontierTrace) (schedules : ∀ i, LaneSchedule (trace i)) :
    threadedStateArtifactTrace trace schedules = canonicalStateArtifactTrace trace := by
  funext i
  simp only [threadedStateArtifactTrace, canonicalStateArtifactTrace,
    threaded_exact_single_lane_multi_step_state_trace_refines_canonical]

end Search
end Proofs
end Runtime
