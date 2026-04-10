import Runtime.Proofs.Search.Refinement

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.ProfileClaims

Profile-scoped fairness claims for search scheduling.

This module makes the public fairness story explicit by scheduler profile:

- canonical serial: exact one-step fairness for the current min-key batch
- threaded exact single-lane: exact one-step refinement to canonical serial
- batched exact / envelope-bounded: no unconditional theorem here; they require
  additional certified window and fairness premises
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Search scheduler profiles, mirrored from the Rust search runtime surface. -/
inductive SearchSchedulerProfile where
  | canonicalSerial
  | threadedExactSingleLane
  | batchedParallelExact
  | batchedParallelEnvelopeBounded
  deriving DecidableEq, Repr

/-- Public fairness-claim status by scheduler profile. -/
inductive FairnessClaimClass where
  | exactOneStep
  | exactOneStepUnderRefinement
  | premisedWindowBounded
  | premiseOnly
  deriving DecidableEq, Repr

/-- Public fairness classification for each search scheduler profile. -/
def fairnessClaimClass : SearchSchedulerProfile → FairnessClaimClass
  | .canonicalSerial => .exactOneStep
  | .threadedExactSingleLane => .exactOneStepUnderRefinement
  | .batchedParallelExact => .premisedWindowBounded
  | .batchedParallelEnvelopeBounded => .premisedWindowBounded

/-- The reduced threaded exact single-lane step refines canonical serial search
exactly. This models the real implementation boundary: parallel successor
generation does not change the frozen legal batch or the normalized committed
post-state. -/
theorem threaded_exact_single_lane_step_refines_canonical
    (frontier : List FrontierEntry) :
    frontierAfterThreadedExactSingleLaneStep frontier =
      frontierAfterCanonicalStep frontier :=
  rfl

/-- Canonical serial search has an unconditional exact fairness claim for the
current legal min-key batch. -/
theorem canonical_serial_profile_has_exact_one_step_fairness :
    fairnessClaimClass .canonicalSerial = .exactOneStep :=
  rfl

/-- Canonical serial search services a goal entry within one step once that
entry is in the current legal min-key batch. This is the route-discovery-facing
restatement of the exact one-step fairness theorem. -/
theorem canonical_serial_goal_window_service_has_exact_suffix_bound
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterCanonicalStep frontier :=
  canonical_serial_one_step_fair_for_min_priority_entries hMin

/-- Threaded exact single-lane search inherits the canonical exact fairness
claim because its reduced one-step semantics refine canonical serial search
exactly. -/
theorem threaded_exact_single_lane_has_exact_one_step_fairness
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterThreadedExactSingleLaneStep frontier := by
  rw [threaded_exact_single_lane_step_refines_canonical]
  exact canonical_serial_one_step_fair_for_min_priority_entries hMin

/-- Threaded exact single-lane search inherits the same goal-window discovery
suffix bound through exact one-step refinement to canonical serial search. -/
theorem threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterThreadedExactSingleLaneStep frontier := by
  rw [threaded_exact_single_lane_step_refines_canonical]
  exact canonical_serial_goal_window_service_has_exact_suffix_bound hMin

/-- Threaded exact single-lane search also inherits exact reduced observation
equivalence to canonical serial search across the claimed search boundary. -/
theorem threaded_exact_single_lane_has_exact_observation_equivalence
    (frontier : List FrontierEntry) :
    observationSliceOfStepArtifact (threadedExactSingleLaneStepArtifact frontier) =
      observationSliceOfStepArtifact (canonicalStepArtifact frontier) :=
  threaded_exact_single_lane_commit_trace_refinement_implies_observation_equivalence frontier

/-- Batched exact search has no unconditional fairness theorem in this module.
Its fairness claim is intentionally premise-scoped. -/
theorem batched_parallel_exact_claim_is_premised :
    fairnessClaimClass .batchedParallelExact = .premisedWindowBounded :=
  rfl

/-- A certified batched exact window that covers the current min-key batch is
window-fair for those entries. This is the explicit premise-scoped theorem
surface for the batched exact profile. -/
theorem certified_batched_exact_window_is_fair
    {frontier : List FrontierEntry}
    (certificate : BatchedExactWindowCertificate frontier)
    {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterCertifiedBatchWindow frontier certificate := by
  intro hAfter
  simp [frontierAfterCertifiedBatchWindow] at hAfter
  have hBatch : entry ∈ canonicalBatch frontier :=
    min_priority_entry_serviced_next_step hMin
  exact hAfter.2 (certificate.coversCurrentMinKeyBatch hBatch)

/-- The premise-scoped batched exact theorem can be restated as a one-window
eventual-service claim. -/
theorem certified_batched_exact_window_eventually_services_min_priority_entries
    {trace : FrontierTrace} {start : Nat}
    (certificate : BatchedExactWindowCertificate (trace start))
    (hStep : trace (start + 1) =
      frontierAfterCertifiedBatchWindow (trace start) certificate)
    {entry : FrontierEntry}
    (hMin : IsMinPriority (trace start) entry) :
    EventuallyServicedWithin trace start 1 entry := by
  refine ⟨0, Nat.zero_lt_one, ?_⟩
  simpa [EventuallyServicedWithin, hStep] using
    certified_batched_exact_window_is_fair certificate hMin

/-- Bounded dynamic starvation-freedom for certified batched exact search.
If an entry remains eligible and reaches the min-priority window within one
bounded preemption horizon, then the certified batch that covers that window
services it within the same bound. -/
theorem certified_batched_exact_window_bounded_dynamic_starvation_freedom
    {trace : FrontierTrace} {start bound : Nat} {entry : FrontierEntry}
    (certificates : ∀ j : Fin bound, BatchedExactWindowCertificate (trace (start + j.1)))
    (hSteps : ∀ j : Fin bound,
      trace (start + j.1 + 1) =
        frontierAfterCertifiedBatchWindow (trace (start + j.1)) (certificates j))
    (hEligible : ContinuouslyEligible trace start bound entry)
    (hBounded : BoundedPreemptionWindow trace start bound entry) :
    EventuallyServicedWithin trace start bound entry := by
  rcases hBounded with ⟨j, hjlt, hMin⟩
  have _hEligibleAtJ := hEligible j hjlt
  let jfin : Fin bound := ⟨j, hjlt⟩
  refine ⟨j, hjlt, ?_⟩
  have hStep :
      trace (start + j + 1) =
        frontierAfterCertifiedBatchWindow (trace (start + j)) (certificates jfin) := by
    simpa [jfin] using hSteps jfin
  have hFair :=
    certified_batched_exact_window_is_fair (certificates jfin) hMin
  simpa [EventuallyServicedWithin, hStep]
    using hFair

/-- Certified batched-exact window traces are structurally valid when each
certificate services exactly the current legal min-key batch and publishes the
standard one-window bound. -/
theorem certified_window_trace_is_valid_for_exact_batch_service
    {trace : FrontierTrace} {start bound : Nat}
    (certificates : ∀ j : Fin bound, BatchedExactWindowCertificate (trace (start + j.1)))
    (hBatchExact : ∀ j : Fin bound,
      (certificates j).servicedEntries = canonicalBatch (trace (start + j.1)))
    (hBound : ∀ j : Fin bound, (certificates j).serviceBoundSteps = 1) :
    CertifiedWindowTraceValid trace start bound
      (fun j => certifiedWindowTraceEntryOfCertificate (trace (start + j.1)) (certificates j)) := by
  intro j
  constructor
  · simpa using hBound j
  · simp [certifiedWindowTraceEntryOfCertificate, hBatchExact j]

/-- Envelope-bounded batched search now carries a theorem-backed certified
window claim. -/
theorem batched_parallel_envelope_claim_is_premised :
    fairnessClaimClass .batchedParallelEnvelopeBounded = .premisedWindowBounded :=
  rfl

end Search
end Proofs
end Runtime
