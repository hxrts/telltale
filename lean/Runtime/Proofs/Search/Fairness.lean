import Runtime.Proofs.Search.Core

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Fairness

Proof-facing fairness results for the canonical serial search scheduler.

The proved unconditional guarantee is intentionally scoped to the current legal
min-key batch. This matches the actual implementation boundary of
`telltale-search`.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Membership in the canonical batch is exactly min-priority membership in the
current frontier. -/
theorem mem_canonicalBatch_iff_isMinPriority
    {frontier : List FrontierEntry} {entry : FrontierEntry} :
    entry ∈ canonicalBatch frontier ↔ IsMinPriority frontier entry := by
  simp [canonicalBatch, IsMinPriority]

/-- Every currently enabled min-priority frontier entry is serviced by the next
canonical serial step. -/
theorem min_priority_entry_serviced_next_step
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∈ canonicalBatch frontier :=
  (mem_canonicalBatch_iff_isMinPriority).2 hMin

/-- Every entry in the current min-key batch disappears from the frontier after
one canonical serial step. -/
theorem canonical_batch_entries_removed_after_step
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hBatch : entry ∈ canonicalBatch frontier) :
    entry ∉ frontierAfterCanonicalStep frontier := by
  intro hAfter
  simp [frontierAfterCanonicalStep] at hAfter
  exact hAfter.2 hBatch

/-- Canonical serial search is one-step fair for the current legal min-key
batch: any currently enabled min-priority entry cannot starve beyond the next
step. -/
theorem canonical_serial_one_step_fair_for_min_priority_entries
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hMin : IsMinPriority frontier entry) :
    entry ∉ frontierAfterCanonicalStep frontier :=
  canonical_batch_entries_removed_after_step
    (min_priority_entry_serviced_next_step hMin)

/-- The canonical serial search scheduler satisfies the search-specific
one-step fairness contract for any frozen frontier. -/
theorem canonical_serial_batch_is_one_step_fair
    (frontier : List FrontierEntry) :
    OneStepFair frontier := by
  intro entry hMin
  exact canonical_serial_one_step_fair_for_min_priority_entries hMin

/-- If a trace follows canonical serial stepping, any entry that is min-priority
at time `start` is serviced within one step. This gives the stronger
eventual-service theorem in the search-specific fairness vocabulary. -/
theorem currently_min_priority_eventually_serviced_within_one_step
    {trace : FrontierTrace} {start : Nat} {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hMin : IsMinPriority (trace start) entry) :
    EventuallyServicedWithin trace start 1 entry := by
  refine ⟨0, Nat.zero_lt_one, ?_⟩
  have hStep : trace (start + 1) = frontierAfterCanonicalStep (trace start) := by
    simpa using hTrace start
  simpa [EventuallyServicedWithin, hStep] using
    canonical_serial_one_step_fair_for_min_priority_entries hMin

/-- Continuous min-priority from one start point is stronger than needed for
canonical serial search. The entry is still serviced within one step, so the
longer continuity premise is harmlessly admissible. -/
theorem continuously_min_priority_until_service_implies_eventual_service
    {trace : FrontierTrace} {start horizon : Nat} {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hCont : ContinuouslyMinPriorityUntilService trace start horizon entry)
    (hPresent : entry ∈ trace start)
    (hHorizon : 0 < horizon) :
    EventuallyServicedWithin trace start 1 entry := by
  have hMin : IsMinPriority (trace start) entry :=
    hCont 0 hHorizon hPresent
  exact currently_min_priority_eventually_serviced_within_one_step hTrace hMin

/-- Dynamic liveness theorem for canonical serial search. If an entry remains
continuously eligible for one horizon prefix and no strictly better entry
appears during that prefix, then the entry is serviced within one step. This
exposes the stability premise explicitly instead of hiding it inside
`ContinuouslyMinPriorityUntilService`. -/
theorem continuously_eligible_without_strictly_better_entries_eventually_serviced
    {trace : FrontierTrace} {start horizon : Nat} {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hEligible : ContinuouslyEligible trace start horizon entry)
    (hNoBetter : NoStrictlyBetterEntryAppears trace start horizon entry)
    (hHorizon : 0 < horizon) :
    EventuallyServicedWithin trace start 1 entry := by
  have hMin : IsMinPriority (trace start) entry := by
    refine ⟨hEligible 0 hHorizon, ?_⟩
    intro other hOther
    have hNoBetterNow := hNoBetter 0 hHorizon other hOther
    exact Nat.le_of_not_lt hNoBetterNow
  exact currently_min_priority_eventually_serviced_within_one_step hTrace hMin

end Search
end Proofs
end Runtime
