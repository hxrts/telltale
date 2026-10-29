import Runtime.Proofs.Search.Liveness.Termination

set_option autoImplicit false

/-! # Runtime.Proofs.Search.Liveness.Fairness

Bounded fairness for frontier entries that are not initially min-priority:
bounded strict preemption, finite better-entry exhaustion, and the derived
scheduler-fairness service horizon.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Premises for bounded service of an entry that is not initially min-priority.
The entry stays present, and the count of strictly better competitors decreases
strictly whenever it is still not min-priority. -/
structure BoundedStrictPreemptionPremises
    (trace : FrontierTrace)
    (start bound : Nat)
    (entry : FrontierEntry) : Prop where
  presentAcrossWindow :
    ∀ j, j ≤ bound → entry ∈ trace (start + j)
  initialStrictlyBetterBound :
    StrictlyBetterEntryCount (trace start) entry ≤ bound
  strictlyBetterDecreasesWhileNonMin :
    ∀ j, j < bound →
      entry ∈ trace (start + j) →
      ¬ IsMinPriority (trace (start + j)) entry →
      StrictlyBetterEntryCount (trace (start + j + 1)) entry <
        StrictlyBetterEntryCount (trace (start + j)) entry

/-- Under bounded strict preemption, a present entry eventually reaches the
min-priority window. -/
theorem bounded_strict_preemption_eventually_becomes_min
    {trace : FrontierTrace}
    {start bound : Nat}
    {entry : FrontierEntry}
    (hPremises : BoundedStrictPreemptionPremises trace start bound entry) :
    ∃ j, j ≤ bound ∧ IsMinPriority (trace (start + j)) entry := by
  induction bound generalizing start with
  | zero =>
      refine ⟨0, Nat.le_refl 0, ?_⟩
      have hPresent : entry ∈ trace (start + 0) :=
        hPremises.presentAcrossWindow 0 (Nat.le_refl 0)
      have hCountZero :
          StrictlyBetterEntryCount (trace start) entry = 0 := by
        exact Nat.eq_zero_of_le_zero hPremises.initialStrictlyBetterBound
      simpa using isMinPriority_of_strictlyBetterEntryCount_eq_zero hPresent hCountZero
  | succ bound ih =>
      by_cases hMin : IsMinPriority (trace start) entry
      · exact ⟨0, Nat.zero_le _, hMin⟩
      · have hPresent0 : entry ∈ trace (start + 0) :=
          hPremises.presentAcrossWindow 0 (Nat.zero_le _)
        have hDecrease :
            StrictlyBetterEntryCount (trace (start + 1)) entry <
              StrictlyBetterEntryCount (trace start) entry := by
          simpa using
            hPremises.strictlyBetterDecreasesWhileNonMin 0 (Nat.zero_lt_succ _) hPresent0 hMin
        have hCountNext :
            StrictlyBetterEntryCount (trace (start + 1)) entry ≤ bound := by
          have hInit := hPremises.initialStrictlyBetterBound
          omega
        let shiftedPremises : BoundedStrictPreemptionPremises trace (start + 1) bound entry :=
          { presentAcrossWindow := by
              intro j hj
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                hPremises.presentAcrossWindow (j + 1) (Nat.succ_le_succ hj)
          , initialStrictlyBetterBound := hCountNext
          , strictlyBetterDecreasesWhileNonMin := by
              intro j hj hPresent hNotMin
              have hPresent' : entry ∈ trace (start + (j + 1)) := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hPresent
              have hNotMin' : ¬ IsMinPriority (trace (start + (j + 1))) entry := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hNotMin
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                hPremises.strictlyBetterDecreasesWhileNonMin (j + 1)
                  (Nat.succ_lt_succ hj) hPresent' hNotMin'
          }
        rcases ih shiftedPremises with ⟨j, hj, hMinLater⟩
        refine ⟨j + 1, Nat.succ_le_succ hj, ?_⟩
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hMinLater

/-- Canonical serial search therefore services a non-min-priority entry within
one extra step after it first becomes min-priority. -/
theorem canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption
    {trace : FrontierTrace}
    {start bound : Nat}
    {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hPremises : BoundedStrictPreemptionPremises trace start bound entry) :
    EventuallyServicedWithin trace start (bound + 1) entry := by
  rcases bounded_strict_preemption_eventually_becomes_min hPremises with
    ⟨j, hj, hMin⟩
  have hService :
      EventuallyServicedWithin trace (start + j) 1 entry :=
    currently_min_priority_eventually_serviced_within_one_step hTrace hMin
  rcases hService with ⟨k, hk, hAbsent⟩
  refine ⟨j + k, ?_, ?_⟩
  · have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    subst hk0
    omega
  · have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    subst hk0
    simpa [Nat.add_assoc] using hAbsent

/-- More structural premise bundle for non-min fairness: the better work ahead
of one entry lives in a finite universe whose size itself provides the service
bound. -/
structure FiniteBetterEntryExhaustionPremises
    (trace : FrontierTrace)
    (start : Nat)
    (entry : FrontierEntry) where
  betterEntryUniverse : List FrontierEntry
  betterEntryUniverseNodup : betterEntryUniverse.Nodup
  presentAcrossUniverseWindow :
    ∀ j, j ≤ betterEntryUniverse.length → entry ∈ trace (start + j)
  initialStrictlyBetterBoundByUniverse :
    StrictlyBetterEntryCount (trace start) entry ≤ betterEntryUniverse.length
  noUnboundedBetterArrivals :
    ∀ j, j ≤ betterEntryUniverse.length →
      ∀ other, other ∈ trace (start + j) → other.priority < entry.priority →
      other ∈ betterEntryUniverse
  strictlyBetterDecreasesWhileNonMin :
    ∀ j, j < betterEntryUniverse.length →
      entry ∈ trace (start + j) →
      ¬ IsMinPriority (trace (start + j)) entry →
      StrictlyBetterEntryCount (trace (start + j + 1)) entry <
        StrictlyBetterEntryCount (trace (start + j)) entry

/-- A finite better-entry universe induces the older bounded strict-preemption
premise with the bound specialized to the universe size. -/
theorem finite_better_entry_exhaustion_implies_bounded_strict_preemption
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hPremises : FiniteBetterEntryExhaustionPremises trace start entry) :
    BoundedStrictPreemptionPremises trace start
      hPremises.betterEntryUniverse.length entry := by
  refine
    { presentAcrossWindow := hPremises.presentAcrossUniverseWindow
    , initialStrictlyBetterBound := hPremises.initialStrictlyBetterBoundByUniverse
    , strictlyBetterDecreasesWhileNonMin := hPremises.strictlyBetterDecreasesWhileNonMin
    }

/-- Structural finite-universe fairness theorem for entries that are not
initially min-priority. -/
theorem finite_better_entry_exhaustion_eventually_becomes_min
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hPremises : FiniteBetterEntryExhaustionPremises trace start entry) :
    ∃ j, j ≤ hPremises.betterEntryUniverse.length ∧
      IsMinPriority (trace (start + j)) entry := by
  exact bounded_strict_preemption_eventually_becomes_min
    (finite_better_entry_exhaustion_implies_bounded_strict_preemption hPremises)

/-- Structural finite-universe service theorem for entries that are not
initially min-priority. -/
theorem canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hPremises : FiniteBetterEntryExhaustionPremises trace start entry) :
    EventuallyServicedWithin trace start
      (hPremises.betterEntryUniverse.length + 1) entry := by
  exact canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption
    hTrace (finite_better_entry_exhaustion_implies_bounded_strict_preemption hPremises)

/-- One canonical serial step strictly shrinks the set of strictly better
competitors of a present entry that is not yet min-priority: the min-key batch
is strictly better than that entry and is removed, and the canonical step never
adds entries. -/
theorem strictlyBetterEntryCount_canonical_step_lt
    {frontier : List FrontierEntry} {entry : FrontierEntry}
    (hPresent : entry ∈ frontier) (hNotMin : ¬ IsMinPriority frontier entry) :
    StrictlyBetterEntryCount (frontierAfterCanonicalStep frontier) entry <
      StrictlyBetterEntryCount frontier entry := by
  obtain ⟨other, hOther, hLt⟩ : ∃ other ∈ frontier, other.priority < entry.priority := by
    by_contra h
    push Not at h
    exact hNotMin ⟨hPresent, h⟩
  obtain ⟨m, hm⟩ := exists_minPriority_of_frontier_ne_nil (List.ne_nil_of_mem hPresent)
  have hmBatch : m ∈ canonicalBatch frontier := min_priority_entry_serviced_next_step hm
  have hmBetter : m.priority < entry.priority := lt_of_le_of_lt (hm.2 other hOther) hLt
  unfold StrictlyBetterEntryCount frontierAfterCanonicalStep
  rw [List.filter_filter, show (fun a : FrontierEntry =>
      decide (a.priority < entry.priority) && decide (a ∉ canonicalBatch frontier)) =
      (fun a => decide (a ∉ canonicalBatch frontier) && decide (a.priority < entry.priority)) from
      funext fun _ => Bool.and_comm _ _, ← List.filter_filter]
  exact List.length_filter_lt_length_iff_exists.mpr
    ⟨m, by simp [hm.1, hmBetter], by simpa using hmBatch⟩

/-- Canonical serial search services every present entry within one more step
than its current number of strictly better competitors. The bound is derived
from the scheduler model itself (`CanonicalSerialTrace`), not assumed. -/
theorem canonical_serial_present_entry_serviced_within_strictly_better_count
    {trace : FrontierTrace} (hTrace : CanonicalSerialTrace trace) :
    ∀ (n start : Nat) (entry : FrontierEntry),
      StrictlyBetterEntryCount (trace start) entry = n →
      entry ∈ trace start → EventuallyServicedWithin trace start (n + 1) entry := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro start entry hCount hPresent
  by_cases hMin : IsMinPriority (trace start) entry
  · rcases currently_min_priority_eventually_serviced_within_one_step hTrace hMin with
      ⟨j, hj, h⟩
    exact ⟨j, by omega, h⟩
  have hLt := strictlyBetterEntryCount_canonical_step_lt hPresent hMin
  rw [← hTrace start] at hLt
  by_cases hNext : entry ∈ trace (start + 1)
  · obtain ⟨j, hj, hAbs⟩ := ih _ (hCount ▸ hLt) (start + 1) entry rfl hNext
    refine ⟨j + 1, by omega, ?_⟩
    rw [show start + (j + 1) + 1 = start + 1 + j + 1 by omega]
    exact hAbs
  · exact ⟨0, by omega, by simpa using hNext⟩

/-- Scheduler-facing public fairness premise bundle: the trace follows the
canonical serial scheduler and the entry is present at the start. No drain or
service-horizon assumption is taken; the horizon is computed. -/
structure SchedulerFairnessPremises
    (trace : FrontierTrace)
    (start : Nat)
    (entry : FrontierEntry) : Prop where
  canonicalTrace : CanonicalSerialTrace trace
  presentAtStart : entry ∈ trace start

/-- Derived service horizon: the number of strictly better competitors at the
start. -/
def SchedulerFairnessPremises.serviceHorizon
    {trace : FrontierTrace} {start : Nat} {entry : FrontierEntry}
    (_ : SchedulerFairnessPremises trace start entry) : Nat :=
  StrictlyBetterEntryCount (trace start) entry

/-- Under the canonical serial scheduler, a present non-min entry is serviced
within its derived service horizon plus one step. -/
theorem canonical_serial_nonmin_entry_eventually_serviced_under_scheduler_fairness
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hPremises : SchedulerFairnessPremises trace start entry) :
    EventuallyServicedWithin trace start (hPremises.serviceHorizon + 1) entry :=
  canonical_serial_present_entry_serviced_within_strictly_better_count
    hPremises.canonicalTrace _ start entry rfl hPremises.presentAtStart

end Search
end Proofs
end Runtime
