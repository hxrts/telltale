import Runtime.Proofs.Search.Liveness

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.GenericLiveness

Generic liveness, termination, and fairness theorems for the search proof
lane.

This module intentionally re-exports only the generic machine theorems from
`Liveness`; path-problem discovery/publication results are surfaced separately
from `PathProblems`.
-/

namespace Runtime
namespace Proofs
namespace Search

theorem generic_fixed_phase_canonical_serial_terminates_under_finite_reachable_bound
    {goal : Nat}
    {reachable : List Nat}
    {trace : SearchMachineTrace}
    (hPremises : FixedPhaseTerminationPremises goal reachable trace) :
    ∃ j,
      j ≤ reachable.length - (trace 0).closedNodes.length ∧
      (trace j).frontier = [] :=
  fixed_phase_canonical_serial_terminates_under_finite_reachable_bound hPremises

theorem generic_rebuild_aware_canonical_serial_terminates_under_phase_work_measure
    {goal : Nat}
    {trace : SearchMachineTrace}
    (hPremises : RebuildAwareTerminationPremises goal trace) :
    ∃ j, j ≤ rebuildAwareEncodedMeasure hPremises 0 ∧ (trace j).frontier = [] :=
  rebuild_aware_canonical_serial_terminates_under_phase_work_measure hPremises

theorem generic_bounded_strict_preemption_eventually_becomes_min
    {trace : FrontierTrace}
    {start bound : Nat}
    {entry : FrontierEntry}
    (hPremises : BoundedStrictPreemptionPremises trace start bound entry) :
    ∃ j, j ≤ bound ∧ IsMinPriority (trace (start + j)) entry :=
  bounded_strict_preemption_eventually_becomes_min hPremises

theorem generic_canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption
    {trace : FrontierTrace}
    {start bound : Nat}
    {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hPremises : BoundedStrictPreemptionPremises trace start bound entry) :
    EventuallyServicedWithin trace start (bound + 1) entry :=
  canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption hTrace hPremises

theorem generic_finite_better_entry_exhaustion_eventually_becomes_min
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hPremises : FiniteBetterEntryExhaustionPremises trace start entry) :
    ∃ j, j ≤ hPremises.betterEntryUniverse.length ∧ IsMinPriority (trace (start + j)) entry :=
  finite_better_entry_exhaustion_eventually_becomes_min hPremises

theorem generic_canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hTrace : CanonicalSerialTrace trace)
    (hPremises : FiniteBetterEntryExhaustionPremises trace start entry) :
    EventuallyServicedWithin trace start (hPremises.betterEntryUniverse.length + 1) entry :=
  canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion hTrace hPremises

theorem generic_canonical_serial_nonmin_entry_eventually_serviced_under_scheduler_fairness
    {trace : FrontierTrace}
    {start : Nat}
    {entry : FrontierEntry}
    (hPremises : SchedulerFairnessPremises trace start entry) :
    EventuallyServicedWithin trace start (hPremises.serviceHorizon + 1) entry :=
  canonical_serial_nonmin_entry_eventually_serviced_under_scheduler_fairness hPremises

end Search
end Proofs
end Runtime
