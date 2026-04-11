import Runtime.Proofs.Search.Envelope

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Approximation

Generic approximation/exactness contract vocabulary for the search proof lane.

This module factors the route-oriented "optimal route" wording into generic
selected-result contracts: exact, certified-window exact, budgeted anytime,
and envelope-bounded.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Proof-side effort profile mirrored from the runtime. -/
inductive SearchEffortProfile where
  | runToCompletion
  | schedulerStepBudget (steps : Nat)
  deriving DecidableEq, Repr

/-- Generic approximation/exactness contract class. -/
inductive SearchApproximationContractClass where
  | exact
  | certifiedWindowExact
  | budgetedAnytime
  | envelopeBounded
  | noResult
  deriving DecidableEq, Repr

/-- Contract classification from execution profile and effort mode. -/
def approximationContractClass
    (profile : SearchExecutionProfile)
    (effort : SearchEffortProfile) : SearchApproximationContractClass :=
  match effort with
  | .schedulerStepBudget _ => .budgetedAnytime
  | .runToCompletion =>
      match profile with
      | .canonicalSerial => .exact
      | .threadedExactSingleLane => .exact
      | .batchedParallelExact => .certifiedWindowExact
      | .batchedParallelEnvelopeBounded => .envelopeBounded

theorem canonical_serial_has_exact_result_contract :
    approximationContractClass .canonicalSerial .runToCompletion = .exact :=
  rfl

theorem threaded_exact_single_lane_has_exact_result_contract :
    approximationContractClass .threadedExactSingleLane .runToCompletion = .exact :=
  rfl

theorem batched_parallel_exact_has_certified_window_exact_contract :
    approximationContractClass .batchedParallelExact .runToCompletion =
      .certifiedWindowExact :=
  rfl

theorem batched_parallel_envelope_has_envelope_bounded_contract :
    approximationContractClass .batchedParallelEnvelopeBounded .runToCompletion =
      .envelopeBounded :=
  rfl

theorem scheduler_step_budget_yields_budgeted_anytime_contract
    (profile : SearchExecutionProfile) (steps : Nat) :
    approximationContractClass profile (.schedulerStepBudget steps) =
      .budgetedAnytime :=
  rfl

end Search
end Proofs
end Runtime
