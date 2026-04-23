import Distributed.Families.Nakamoto.Core

set_option autoImplicit false

/-! # Distributed.Families.Nakamoto.API

High-level API for automatic Nakamoto-style security certification.
-/

namespace Distributed
namespace Nakamoto

universe u v w

/-- Certified protocol package for Nakamoto-style guarantees. -/
structure SecurityProtocol where
  State : Type u
  Block : Type v
  Party : Type w
  model : Model State Block Party
  assumptions : Assumptions model

/-- Extract probabilistic-safety theorem from a certified protocol bundle. -/
theorem probabilistic_safety_of_protocol (P : SecurityProtocol) :
    ProbabilisticSafety P.model P.assumptions.AdmissibleRun P.assumptions.ε :=
  probabilistic_safety_of_assumptions P.assumptions

/-- Extract settlement-finality theorem from a certified protocol bundle. -/
theorem settlement_finality_of_protocol (P : SecurityProtocol) :
    SettlementDepthFinality
      P.model P.assumptions.AdmissibleRun P.assumptions.settlementDepth :=
  settlement_finality_of_assumptions P.assumptions

/-- Extract churn-liveness theorem from a certified protocol bundle. -/
theorem liveness_under_churn_of_protocol (P : SecurityProtocol) :
    LivenessUnderChurn P.model P.assumptions.AdmissibleRun P.assumptions.churnBudget :=
  liveness_under_churn_of_assumptions P.assumptions

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : SecurityProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end Nakamoto
end Distributed
