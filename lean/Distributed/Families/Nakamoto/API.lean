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
  premises : Premises model
  probabilisticSafety :
    ProbabilisticSafety model premises.AdmissibleRun premises.ε :=
      probabilistic_safety_of_assumptions assumptions premises
  settlementFinality :
    SettlementDepthFinality model premises.AdmissibleRun premises.settlementDepth :=
      settlement_finality_of_assumptions assumptions premises
  livenessUnderChurn :
    LivenessUnderChurn model premises.AdmissibleRun premises.churnBudget :=
      liveness_under_churn_of_assumptions assumptions premises

/-- Extract probabilistic-safety theorem from a certified protocol bundle. -/
theorem probabilisticSafety_of_protocol (P : SecurityProtocol) :
    ProbabilisticSafety P.model P.premises.AdmissibleRun P.premises.ε :=
  P.probabilisticSafety

/-- Extract settlement-finality theorem from a certified protocol bundle. -/
theorem settlementFinality_of_protocol (P : SecurityProtocol) :
    SettlementDepthFinality P.model P.premises.AdmissibleRun P.premises.settlementDepth :=
  P.settlementFinality

/-- Extract churn-liveness theorem from a certified protocol bundle. -/
theorem livenessUnderChurn_of_protocol (P : SecurityProtocol) :
    LivenessUnderChurn P.model P.premises.AdmissibleRun P.premises.churnBudget :=
  P.livenessUnderChurn

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : SecurityProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end Nakamoto
end Distributed
