import Distributed.Families.Responsiveness.Core

set_option autoImplicit false

/-! # Distributed.Families.Responsiveness.API

High-level API for automatic responsiveness certification.
-/

namespace Distributed
namespace Responsiveness

universe u v w x

/-- Certified protocol package for responsiveness properties. -/
structure ResponsiveProtocol where
  State : Type u
  Value : Type v
  Event : Type w
  Party : Type x
  model : Model State Value Event Party
  assumptions : Assumptions model
  premises : Premises model
  eventualDecision :
    TerminatesOnAllFairRuns model premises.FairRun :=
      eventual_decision_of_assumptions assumptions premises
  timeoutIndependentLatency :
    TimeoutIndependentLatencyBound model premises.FairRun
      premises.gst premises.optimisticBound :=
      timeout_independent_latency_of_assumptions assumptions premises

/-- Extract eventual-decision theorem from a certified protocol bundle. -/
theorem eventual_decision_of_protocol (P : ResponsiveProtocol) :
    TerminatesOnAllFairRuns P.model P.premises.FairRun :=
  P.eventualDecision

/-- Extract timeout-independent-latency theorem from a certified protocol bundle. -/
theorem timeout_independent_latency_of_protocol (P : ResponsiveProtocol) :
    TimeoutIndependentLatencyBound
      P.model P.premises.FairRun P.premises.gst P.premises.optimisticBound :=
  P.timeoutIndependentLatency

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : ResponsiveProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end Responsiveness
end Distributed
