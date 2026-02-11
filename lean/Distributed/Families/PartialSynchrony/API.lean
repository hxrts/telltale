import Distributed.Families.PartialSynchrony.Core

set_option autoImplicit false

/-! # Distributed.Families.PartialSynchrony.API

High-level API for automatic partial-synchrony liveness certification.
-/

namespace Distributed
namespace PartialSynchrony

universe u v w x

/-- Certified protocol package for partial-synchrony liveness properties. -/
structure LivenessProtocol where
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
  boundedPostGST :
    BoundedTerminationAfterGST model premises.FairRun premises.gst premises.postGSTBound :=
      bounded_postGST_termination_of_assumptions assumptions premises

/-- Extract eventual-decision theorem from a certified protocol bundle. -/
theorem eventualDecision_of_protocol (P : LivenessProtocol) :
    TerminatesOnAllFairRuns P.model P.premises.FairRun :=
  P.eventualDecision

/-- Extract bounded post-GST termination theorem from a certified protocol bundle. -/
theorem boundedPostGST_of_protocol (P : LivenessProtocol) :
    BoundedTerminationAfterGST
      P.model P.premises.FairRun P.premises.gst P.premises.postGSTBound :=
  P.boundedPostGST

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : LivenessProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end PartialSynchrony
end Distributed
