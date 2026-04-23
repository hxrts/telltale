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

/-- Extract eventual-decision theorem from a certified protocol bundle. -/
theorem eventual_decision_of_protocol (P : LivenessProtocol) :
    TerminatesOnAllFairRuns P.model P.assumptions.FairRun :=
  eventual_decision_of_assumptions P.assumptions

/-- Extract bounded post-GST termination theorem from a certified protocol bundle. -/
theorem bounded_post_gst_of_protocol (P : LivenessProtocol) :
    BoundedTerminationAfterGST
      P.model P.assumptions.FairRun P.assumptions.gst P.assumptions.postGSTBound :=
  bounded_post_gst_termination_of_assumptions P.assumptions

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : LivenessProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end PartialSynchrony
end Distributed
