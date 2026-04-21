import Distributed.Families.TriangleOfForgetting.Core

set_option autoImplicit false

/-! # Distributed.Families.TriangleOfForgetting.API

High-level API for automatic triangle-of-forgetting impossibility certification.
-/

namespace Distributed
namespace TriangleOfForgetting

universe u v w

universe x

/-- Full triangle-of-forgetting-certified protocol package. -/
structure ImpossibilityProtocol where
  State : Type u
  Update : Type v
  Member : Type w
  View : Type x
  model : Model State Update Member View
  assumptions : Assumptions model

/-- Extract the full triangle-of-forgetting impossibility theorem from a certified protocol. -/
theorem impossibility_of_protocol (P : ImpossibilityProtocol) :
    ¬ TriangleGuarantee P.model :=
  not_triangle_guarantee_of_assumptions P.assumptions

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : ImpossibilityProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end TriangleOfForgetting
end Distributed
