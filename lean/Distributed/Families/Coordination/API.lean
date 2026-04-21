import Distributed.Families.Coordination.Core

set_option autoImplicit false

/-! # Distributed.Families.Coordination.API

High-level API for automatic coordination characterization.
-/

namespace Distributed
namespace Coordination

universe u v

/-- Certified protocol package for coordination characterization. -/
structure CoordinationProtocol where
  State : Type u
  Update : Type v
  model : Model State Update
  assumptions : Assumptions model
  premises : Premises model

/-- Extract coordination characterization from a certified protocol bundle. -/
theorem characterization_of_protocol (P : CoordinationProtocol) :
    CoordinationCharacterization P.model :=
  coordination_characterization_of_assumptions P.assumptions P.premises

/-- Monotone side of the characterization. -/
theorem coordination_free_of_monotone (P : CoordinationProtocol)
    (hMono : MonotoneUpdates P.model) :
    CoordinationFreeSafety P.model :=
  (characterization_of_protocol P).1 hMono

/-- Non-monotone side of the characterization. -/
theorem coordination_required_of_non_monotone (P : CoordinationProtocol)
    (hNonMono : ¬ MonotoneUpdates P.model) :
    CoordinationRequired P.model :=
  (characterization_of_protocol P).2 hNonMono

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : CoordinationProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end Coordination
end Distributed
