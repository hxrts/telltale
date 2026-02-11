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
  characterization :
    CoordinationCharacterization model :=
      coordination_characterization_of_assumptions assumptions premises

/-- Extract coordination characterization from a certified protocol bundle. -/
theorem characterization_of_protocol (P : CoordinationProtocol) :
    CoordinationCharacterization P.model :=
  P.characterization

/-- Monotone side of the characterization. -/
theorem coordinationFree_of_monotone (P : CoordinationProtocol)
    (hMono : P.model.monotoneUpdateClass) :
    CoordinationFreeSafety P.model :=
  P.characterization.1 hMono

/-- Non-monotone side of the characterization. -/
theorem coordinationRequired_of_nonMonotone (P : CoordinationProtocol)
    (hNonMono : ¬ P.model.monotoneUpdateClass) :
    CoordinationRequired P.model :=
  P.characterization.2 hNonMono

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : CoordinationProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end Coordination
end Distributed
