import Distributed.Families.FailureDetectors.Core

set_option autoImplicit false

/-! # Distributed.Families.FailureDetectors.API

High-level API for automatic failure-detector boundary certification.
-/

namespace Distributed
namespace FailureDetectors

universe u v

/-- Certified protocol package for detector-boundary guarantees. -/
structure BoundaryProtocol where
  State : Type u
  Party : Type v
  model : Model State Party
  assumptions : Assumptions model
  premises : Premises model
  solvabilityBoundary :
    SolvableBoundary model premises.detector :=
      solvability_boundary_of_assumptions assumptions premises
  impossibilityBoundary :
    ImpossibilityBoundary model premises.detector :=
      impossibility_boundary_of_assumptions assumptions premises

/-- Extract solvability boundary theorem from a certified protocol bundle. -/
theorem solvabilityBoundary_of_protocol (P : BoundaryProtocol) :
    SolvableBoundary P.model P.premises.detector :=
  P.solvabilityBoundary

/-- Extract impossibility boundary theorem from a certified protocol bundle. -/
theorem impossibilityBoundary_of_protocol (P : BoundaryProtocol) :
    ImpossibilityBoundary P.model P.premises.detector :=
  P.impossibilityBoundary

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : BoundaryProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end FailureDetectors
end Distributed
