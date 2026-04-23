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
  detector : DetectorClass

/-- Extract solvability boundary theorem from a certified protocol bundle. -/
theorem solvability_boundary_of_protocol (P : BoundaryProtocol) :
    SolvableBoundary P.model P.detector :=
  solvability_boundary_of_assumptions P.assumptions P.detector

/-- Extract impossibility boundary theorem from a certified protocol bundle. -/
theorem impossibility_boundary_of_protocol (P : BoundaryProtocol) :
    ImpossibilityBoundary P.model P.detector :=
  impossibility_boundary_of_assumptions P.assumptions P.detector

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : BoundaryProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end FailureDetectors
end Distributed
