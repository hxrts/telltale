import Distributed.Families.ByzantineSafety.Core

set_option autoImplicit false

/-! # Distributed.Families.ByzantineSafety.API

High-level API for automatic Byzantine safety characterization certification.
-/

namespace Distributed
namespace ByzantineSafety

universe u v w x

/-- Certified protocol package for Byzantine safety characterization. -/
structure SafetyProtocol where
  State : Type u
  Decision : Type v
  Certificate : Type w
  Obs : Type x
  model : Model State Decision Certificate Obs
  safetyAssumptions : SafetyAssumptions model
  livenessAssumptions? : Option LivenessAssumptions := none
  protocolSpec : ProtocolSpec
  assumptionsPassed :
    (runAssumptionValidation
      protocolSpec (byzantineSafetyAssumptionsFor protocolSpec)).allPassed = true

/-- Extract exact-characterization theorem from a certified protocol bundle. -/
theorem exact_characterization_of_protocol (P : SafetyProtocol) :
    ExactByzantineSafetyCharacterization P.model :=
  exact_byzantine_safety_characterization P.model

/-- Certified protocols expose the full assumption-summary pass gate. -/
theorem byzantine_assumptions_all_passed (P : SafetyProtocol) :
    (runAssumptionValidation
      P.protocolSpec (byzantineSafetyAssumptionsFor P.protocolSpec)).allPassed = true := by
  -- The package stores the full gate witness directly.
  exact P.assumptionsPassed

/-- Certified protocols expose certified-side characterization directly. -/
theorem characterization_of_protocol (P : SafetyProtocol) :
    CharacterizationCondition P.model := by
  -- Characterization is derived from the embedded quorum-geometry proof.
  exact characterization_of_byzantine_safety P.model
    (byzantine_safety_of_assumptions P.model P.safetyAssumptions)

/-- Certified protocols expose committed-side Byzantine safety directly. -/
theorem byzantine_safety_of_protocol (P : SafetyProtocol) :
    ByzantineSafety P.model := by
  -- Project the soundness branch from the packaged exact characterization.
  exact (exact_characterization_of_protocol P).1 (characterization_of_protocol P)

end ByzantineSafety
end Distributed
