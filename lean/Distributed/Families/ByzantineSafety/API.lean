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
  exactCharacterization :
    ExactByzantineSafetyCharacterization model :=
      exact_byzantineSafety_characterization model

/-- Extract exact-characterization theorem from a certified protocol bundle. -/
theorem exactCharacterization_of_protocol (P : SafetyProtocol) :
    ExactByzantineSafetyCharacterization P.model :=
  P.exactCharacterization

/-- Certified protocols expose the full assumption-summary pass gate. -/
theorem byzantineAssumptions_allPassed (P : SafetyProtocol) :
    (runAssumptionValidation
      P.protocolSpec (byzantineSafetyAssumptionsFor P.protocolSpec)).allPassed = true := by
  -- The package stores the full gate witness directly.
  exact P.assumptionsPassed

/-- Certified protocols expose committed-side Byzantine safety directly. -/
theorem byzantineSafety_of_protocol (P : SafetyProtocol) :
    ByzantineSafety P.model := by
  -- Project the soundness branch from the packaged exact characterization.
  exact P.exactCharacterization.1 P.safetyAssumptions.characterizationWitness

/-- Certified protocols expose certified-side characterization directly. -/
theorem characterization_of_protocol (P : SafetyProtocol) :
    CharacterizationCondition P.model :=
  P.safetyAssumptions.characterizationWitness

end ByzantineSafety
end Distributed
