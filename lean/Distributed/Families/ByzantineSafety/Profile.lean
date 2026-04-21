import Distributed.Families.ByzantineSafety.API

set_option autoImplicit false

/-! # Distributed.Families.ByzantineSafety.Profile

Profile constructors for Byzantine-safety theorem-pack attachment.
-/

namespace Distributed
namespace ByzantineSafety
namespace Profile

universe u v w x

/-- Build a Byzantine-safety profile from semantic safety evidence and protocol validation. -/
def mk
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (model : Model State Decision Certificate Obs)
    (safetyAssumptions : SafetyAssumptions model)
    (protocolSpec : ProtocolSpec)
    (assumptionsPassed :
      (runAssumptionValidation
        protocolSpec (byzantineSafetyAssumptionsFor protocolSpec)).allPassed = true)
    (livenessAssumptions? : Option LivenessAssumptions := none) :
    SafetyProtocol where
  State := State
  Decision := Decision
  Certificate := Certificate
  Obs := Obs
  model := model
  safetyAssumptions := safetyAssumptions
  livenessAssumptions? := livenessAssumptions?
  protocolSpec := protocolSpec
  assumptionsPassed := assumptionsPassed

/--
Build a Byzantine-safety profile from a quorum-geometry profile. The safety
artifact is derived from quorum intersection and lock monotonicity; the protocol
spec gate only records that the declared Byzantine profile is admissible.
-/
def ofQuorumGeometry
    (protocol : Distributed.QuorumGeometry.SafetyProtocol)
    (protocolSpec : ProtocolSpec)
    (assumptionsPassed :
      (runAssumptionValidation
        protocolSpec (byzantineSafetyAssumptionsFor protocolSpec)).allPassed = true)
    (livenessAssumptions? : Option LivenessAssumptions := none) :
    SafetyProtocol where
  State := protocol.State
  Decision := protocol.Decision
  Certificate := protocol.Certificate
  Obs := protocol.State
  model := modelOfQuorumGeometry protocol.model
  safetyAssumptions :=
    safetyAssumptionsOfQuorumGeometry protocol protocolSpec
  livenessAssumptions? := livenessAssumptions?
  protocolSpec := protocolSpec
  assumptionsPassed := assumptionsPassed

end Profile
end ByzantineSafety
end Distributed
