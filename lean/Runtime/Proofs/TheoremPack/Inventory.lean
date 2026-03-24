import Runtime.Proofs.TheoremPack.Build
set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

section

/-! ## Base Inventory -/

variable {ν : Type u} [VerificationModel ν]

def semanticObjectInventory
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : ProtocolMachineTheoremPack (space := space)) : List (String × Bool) :=
  SemanticObjectArtifacts.inventory pack.semanticObjects?

def theoremInventory
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : ProtocolMachineTheoremPack (space := space)) : List (String × Bool) :=
  [ ("termination", pack.termination?.isSome)
  , ("output_condition_soundness", pack.outputCondition?.isSome)
  , ("flp_lower_bound", pack.flpLowerBound?.isSome)
  , ("flp_impossibility", pack.flpImpossibility?.isSome)
  , ("cap_impossibility", pack.capImpossibility?.isSome)
  , ("quorum_geometry_safety", pack.quorumGeometry?.isSome)
  , ("partial_synchrony_liveness", pack.partialSynchrony?.isSome)
  , ("responsiveness", pack.responsiveness?.isSome)
  , ("nakamoto_security", pack.nakamoto?.isSome)
  , ("reconfiguration_safety", pack.reconfiguration?.isSome)
  , ("atomic_broadcast_ordering", pack.atomicBroadcast?.isSome)
  , ("accountable_safety", pack.accountableSafety?.isSome)
  , ("failure_detector_boundaries", pack.failureDetectors?.isSome)
  , ("data_availability_retrievability", pack.dataAvailability?.isSome)
  , ("coordination_characterization", pack.coordination?.isSome)
  , ("crdt_envelope_and_equivalence", pack.crdt?.isSome)
  , ("byzantine_safety_characterization", pack.byzantineSafety?.isSome)
  , ("consensus_envelope", pack.consensusEnvelope?.isSome)
  , ("failure_envelope", pack.failureEnvelope?.isSome)
  , ("protocol_machine_envelope_adherence", pack.vmEnvelopeAdherence?.isSome)
  , ("protocol_machine_envelope_admission", pack.vmEnvelopeAdmission?.isSome)
  , ("protocol_envelope_bridge", pack.protocolEnvelopeBridge?.isSome)
  , ("effect_interface_bridge",
      pack.vmEnvelopeAdherence?.isSome && pack.protocolEnvelopeBridge?.isSome)
  , ("classical_foster", pack.foster?.isSome)
  , ("classical_maxweight", pack.maxWeight?.isSome)
  , ("classical_ldp", pack.ldp?.isSome)
  , ("classical_mean_field", pack.meanField?.isSome)
  , ("classical_heavy_traffic", pack.heavyTraffic?.isSome)
  , ("classical_mixing", pack.mixing?.isSome)
  , ("classical_fluid", pack.fluid?.isSome)
  , ("classical_concentration", pack.concentration?.isSome)
  , ("classical_littles_law", pack.littlesLaw?.isSome)
  , ("classical_functional_clt", pack.functionalCLT?.isSome)
  ] ++ semanticObjectInventory (pack := pack)

/-! ## Determinism Extension -/

/-- Theorem inventory extended with determinism artifacts. -/
def theoremInventoryWithDeterminism
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : ProtocolMachineTheoremPack (space := space))
    (determinism : ProtocolMachineDeterminismArtifacts) : List (String × Bool) :=
  theoremInventory (space := space) pack ++
    determinismInventory determinism

end

end Proofs
end Runtime
