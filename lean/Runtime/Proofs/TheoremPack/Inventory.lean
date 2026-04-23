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

/-- Proof-carrying artifact metadata inventory extracted from one theorem pack. -/
def proofCarryingMetadataInventory
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : ProtocolMachineTheoremPack (space := space)) : List (String × Bool) :=
  [ ("profile_fairness_schedule_confluence",
      ProtocolMachineFairnessAssumption.scheduleConfluence ∈
        pack.proofCarryingMetadata.profile.executionProfile.fairnessAssumptions)
  , ("profile_fairness_starvation_freedom",
      ProtocolMachineFairnessAssumption.starvationFreedom ∈
        pack.proofCarryingMetadata.profile.executionProfile.fairnessAssumptions)
  , ("profile_progress_contract_bounded",
      ProtocolMachineEscalationWindowClass.progressContractBounded ∈
        pack.proofCarryingMetadata.profile.executionProfile.escalationWindowClasses)
  , ("profile_protocol_bridge_bounded",
      ProtocolMachineEscalationWindowClass.protocolBridgeBounded ∈
        pack.proofCarryingMetadata.profile.executionProfile.escalationWindowClasses)
  , ("metadata_requires_explicit_progress_contracts",
      pack.proofCarryingMetadata.progress.requiresExplicitProgressContracts)
  , ("metadata_parity_critical_progress_protected",
      pack.proofCarryingMetadata.progress.parityCriticalOperationsProtected)
  , ("metadata_failure_taxonomy_linked",
      pack.proofCarryingMetadata.progress.failureTaxonomyLinked)
  , ("metadata_protocol_machine_envelope_adherence",
      pack.proofCarryingMetadata.envelope.protocolMachineEnvelopeAdherence)
  , ("metadata_protocol_machine_envelope_admission",
      pack.proofCarryingMetadata.envelope.protocolMachineEnvelopeAdmission)
  , ("metadata_protocol_envelope_bridge",
      pack.proofCarryingMetadata.envelope.protocolEnvelopeBridge)
  , ("metadata_envelope_adequacy_linked",
      pack.proofCarryingMetadata.envelope.adequacyLinked)
  , ("metadata_envelope_adherence_linked",
      pack.proofCarryingMetadata.envelope.adherenceLinked)
  ]

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
  , ("calm_characterization", pack.calm?.isSome)
  , ("crdt_envelope_and_equivalence", pack.crdt?.isSome)
  , ("crdt_monotonicity", pack.crdtMonotonicity?.isSome)
  , ("triangle_of_forgetting_impossibility", pack.triangleOfForgetting?.isSome)
  , ("byzantine_safety_characterization", pack.byzantineSafety?.isSome)
  , ("consensus_envelope", pack.consensusEnvelope?.isSome)
  , ("failure_envelope", pack.failureEnvelope?.isSome)
  , ("protocol_machine_envelope_adherence", pack.protocolMachineEnvelopeAdherence?.isSome)
  , ("protocol_machine_envelope_admission", pack.protocolMachineEnvelopeAdmission?.isSome)
  , ("protocol_envelope_bridge", pack.protocolEnvelopeBridge?.isSome)
  , ("effect_interface_bridge",
      pack.protocolMachineEnvelopeAdherence?.isSome && pack.protocolEnvelopeBridge?.isSome)
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
  , ("classical_spectral_gap_termination", pack.spectralGapTermination?.isSome)
  ] ++ semanticObjectInventory (pack := pack) ++
    proofCarryingMetadataInventory (pack := pack)

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
