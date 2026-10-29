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

/-- Proof-carrying artifact metadata inventory extracted from one theorem pack.

`profile_*` keys report declared execution-profile assumptions. `metadata_*`
keys report that a premise bundle was supplied (`*_premise_supplied`); none
of them asserts that a property was proved. -/
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
  , ("metadata_progress_contracts_premise_supplied",
      pack.proofCarryingMetadata.progress.parityCriticalOperationsProtected)
  , ("metadata_replay_failure_exactness_premise_supplied",
      pack.proofCarryingMetadata.progress.failureTaxonomyLinked)
  , ("metadata_envelope_adherence_premise_supplied",
      pack.proofCarryingMetadata.envelope.protocolMachineEnvelopeAdherence)
  , ("metadata_envelope_admission_premise_supplied",
      pack.proofCarryingMetadata.envelope.protocolMachineEnvelopeAdmission)
  , ("metadata_envelope_bridge_premise_supplied",
      pack.proofCarryingMetadata.envelope.protocolEnvelopeBridge)
  , ("metadata_adherence_or_admission_premise_supplied",
      pack.proofCarryingMetadata.envelope.adequacyLinked)
  , ("metadata_adherence_and_bridge_premise_supplied",
      pack.proofCarryingMetadata.envelope.adherenceLinked)
  ]

/-- Flat theorem-pack inventory. Each Bool is `true` iff the corresponding
artifact's premise bundle was supplied to the invariant space; it is a presence
flag, not a proof status. Key strings are consumed by Rust and kept stable. -/
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
  -- `classical_*` flags record artifact presence only; see
  -- `classicalEvidenceInventory` for which are assumed classical inputs.
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

/-! ## Classical Evidence Classification -/

/-- Honest evidence class of a `classical_*` theorem-pack entry (Option B).
An inventory flag being `true` means the artifact is *present*, not that the
named classical theorem was proved. -/
inductive ClassicalEvidenceKind where
  /-- The named classical theorem is a caller-supplied witness field; the
  artifact's conclusion is that field (nothing derived). -/
  | assumedClassicalInput
  /-- The named classical theorem is an assumed witness field; the artifact
  carries an elementary consequence derived from it. -/
  | derivedFromAssumedInput
  /-- Only an elementary identity is proved; no classical theorem is involved. -/
  | elementaryIdentity
  /-- Deterministic fact proved outright (no stochastic content). -/
  | provedDeterministic
  deriving Repr, DecidableEq, Inhabited

/-- Classification of every `classical_*` key of `theoremInventory`. -/
def classicalEvidenceInventory : List (String × ClassicalEvidenceKind) :=
  [ ("classical_foster", .provedDeterministic)
  , ("classical_maxweight", .assumedClassicalInput)
  , ("classical_ldp", .derivedFromAssumedInput)
  , ("classical_mean_field", .elementaryIdentity)
  , ("classical_heavy_traffic", .elementaryIdentity)
  , ("classical_mixing", .derivedFromAssumedInput)
  , ("classical_fluid", .derivedFromAssumedInput)
  , ("classical_concentration", .assumedClassicalInput)
  , ("classical_littles_law", .assumedClassicalInput)
  , ("classical_functional_clt", .elementaryIdentity)
  , ("classical_spectral_gap_termination", .assumedClassicalInput)
  ]

/-- Keys whose named classical theorem is an assumed (unproved) input. -/
def assumedClassicalInputKeys : List String :=
  (classicalEvidenceInventory.filter (fun e => e.2 = .assumedClassicalInput)).map Prod.fst

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
