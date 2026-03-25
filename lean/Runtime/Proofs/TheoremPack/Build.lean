
import Runtime.Proofs.TheoremPack.Artifacts

/-! # Theorem Pack Building

`ProtocolMachineTheoremPack` structure bundling all optional proof artifacts for
a protocol machine invariant space, enabling certificate generation and validation. -/

/-
The Problem. Protocol verification may prove various properties (FLP,
CAP, termination, envelope adherence, etc.). We need a single structure
bundling all available proof artifacts for a given protocol machine configuration.

Solution Structure. Define `ProtocolMachineTheoremPack` with optional fields for
each artifact type. The pack is parameterized by a `ProtocolMachineInvariantSpace-
WithProfiles` providing the base invariant and profile structure.
-/

/- ## Structured Block 1 -/
set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]


-- Theorem Pack Structure

structure ProtocolMachineTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) where
  termination? : Option (TerminationArtifact (ν := ν) (store₀ := store₀))
  outputCondition? : Option OutputConditionArtifact
  semanticObjects? : Option SemanticObjectArtifacts
  flpLowerBound? : Option FLPLowerBoundArtifact
  flpImpossibility? : Option FLPImpossibilityArtifact
  capImpossibility? : Option CAPImpossibilityArtifact
  quorumGeometry? : Option QuorumGeometryArtifact
  partialSynchrony? : Option PartialSynchronyArtifact
  responsiveness? : Option ResponsivenessArtifact
  nakamoto? : Option NakamotoArtifact
  reconfiguration? : Option ReconfigurationArtifact
  atomicBroadcast? : Option AtomicBroadcastArtifact
  accountableSafety? : Option AccountableSafetyArtifact
  failureDetectors? : Option FailureDetectorsArtifact
  dataAvailability? : Option DataAvailabilityArtifact
  coordination? : Option CoordinationArtifact
  crdt? : Option CRDTArtifact
  byzantineSafety? : Option ByzantineSafetyArtifact
  consensusEnvelope? : Option ConsensusEnvelopeArtifact
  failureEnvelope? : Option FailureEnvelopeArtifact
  protocolMachineEnvelopeAdherence? : Option ProtocolMachineEnvelopeAdherenceArtifact
  protocolMachineEnvelopeAdmission? : Option ProtocolMachineEnvelopeAdmissionArtifact
  protocolEnvelopeBridge? : Option ProtocolEnvelopeBridgeArtifact
  proofCarryingMetadata : ProofCarryingArtifactMetadata
  foster? : Option (Adapters.FosterArtifact State)
  maxWeight? : Option Adapters.MaxWeightArtifact
  ldp? : Option Adapters.LDPArtifact
  meanField? : Option Adapters.MeanFieldArtifact
  heavyTraffic? : Option Adapters.HeavyTrafficArtifact
  mixing? : Option Adapters.MixingArtifact
  fluid? : Option Adapters.FluidArtifact
  concentration? : Option Adapters.ConcentrationArtifact
  littlesLaw? : Option Adapters.LittlesLawArtifact
  functionalCLT? : Option Adapters.FunctionalCLTArtifact

-- Builder

/-- Build theorem artifacts from one invariant space. -/
def buildProtocolMachineTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    ProtocolMachineTheoremPack space :=
  let termination? :=
    match space.toProtocolMachineInvariantSpace.liveness? with
    | none => none
    | some bundle =>
        some
/- ## Structured Block 2 -/
          { bundle := bundle
          , proof := by
              simpa using protocol_machine_termination_from_bundle (bundle := bundle)
          }
  let outputCondition? :=
    match space.toProtocolMachineInvariantSpace.outputConditionWitness? with
    | none => none
    | some w =>
        some
          { witness := w
          , soundness := w.sound
          }
  let semanticObjects? :=
    space.toProtocolMachineInvariantSpace.semanticObjectWitnesses?.map
      SemanticObjectArtifacts.ofWitnessBundle

  -- Builder: Distributed Impossibility and Quorum

  let flpLowerBound? :=
    match space.distributed.flp? with
    | none => none
    | some p => some { protocol := p, proof := p.lowerBound }
  let flpImpossibility? :=
    match space.distributed.flp? with
    | none => none
    | some p => some { protocol := p, proof := p.impossibility }
  let capImpossibility? :=
    match space.distributed.cap? with
    | none => none
    | some p => some { protocol := p, proof := p.impossibility }
  let quorumGeometry? :=
    match space.distributed.quorumGeometry? with
    | none => none
    | some p =>
        some
          { protocol := p
          , noConflictingCommits := p.noConflictingCommits
          , forkExclusion := p.forkExclusion
          , safeFinality := p.safeFinality
          }

  -- Builder: Liveness and Responsiveness

  let partialSynchrony? :=
    match space.distributed.partialSynchrony? with
    | none => none
    | some p =>
        some
          { protocol := p
          , eventualDecision := p.eventualDecision
          , boundedPostGST := p.boundedPostGST
          }
  let responsiveness? :=
    match space.distributed.responsiveness? with
    | none => none
    | some p =>
        some
          { protocol := p
          , eventualDecision := p.eventualDecision
/- ## Structured Block 3 -/
          , timeoutIndependentLatency := p.timeoutIndependentLatency
          }
  let nakamoto? :=
    match space.distributed.nakamoto? with
    | none => none
    | some p =>
        some
          { protocol := p
          , probabilisticSafety := p.probabilisticSafety
          , settlementFinality := p.settlementFinality
          , livenessUnderChurn := p.livenessUnderChurn
          }
  let reconfiguration? :=
    match space.distributed.reconfiguration? with
    | none => none
    | some p =>
        some
          { protocol := p
          , noSplitBrain := p.noSplitBrain
          , safeHandoff := p.safeHandoff
          , livenessPreserved := p.livenessPreserved
          }
  let atomicBroadcast? :=
    match space.distributed.atomicBroadcast? with
    | none => none
    | some p =>
        some
          { protocol := p
          , totalOrderConsistency := p.totalOrderConsistency
          , logPrefixCompatibility := p.logPrefixCompatibility
          , consensusAtomicBroadcastBridge := p.consensusAtomicBroadcastBridge
          }

  -- Builder: Safety Boundaries and Availability

  let accountableSafety? :=
    match space.distributed.accountableSafety? with
    | none => none
    | some p =>
        some
          { protocol := p
          , accountableSafety := p.accountableSafety
          }
  let failureDetectors? :=
    match space.distributed.failureDetectors? with
    | none => none
    | some p =>
        some
          { protocol := p
          , solvabilityBoundary := p.solvabilityBoundary
          , impossibilityBoundary := p.impossibilityBoundary
          }
  let dataAvailability? :=
/- ## Structured Block 4 -/
    match space.distributed.dataAvailability? with
    | none => none
    | some p =>
        some
          { protocol := p
          , availability := p.availability
          , retrievability := p.retrievability
          }
  let coordination? :=
    match space.distributed.coordination? with
    | none => none
    | some p =>
        some
          { protocol := p
          , characterization := p.characterization
          }

  -- Builder: CRDT and Consensus Envelope Families

  let crdt? :=
    match space.distributed.crdt? with
    | none => none
    | some p =>
        some
          { protocol := p
          , exactEnvelope := p.exactEnvelope
          , adequacy := p.adequacy
          , principalCapability := p.principalCapability
          , admissionSoundness := p.admissionSoundness
          , admissionCompleteness := p.admissionCompleteness
          , opStateEquivalence := p.opStateEquivalence
          , gcSafetyIff := p.gcSafetyIffCausalDominance
          , boundedApproximation := p.boundedApproximation
          , approximationMonotonicity := p.approximationMonotonicity
          , exactSECAsLimit := p.exactSECAsLimit
          , hcrdtCore := p.hcrdtCore
          , hcrdtFoundation := p.hcrdtFoundation
          , hcrdtDynamics := p.hcrdtDynamics
          , hcrdtExtensions := p.hcrdtExtensions
          , hcrdtLimits := p.hcrdtLimits
          }

  -- Builder: Byzantine and Consensus Envelope Families

  let byzantineSafety? :=
    match space.distributed.byzantineSafety? with
    | none => none
    | some p =>
        some
          { protocol := p
          , exactCharacterization := p.exactCharacterization
          , byzantineSafety := Distributed.ByzantineSafety.byzantine_safety_of_protocol p
          , characterization := Distributed.ByzantineSafety.characterization_of_protocol p
          , assumptionsPassed := Distributed.ByzantineSafety.byzantine_assumptions_all_passed p
          }
  let consensusEnvelope? :=
/- ## Structured Block 5 -/
    match space.distributed.consensusEnvelope? with
    | none => none
    | some p =>
        some
          { protocol := p
          , exactEnvelope := p.exactEnvelope
          , adequacy := p.adequacy
          , principalCapability := p.principalCapability
          , admissionSoundness := p.admissionSoundness
          , admissionCompleteness := p.admissionCompleteness
          }
  let failureEnvelope? :=
    match space.distributed.failureEnvelope? with
    | none => none
    | some p =>
        some
          { protocol := p
          , recoveryActionSafety := p.recoveryActionSafety
          , noUnsafeReplay := p.noUnsafeReplay
          , checkpointRestartRefinement := p.checkpointRestartRefinement
          , crossTargetConformance := p.crossTargetConformance
          , restartStructuredErrorAdequacy := p.restartStructuredErrorAdequacy
          , failureEnvelopeSoundness := p.failureEnvelopeSoundness
          , failureEnvelopeMaximality := p.failureEnvelopeMaximality
          }

  -- Builder: protocol machine Envelope Families

  let protocolMachineEnvelopeAdherence? :=
    match space.distributed.protocolMachineEnvelopeAdherence? with
    | none => none
    | some p =>
        some
          { protocol := p
          , localAdherence := p.localAdherence
          , shardedAdherence := p.shardedAdherence
          , schedulerDeterminismLocal := p.schedulerDeterminismLocal
          , schedulerDeterminismSharded := p.schedulerDeterminismSharded
          , monotonicity := p.monotonicity
          , localAdequacy := p.localAdequacy
          , shardedAdequacy := p.shardedAdequacy
          , localFullAbstraction := p.localFullAbstraction
          , shardedFullAbstraction := p.shardedFullAbstraction
          , capabilityMonotonicity := p.capabilityMonotonicity
          }
  let protocolMachineEnvelopeAdmission? :=
    match space.distributed.protocolMachineEnvelopeAdmission? with
    | none => none
    | some p =>
        some
          { protocol := p
          , localInferenceSoundness := p.localInferenceSoundness
          , shardedInferenceSoundness := p.shardedInferenceSoundness
/- ## Structured Block 6 -/
          , localPrincipalCapability := p.localPrincipalCapability
          , shardedPrincipalCapability := p.shardedPrincipalCapability
          , localAdmissionSoundness := p.localAdmissionSoundness
          , localAdmissionCompleteness := p.localAdmissionCompleteness
          , shardedAdmissionSoundness := p.shardedAdmissionSoundness
          , shardedAdmissionCompleteness := p.shardedAdmissionCompleteness
          , decidability := p.decidability
          , complexity := p.complexity
          , conservativeExtension := p.conservativeExtension
          , necessityMinimality := p.necessityMinimality
          }

  -- Builder: Protocol Bridge and Classical Pack

  let protocolEnvelopeBridge? :=
    match space.distributed.protocolEnvelopeBridge? with
    | none => none
    | some p =>
        some
          { profile := p
          , roleRenamingInvariant := p.bundle.roleRenamingInvariant
          , compositionalEnvelope := p.bundle.compositionalEnvelope
          , delegationPreserves := p.bundle.delegationPreserves
          , spatialMonotonicity := p.bundle.spatialMonotonicity
          , exchangeNormalization := p.bundle.exchangeNormalization
          , shardCutPreservation := p.bundle.shardCutPreservation
          }
  let classicalPack := Adapters.buildProtocolMachineClassicalTheoremPack (space := space.toClassicalSpace)
  let proofCarryingMetadata :=
    ProofCarryingArtifactMetadata.ofInvariantSpace
      (space := space)
      semanticObjects?
      protocolMachineEnvelopeAdherence?.isSome
      protocolMachineEnvelopeAdmission?.isSome
      protocolEnvelopeBridge?.isSome
  { termination? := termination?
  , outputCondition? := outputCondition?
  , semanticObjects? := semanticObjects?
  , flpLowerBound? := flpLowerBound?
  , flpImpossibility? := flpImpossibility?
  , capImpossibility? := capImpossibility?
  , quorumGeometry? := quorumGeometry?
  , partialSynchrony? := partialSynchrony?
  , responsiveness? := responsiveness?
  , nakamoto? := nakamoto?
  , reconfiguration? := reconfiguration?
  , atomicBroadcast? := atomicBroadcast?
  , accountableSafety? := accountableSafety?
  , failureDetectors? := failureDetectors?
  , dataAvailability? := dataAvailability?
  , coordination? := coordination?
  , crdt? := crdt?
  , byzantineSafety? := byzantineSafety?
  , consensusEnvelope? := consensusEnvelope?
  , failureEnvelope? := failureEnvelope?
  , protocolMachineEnvelopeAdherence? := protocolMachineEnvelopeAdherence?
  , protocolMachineEnvelopeAdmission? := protocolMachineEnvelopeAdmission?
  , protocolEnvelopeBridge? := protocolEnvelopeBridge?
  , proofCarryingMetadata := proofCarryingMetadata
  , foster? := classicalPack.foster?
  , maxWeight? := classicalPack.maxWeight?
  , ldp? := classicalPack.ldp?
/- ## Structured Block 7 -/
  , meanField? := classicalPack.meanField?
  , heavyTraffic? := classicalPack.heavyTraffic?
  , mixing? := classicalPack.mixing?
  , fluid? := classicalPack.fluid?
  , concentration? := classicalPack.concentration?
  , littlesLaw? := classicalPack.littlesLaw?
  , functionalCLT? := classicalPack.functionalCLT?
  }

/-- Theorem-pack adherence artifact presence matches the canonical execution-profile flag. -/
theorem protocolMachineEnvelopeAdherence_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).protocolMachineEnvelopeAdherence?.isSome =
      space.executionProfile.supportsProtocolMachineEnvelopeAdherence := by
  cases h : space.distributed.protocolMachineEnvelopeAdherence? <;>
    simp [buildProtocolMachineTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsProtocolMachineEnvelopeAdherence, h]

/-- Theorem-pack admission artifact presence matches the canonical execution-profile flag. -/
theorem protocolMachineEnvelopeAdmission_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).protocolMachineEnvelopeAdmission?.isSome =
      space.executionProfile.supportsProtocolMachineEnvelopeAdmission := by
  cases h : space.distributed.protocolMachineEnvelopeAdmission? <;>
    simp [buildProtocolMachineTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsProtocolMachineEnvelopeAdmission, h]

/-- Theorem-pack bridge artifact presence matches the canonical execution-profile flag. -/
theorem protocolEnvelopeBridge_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).protocolEnvelopeBridge?.isSome =
      space.executionProfile.supportsProtocolEnvelopeBridge := by
  cases h : space.distributed.protocolEnvelopeBridge? <;>
    simp [buildProtocolMachineTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsProtocolEnvelopeBridge, h]

end

end Proofs
end Runtime
