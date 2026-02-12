import Runtime.Proofs.TheoremPack.Artifacts

/-! # Theorem Pack Building

`VMTheoremPack` structure bundling all optional proof artifacts for
a VM invariant space, enabling certificate generation and validation. -/

/-
The Problem. Protocol verification may prove various properties (FLP,
CAP, termination, envelope adherence, etc.). We need a single structure
bundling all available proof artifacts for a given VM configuration.

Solution Structure. Define `VMTheoremPack` with optional fields for
each artifact type. The pack is parameterized by a `VMInvariantSpace-
WithProfiles` providing the base invariant and profile structure.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-! ## Theorem Pack Structure -/

structure VMTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) where
  termination? : Option (TerminationArtifact (ν := ν) (store₀ := store₀))
  outputCondition? : Option OutputConditionArtifact
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
  consensusEnvelope? : Option ConsensusEnvelopeArtifact
  failureEnvelope? : Option FailureEnvelopeArtifact
  vmEnvelopeAdherence? : Option VMEnvelopeAdherenceArtifact
  vmEnvelopeAdmission? : Option VMEnvelopeAdmissionArtifact
  protocolEnvelopeBridge? : Option ProtocolEnvelopeBridgeArtifact
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

/-- Build theorem artifacts from one invariant space. -/
def buildVMTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    VMTheoremPack space :=
  let termination? :=
    match space.toVMInvariantSpace.liveness? with
    | none => none
    | some bundle =>
        some
          { bundle := bundle
          , proof := by
              simpa using vm_termination_from_bundle (bundle := bundle)
          }
  let outputCondition? :=
    match space.toVMInvariantSpace.outputConditionWitness? with
    | none => none
    | some w =>
        some
          { witness := w
          , soundness := w.sound
          }
  let flpLowerBound? :=
    match space.distributed.flp? with
    | none => none
    | some p => some { protocol := p.protocol, proof := p.protocol.lowerBound }
  let flpImpossibility? :=
    match space.distributed.flp? with
    | none => none
    | some p => some { protocol := p.protocol, proof := p.protocol.impossibility }
  let capImpossibility? :=
    match space.distributed.cap? with
    | none => none
    | some p => some { protocol := p.protocol, proof := p.protocol.impossibility }
  let quorumGeometry? :=
    match space.distributed.quorumGeometry? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , noConflictingCommits := p.protocol.noConflictingCommits
          , forkExclusion := p.protocol.forkExclusion
          , safeFinality := p.protocol.safeFinality
          }
  let partialSynchrony? :=
    match space.distributed.partialSynchrony? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , eventualDecision := p.protocol.eventualDecision
          , boundedPostGST := p.protocol.boundedPostGST
          }
  let responsiveness? :=
    match space.distributed.responsiveness? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , eventualDecision := p.protocol.eventualDecision
          , timeoutIndependentLatency := p.protocol.timeoutIndependentLatency
          }
  let nakamoto? :=
    match space.distributed.nakamoto? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , probabilisticSafety := p.protocol.probabilisticSafety
          , settlementFinality := p.protocol.settlementFinality
          , livenessUnderChurn := p.protocol.livenessUnderChurn
          }
  let reconfiguration? :=
    match space.distributed.reconfiguration? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , noSplitBrain := p.protocol.noSplitBrain
          , safeHandoff := p.protocol.safeHandoff
          , livenessPreserved := p.protocol.livenessPreserved
          }
  let atomicBroadcast? :=
    match space.distributed.atomicBroadcast? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , totalOrderConsistency := p.protocol.totalOrderConsistency
          , logPrefixCompatibility := p.protocol.logPrefixCompatibility
          , consensusAtomicBroadcastBridge := p.protocol.consensusAtomicBroadcastBridge
          }
  let accountableSafety? :=
    match space.distributed.accountableSafety? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , accountableSafety := p.protocol.accountableSafety
          }
  let failureDetectors? :=
    match space.distributed.failureDetectors? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , solvabilityBoundary := p.protocol.solvabilityBoundary
          , impossibilityBoundary := p.protocol.impossibilityBoundary
          }
  let dataAvailability? :=
    match space.distributed.dataAvailability? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , availability := p.protocol.availability
          , retrievability := p.protocol.retrievability
          }
  let coordination? :=
    match space.distributed.coordination? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , characterization := p.protocol.characterization
          }
  let crdt? :=
    match space.distributed.crdt? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , exactEnvelope := p.protocol.exactEnvelope
          , adequacy := p.protocol.adequacy
          , principalCapability := p.protocol.principalCapability
          , admissionSoundness := p.protocol.admissionSoundness
          , admissionCompleteness := p.protocol.admissionCompleteness
          , opStateEquivalence := p.protocol.opStateEquivalence
          , gcSafetyIff := p.protocol.gcSafetyIffCausalDominance
          , boundedApproximation := p.protocol.boundedApproximation
          , approximationMonotonicity := p.protocol.approximationMonotonicity
          , exactSECAsLimit := p.protocol.exactSECAsLimit
          , hcrdtCore := p.protocol.hcrdtCore
          , hcrdtFoundation := p.protocol.hcrdtFoundation
          , hcrdtDynamics := p.protocol.hcrdtDynamics
          , hcrdtExtensions := p.protocol.hcrdtExtensions
          , hcrdtLimits := p.protocol.hcrdtLimits
          }
  let consensusEnvelope? :=
    match space.distributed.consensusEnvelope? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , exactEnvelope := p.protocol.exactEnvelope
          , adequacy := p.protocol.adequacy
          , principalCapability := p.protocol.principalCapability
          , admissionSoundness := p.protocol.admissionSoundness
          , admissionCompleteness := p.protocol.admissionCompleteness
          }
  let failureEnvelope? :=
    match space.distributed.failureEnvelope? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , recoveryActionSafety := p.protocol.recoveryActionSafety
          , noUnsafeReplay := p.protocol.noUnsafeReplay
          , checkpointRestartRefinement := p.protocol.checkpointRestartRefinement
          , crossTargetConformance := p.protocol.crossTargetConformance
          , restartStructuredErrorAdequacy := p.protocol.restartStructuredErrorAdequacy
          , failureEnvelopeSoundness := p.protocol.failureEnvelopeSoundness
          , failureEnvelopeMaximality := p.protocol.failureEnvelopeMaximality
          }
  let vmEnvelopeAdherence? :=
    match space.distributed.vmEnvelopeAdherence? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , localAdherence := p.protocol.localAdherence
          , shardedAdherence := p.protocol.shardedAdherence
          , schedulerDeterminismLocal := p.protocol.schedulerDeterminismLocal
          , schedulerDeterminismSharded := p.protocol.schedulerDeterminismSharded
          , monotonicity := p.protocol.monotonicity
          , localAdequacy := p.protocol.localAdequacy
          , shardedAdequacy := p.protocol.shardedAdequacy
          , localFullAbstraction := p.protocol.localFullAbstraction
          , shardedFullAbstraction := p.protocol.shardedFullAbstraction
          , capabilityMonotonicity := p.protocol.capabilityMonotonicity
          }
  let vmEnvelopeAdmission? :=
    match space.distributed.vmEnvelopeAdmission? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , localInferenceSoundness := p.protocol.localInferenceSoundness
          , shardedInferenceSoundness := p.protocol.shardedInferenceSoundness
          , localPrincipalCapability := p.protocol.localPrincipalCapability
          , shardedPrincipalCapability := p.protocol.shardedPrincipalCapability
          , localAdmissionSoundness := p.protocol.localAdmissionSoundness
          , localAdmissionCompleteness := p.protocol.localAdmissionCompleteness
          , shardedAdmissionSoundness := p.protocol.shardedAdmissionSoundness
          , shardedAdmissionCompleteness := p.protocol.shardedAdmissionCompleteness
          , decidability := p.protocol.decidability
          , complexity := p.protocol.complexity
          , conservativeExtension := p.protocol.conservativeExtension
          , necessityMinimality := p.protocol.necessityMinimality
          }
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
  let classicalPack := Adapters.buildVMClassicalTheoremPack (space := space.toClassicalSpace)
  { termination? := termination?
  , outputCondition? := outputCondition?
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
  , consensusEnvelope? := consensusEnvelope?
  , failureEnvelope? := failureEnvelope?
  , vmEnvelopeAdherence? := vmEnvelopeAdherence?
  , vmEnvelopeAdmission? := vmEnvelopeAdmission?
  , protocolEnvelopeBridge? := protocolEnvelopeBridge?
  , foster? := classicalPack.foster?
  , maxWeight? := classicalPack.maxWeight?
  , ldp? := classicalPack.ldp?
  , meanField? := classicalPack.meanField?
  , heavyTraffic? := classicalPack.heavyTraffic?
  , mixing? := classicalPack.mixing?
  , fluid? := classicalPack.fluid?
  , concentration? := classicalPack.concentration?
  , littlesLaw? := classicalPack.littlesLaw?
  , functionalCLT? := classicalPack.functionalCLT?
  }

end

end Proofs
end Runtime
