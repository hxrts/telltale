
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
  calm? : Option CALMArtifact
  crdt? : Option CRDTArtifact
  crdtMonotonicity? : Option CRDTMonotonicityArtifact
  crdtErasure? : Option CRDTErasureArtifact
  triangleOfForgetting? : Option TriangleOfForgettingArtifact
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
          { condition := w
          , soundness := w.sound
          }
  let semanticObjects? :=
    space.toProtocolMachineInvariantSpace.semanticObjectWitnesses?.map
      SemanticObjectArtifacts.ofWitnessBundle

  -- Builder: Distributed Impossibility and Quorum

  let flpLowerBound? :=
    match space.distributed.flp? with
    | none => none
    | some p => some
        { protocol := p
        , proof := Distributed.FLP.lower_bound_of_assumptions
            p.assumptions p.premises.toLowerBoundPremises
        }
  let flpImpossibility? :=
    match space.distributed.flp? with
    | none => none
    | some p => some { protocol := p, proof := Distributed.FLP.impossibility_of_protocol p }
  let capImpossibility? :=
    match space.distributed.cap? with
    | none => none
    | some p => some { protocol := p, proof := Distributed.CAP.impossibility_of_protocol p }
  let quorumGeometry? :=
    match space.distributed.quorumGeometry? with
    | none => none
    | some p =>
        some
          { protocol := p
          , noConflictingCommits := Distributed.QuorumGeometry.no_conflicting_commits_of_protocol p
          , forkExclusion := Distributed.QuorumGeometry.fork_exclusion_of_protocol p
          , safeFinality := Distributed.QuorumGeometry.safe_finality_of_protocol p
          }

  -- Builder: Liveness and Responsiveness

  let partialSynchrony? :=
    match space.distributed.partialSynchrony? with
    | none => none
    | some p =>
        some
          { protocol := p
          , eventualDecision := Distributed.PartialSynchrony.eventual_decision_of_protocol p
          , boundedPostGST := Distributed.PartialSynchrony.bounded_post_gst_of_protocol p
          }
  let responsiveness? :=
    match space.distributed.responsiveness? with
    | none => none
    | some p =>
        some
          { protocol := p
          , eventualDecision := Distributed.Responsiveness.eventual_decision_of_protocol p
/- ## Structured Block 3 -/
          , timeoutIndependentLatency := Distributed.Responsiveness.timeout_independent_latency_of_protocol p
          }
  let nakamoto? :=
    match space.distributed.nakamoto? with
    | none => none
    | some p =>
        some
          { protocol := p
          , probabilisticSafety := Distributed.Nakamoto.probabilistic_safety_of_protocol p
          , settlementFinality := Distributed.Nakamoto.settlement_finality_of_protocol p
          , livenessUnderChurn := Distributed.Nakamoto.liveness_under_churn_of_protocol p
          }
  let reconfiguration? :=
    match space.distributed.reconfiguration? with
    | none => none
    | some p =>
        some
          { protocol := p
          , noSplitBrain := Distributed.Reconfiguration.no_split_brain_of_protocol p
          , safeHandoff := Distributed.Reconfiguration.safe_handoff_of_protocol p
          , livenessPreserved := Distributed.Reconfiguration.liveness_preserved_of_protocol p
          }
  let atomicBroadcast? :=
    match space.distributed.atomicBroadcast? with
    | none => none
    | some p =>
        some
          { protocol := p
          , totalOrderConsistency := Distributed.AtomicBroadcast.total_order_consistency_of_protocol p
          , logPrefixCompatibility := Distributed.AtomicBroadcast.log_prefix_compatibility_of_protocol p
          , consensusAtomicBroadcastBridge := Distributed.AtomicBroadcast.bridge_of_protocol p
          }

  -- Builder: Safety Boundaries and Availability

  let accountableSafety? :=
    match space.distributed.accountableSafety? with
    | none => none
    | some p =>
        some
          { protocol := p
          , accountableSafety := Distributed.AccountableSafety.accountable_safety_of_protocol p
          }
  let failureDetectors? :=
    match space.distributed.failureDetectors? with
    | none => none
    | some p =>
        some
          { protocol := p
          , solvabilityBoundary := Distributed.FailureDetectors.solvability_boundary_of_protocol p
          , impossibilityBoundary := Distributed.FailureDetectors.impossibility_boundary_of_protocol p
          }
  let dataAvailability? :=
/- ## Structured Block 4 -/
    match space.distributed.dataAvailability? with
    | none => none
    | some p =>
        some
          { protocol := p
          , availability := Distributed.DataAvailability.availability_of_protocol p
          , retrievability := Distributed.DataAvailability.retrievability_of_protocol p
          }
  let coordination? :=
    match space.distributed.coordination? with
    | none => none
    | some p =>
        some
          { protocol := p
          , characterization := Distributed.Coordination.characterization_of_protocol p
          }
  let calm? :=
    match space.distributed.coordination? with
    | none => none
    | some p =>
        some
          { protocol := p
          , characterization := Distributed.Coordination.characterization_of_protocol p
          , coordinationFreeWhenMonotone := Distributed.Coordination.coordination_free_of_monotone p
          , coordinationRequiredWhenNonMonotone :=
              Distributed.Coordination.coordination_required_of_non_monotone p
          }

  -- Builder: CRDT and Consensus Envelope Families

  let crdt? :=
    match space.distributed.crdt? with
    | none => none
    | some p =>
        some
          { protocol := p
          , exactEnvelope := Distributed.CRDT.exact_envelope_of_protocol p
          , adequacy := Distributed.CRDT.adequacy_of_protocol p
          , principalCapability := Distributed.CRDT.principal_capability_of_protocol p
          , admissionSoundness := Distributed.CRDT.admission_soundness_of_protocol p
          , admissionCompleteness := Distributed.CRDT.admission_completeness_of_protocol p
          , opStateEquivalence := Distributed.CRDT.op_state_equivalence_of_protocol p
          , gcSafetyIff := Distributed.CRDT.gc_safety_iff_of_protocol p
          , boundedApproximation := Distributed.CRDT.bounded_approximation_of_protocol p
          , approximationMonotonicity := Distributed.CRDT.approximation_monotone_of_protocol p
          , exactSECAsLimit := Distributed.CRDT.exact_sec_as_limit_of_protocol p
          , hcrdtCore := Distributed.CRDT.hcrdt_core_of_protocol p
          , hcrdtFoundation := Distributed.CRDT.hcrdt_foundation_of_protocol p
          , hcrdtDynamics := Distributed.CRDT.hcrdt_dynamics_of_protocol p
          , hcrdtExtensions := Distributed.CRDT.hcrdt_extensions_of_protocol p
          , hcrdtLimits := Distributed.CRDT.hcrdt_limits_of_protocol p
          }
  let crdtMonotonicity? :=
    match space.distributed.crdt? with
    | none => none
    | some p =>
        some
          { protocol := p
          , semilatticeCore := p.assumptions.semilatticeCoreClass
          , opContextLayer := p.assumptions.opContextLayerClass
          , mergeInflationary :=
              Distributed.CRDT.merge_inflationary_of_state_based_crdt p.premises.stateSemantics
          , mergeMonotone :=
              Distributed.CRDT.merge_monotone_of_state_based_crdt p.premises.stateSemantics
          , strongEventualConvergence :=
              Distributed.CRDT.strong_eventual_convergence_of_state_based_crdt
                p.premises.stateSemantics
          , finiteCausalDeliveryConverges :=
              Distributed.CRDT.finite_causal_delivery_converges_of_state_based_crdt
                p.premises.stateSemantics
          , approximationMonotonicity := Distributed.CRDT.approximation_monotone_of_protocol p
          , hcrdtCore := Distributed.CRDT.hcrdt_core_of_protocol p
          }
  let crdtErasure? :=
    match space.distributed.crdtErasure? with
    | none => none
    | some p =>
        some
          { protocol := p
          , weakestOpCoreErasure := p.weakestOpCoreErasure
          , replayStable := p.replayStable
          , serializationInvariant := p.serializationInvariant
          , conformanceGateIffLowered := p.conformanceGateIffLowered
          }
  let triangleOfForgetting? :=
    match space.distributed.triangleOfForgetting? with
    | none => none
    | some p =>
        some
          { protocol := p
          , proof := Distributed.TriangleOfForgetting.impossibility_of_protocol p
          }

  -- Builder: Byzantine and Consensus Envelope Families

  let byzantineSafety? :=
    match space.distributed.byzantineSafety? with
    | none => none
    | some p =>
        some
          { protocol := p
          , exactCharacterization := Distributed.ByzantineSafety.exact_characterization_of_protocol p
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
          , exactEnvelope := Distributed.ConsensusEnvelope.exact_envelope_of_protocol p
          , adequacy := Distributed.ConsensusEnvelope.adequacy_of_protocol p
          , principalCapability := Distributed.ConsensusEnvelope.principal_capability_of_protocol p
          , admissionSoundness := Distributed.ConsensusEnvelope.admission_soundness_of_protocol p
          , admissionCompleteness := Distributed.ConsensusEnvelope.admission_completeness_of_protocol p
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
  , calm? := calm?
  , crdt? := crdt?
  , crdtMonotonicity? := crdtMonotonicity?
  , crdtErasure? := crdtErasure?
  , triangleOfForgetting? := triangleOfForgetting?
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
