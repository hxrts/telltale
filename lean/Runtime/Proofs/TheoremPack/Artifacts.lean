import Runtime.Proofs.TheoremPack.Profiles

/-! # Theorem Pack Artifacts

Packaged proof artifacts for distributed systems impossibility results,
quorum geometry safety, and consensus envelope theorems. -/

/-
The Problem. Theorem packs bundle proof artifacts (FLP, CAP, quorum,
etc.) for certificate generation. Each artifact type encapsulates
the protocol structure and its correctness proof in a uniform format.

Solution Structure. Define artifact structures for each theorem family:
`FLPLowerBoundArtifact`, `CAPImpossibilityArtifact`, `QuorumGeometry-
Artifact`, etc. Each bundles the protocol model with its proof term.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-! ## FLP Artifacts -/

structure FLPLowerBoundArtifact where
  protocol : Distributed.FLP.ImpossibilityProtocol
  proof : ∃ run, protocol.premises.FairRun run ∧ ∀ n, protocol.premises.Uncommitted (run n)

/-- Packaged FLP impossibility artifact. -/
structure FLPImpossibilityArtifact where
  protocol : Distributed.FLP.ImpossibilityProtocol
  proof : ¬ Distributed.FLP.TerminatesOnAllFairRuns protocol.model protocol.premises.FairRun

/-- Packaged CAP impossibility artifact. -/
structure CAPImpossibilityArtifact where
  protocol : Distributed.CAP.ImpossibilityProtocol
  proof : ¬ Distributed.CAP.CAPGuarantee protocol.model protocol.premises.PartitionRun

/-- Packaged quorum-geometry safety artifact. -/
structure QuorumGeometryArtifact where
  protocol : Distributed.QuorumGeometry.SafetyProtocol
  noConflictingCommits :
    ∀ {s d₁ d₂},
      Distributed.QuorumGeometry.Committed protocol.model s d₁ →
      Distributed.QuorumGeometry.Committed protocol.model s d₂ →
      ¬ protocol.model.conflicts d₁ d₂
  forkExclusion :
    ∀ s, ¬ Distributed.QuorumGeometry.Forked protocol.model s
  safeFinality :
    ∀ {s d},
      Distributed.QuorumGeometry.Finalized protocol.model s d →
      ∀ d', Distributed.QuorumGeometry.Committed protocol.model s d' →
        ¬ protocol.model.conflicts d d'

/-- Packaged partial-synchrony liveness artifact. -/
structure PartialSynchronyArtifact where
  protocol : Distributed.PartialSynchrony.LivenessProtocol
  eventualDecision :
    Distributed.PartialSynchrony.TerminatesOnAllFairRuns
      protocol.model protocol.premises.FairRun
  boundedPostGST :
    Distributed.PartialSynchrony.BoundedTerminationAfterGST
      protocol.model protocol.premises.FairRun
      protocol.premises.gst protocol.premises.postGSTBound

/-- Packaged responsiveness artifact. -/
structure ResponsivenessArtifact where
  protocol : Distributed.Responsiveness.ResponsiveProtocol
  eventualDecision :
    Distributed.Responsiveness.TerminatesOnAllFairRuns
      protocol.model protocol.premises.FairRun
  timeoutIndependentLatency :
    Distributed.Responsiveness.TimeoutIndependentLatencyBound
      protocol.model protocol.premises.FairRun
      protocol.premises.gst protocol.premises.optimisticBound

/-- Packaged Nakamoto-security artifact. -/
structure NakamotoArtifact where
  protocol : Distributed.Nakamoto.SecurityProtocol
  probabilisticSafety :
    Distributed.Nakamoto.ProbabilisticSafety
      protocol.model protocol.premises.AdmissibleRun protocol.premises.ε
  settlementFinality :
    Distributed.Nakamoto.SettlementDepthFinality
      protocol.model protocol.premises.AdmissibleRun protocol.premises.settlementDepth
  livenessUnderChurn :
    Distributed.Nakamoto.LivenessUnderChurn
      protocol.model protocol.premises.AdmissibleRun protocol.premises.churnBudget

/-- Packaged reconfiguration artifact. -/
structure ReconfigurationArtifact where
  protocol : Distributed.Reconfiguration.ReconfigurationProtocol
  noSplitBrain :
    Distributed.Reconfiguration.NoSplitBrainAcrossReconfiguration protocol.model
  safeHandoff :
    Distributed.Reconfiguration.SafeHandoff protocol.model
  livenessPreserved :
    Distributed.Reconfiguration.LivenessPreserved protocol.model

/-- Packaged atomic-broadcast artifact. -/
structure AtomicBroadcastArtifact where
  protocol : Distributed.AtomicBroadcast.AtomicBroadcastProtocol
  totalOrderConsistency :
    Distributed.AtomicBroadcast.TotalOrderConsistency protocol.model
  logPrefixCompatibility :
    Distributed.AtomicBroadcast.LogPrefixCompatibility protocol.model
  consensusAtomicBroadcastBridge :
    Distributed.AtomicBroadcast.ConsensusAtomicBroadcastBridge protocol.model

/-- Packaged accountable-safety artifact. -/
structure AccountableSafetyArtifact where
  protocol : Distributed.AccountableSafety.AccountableProtocol
  accountableSafety :
    Distributed.AccountableSafety.AccountableSafety protocol.model

/-- Packaged failure-detector boundary artifact. -/
structure FailureDetectorsArtifact where
  protocol : Distributed.FailureDetectors.BoundaryProtocol
  solvabilityBoundary :
    Distributed.FailureDetectors.SolvableBoundary
      protocol.model protocol.premises.detector
  impossibilityBoundary :
    Distributed.FailureDetectors.ImpossibilityBoundary
      protocol.model protocol.premises.detector

/-- Packaged data-availability artifact. -/
structure DataAvailabilityArtifact where
  protocol : Distributed.DataAvailability.DAProtocol
  availability :
    Distributed.DataAvailability.DataAvailability protocol.model
  retrievability :
    Distributed.DataAvailability.DataRetrievability protocol.model

/-- Packaged coordination-characterization artifact. -/
structure CoordinationArtifact where
  protocol : Distributed.Coordination.CoordinationProtocol
  characterization :
    Distributed.Coordination.CoordinationCharacterization protocol.model

/-- Packaged CRDT theorem-family artifact. -/
structure CRDTArtifact where
  protocol : Distributed.CRDT.CRDTProtocol
  exactEnvelope :
    Distributed.CRDT.ExactEnvelopeCharacterization
      protocol.model protocol.premises.RefRun protocol.premises.ImplRun
  adequacy :
    Distributed.CRDT.ObservationalAdequacyModuloEnvelope
      protocol.model protocol.premises.RefRun protocol.premises.ImplRun
  principalCapability :
    Distributed.CRDT.PrincipalCapability
      protocol.premises.inferredBudget protocol.premises.envelopeBudget
  admissionSoundness :
    Distributed.CRDT.AdmissionSoundness
      protocol.premises.inferredBudget protocol.premises.envelopeBudget
  admissionCompleteness :
    Distributed.CRDT.AdmissionCompleteness
      protocol.premises.inferredBudget protocol.premises.envelopeBudget
  opStateEquivalence :
    Distributed.CRDT.OpStateEquivalence
      protocol.model protocol.premises.opRun protocol.premises.stateRun
  gcSafetyIff :
    Distributed.CRDT.GCSafetyIffCausalDominance
      protocol.premises.GCSafe protocol.premises.CausalDominanceEstablished
  boundedApproximation :
    Distributed.CRDT.BoundedMetadataApproximation
      protocol.model protocol.premises.approxPolicy protocol.premises.horizon
      protocol.premises.epsilon protocol.premises.referenceRun protocol.premises.deployedRun
  approximationMonotonicity :
    Distributed.CRDT.ApproximationMonotoneUnderPolicyTightening
      protocol.model protocol.premises.approxPolicy protocol.premises.approxPolicy
      protocol.premises.horizon protocol.premises.epsilon
      protocol.premises.referenceRun protocol.premises.deployedRun
  exactSECAsLimit :
    Distributed.CRDT.ExactSECRecoveryAsLimit
      protocol.model protocol.premises.approxPolicy
      protocol.premises.referenceRun protocol.premises.deployedRun
  hcrdtCore : Distributed.CRDT.HcrdtCore protocol.model
  hcrdtFoundation : Distributed.CRDT.HcrdtFoundation protocol.model
  hcrdtDynamics : Distributed.CRDT.HcrdtDynamics protocol.model
  hcrdtExtensions : Distributed.CRDT.HcrdtExtensions protocol.model
  hcrdtLimits : Distributed.CRDT.HcrdtLimits protocol.model

/-- Packaged consensus-envelope theorem-family artifact. -/
structure ConsensusEnvelopeArtifact where
  protocol : Distributed.ConsensusEnvelope.ConsensusEnvelopeProtocol
  exactEnvelope :
    Distributed.ConsensusEnvelope.ExactEnvelopeCharacterization_consensus
      protocol.observe protocol.premises.RefRun protocol.premises.ImplRun
  adequacy :
    Distributed.ConsensusEnvelope.ObservationalAdequacyModuloEnvelope_consensus
      protocol.observe protocol.premises.RefRun protocol.premises.ImplRun
  principalCapability :
    Distributed.ConsensusEnvelope.PrincipalCapability_consensus
      protocol.premises.inferredBudget protocol.premises.envelopeBudget
  admissionSoundness :
    Distributed.ConsensusEnvelope.AdmissionSoundness_consensus
      protocol.premises.inferredBudget protocol.premises.envelopeBudget
  admissionCompleteness :
    Distributed.ConsensusEnvelope.AdmissionCompleteness_consensus
      protocol.premises.inferredBudget protocol.premises.envelopeBudget

/-- Packaged failure-envelope theorem-family artifact. -/
structure FailureEnvelopeArtifact where
  protocol : Runtime.Adequacy.FailureEnvelopeProtocol
  recoveryActionSafety :
    Runtime.Adequacy.RecoveryActionSafety
      protocol.premises.Safe protocol.premises.recoveryStep
  noUnsafeReplay :
    Runtime.Adequacy.NoUnsafeReplay
      protocol.premises.Safe protocol.premises.replayPre protocol.premises.replay
  checkpointRestartRefinement :
    Runtime.Adequacy.CheckpointRestartRefinement
      protocol.premises.Refines protocol.premises.checkpoint protocol.premises.restart
  crossTargetConformance :
    Runtime.Adequacy.CrossTargetFailureConformance
      protocol.premises.failureVisible
      protocol.premises.singleThreadRun
      protocol.premises.multiThreadRun
      protocol.premises.shardedRun
  restartStructuredErrorAdequacy :
    Runtime.Adequacy.RestartRefinementStructuredErrorAdequacy
      protocol.premises.Refines
      protocol.premises.checkpoint
      protocol.premises.restart
      protocol.premises.structuredErrors
  failureEnvelopeSoundness :
    Runtime.Adequacy.FailureEnvelopeSoundnessExtension
      protocol.premises.localEnvelope
      protocol.premises.RefRun
      protocol.premises.ImplRun
      protocol.premises.injectFailure
  failureEnvelopeMaximality :
    Runtime.Adequacy.FailureEnvelopeMaximalityExtension
      protocol.premises.localEnvelope
      protocol.premises.RefRun
      protocol.premises.ImplRun
      protocol.premises.injectFailure

/-- Packaged VM envelope-adherence theorem-family artifact. -/
structure VMEnvelopeAdherenceArtifact where
  protocol : Runtime.Adequacy.VMEnvelopeAdherenceProtocol
  localAdherence :
    Runtime.Adequacy.LocalEnvelopeSoundness
      protocol.premises.localHypotheses.localEnvelope
      protocol.premises.localHypotheses.refRun
      protocol.premises.localHypotheses.vmRun
  shardedAdherence :
    Runtime.Adequacy.ShardedEnvelopeSoundness
      protocol.premises.shardedHypotheses.shardedEnvelope
      protocol.premises.shardedHypotheses.refRun
      protocol.premises.shardedHypotheses.vmRun
  schedulerDeterminismLocal :
    Runtime.Adequacy.ExchangeNormalization
      protocol.premises.localHypotheses.localEnvelope
      protocol.premises.localHypotheses.certifiedExchange
  schedulerDeterminismSharded :
    Runtime.Adequacy.ShardedExchangeNormalization
      protocol.premises.shardedHypotheses.shardedEnvelope
      protocol.premises.shardedHypotheses.certifiedExchange
  monotonicity :
    Runtime.Adequacy.SpatialSubtypingMonotonicity
      protocol.premises.subtype protocol.premises.obligation
  localAdequacy :
    Runtime.Adequacy.VMObservationalAdequacyModuloEnvelope
      (Runtime.Adequacy.EqEnvLocal protocol.premises.localHypotheses.localEnvelope)
      protocol.premises.localHypotheses.refRun
      protocol.premises.localHypotheses.vmRun
  shardedAdequacy :
    Runtime.Adequacy.VMObservationalAdequacyModuloEnvelope
      (Runtime.Adequacy.EqEnvShard protocol.premises.shardedHypotheses.shardedEnvelope)
      protocol.premises.shardedHypotheses.refRun
      protocol.premises.shardedHypotheses.vmRun
  localFullAbstraction :
    Runtime.Adequacy.EnvelopeFullAbstraction
      protocol.premises.localHypotheses.localEnvelope.toEnvelope.observe
      (Runtime.Adequacy.EqEnvLocal protocol.premises.localHypotheses.localEnvelope)
  shardedFullAbstraction :
    Runtime.Adequacy.EnvelopeFullAbstraction
      protocol.premises.shardedHypotheses.shardedEnvelope.toEnvelope.observe
      (Runtime.Adequacy.EqEnvShard protocol.premises.shardedHypotheses.shardedEnvelope)
  capabilityMonotonicity :
    protocol.premises.guarantee protocol.premises.weakCapability →
    protocol.premises.guarantee protocol.premises.strongCapability

/-- Packaged VM envelope-admission theorem-family artifact. -/
structure VMEnvelopeAdmissionArtifact where
  protocol : Runtime.Adequacy.VMEnvelopeAdmissionProtocol
  localInferenceSoundness :
    Runtime.Adequacy.DProgInferenceSoundness_local
      protocol.premises.input protocol.premises.localHypotheses
  shardedInferenceSoundness :
    Runtime.Adequacy.DProgInferenceSoundness_shard
      protocol.premises.input protocol.premises.shardedHypotheses
  localPrincipalCapability :
    Runtime.Adequacy.PrincipalCapabilityProperty
      (Runtime.Adequacy.DProg_local protocol.premises.input)
      (fun c =>
        Runtime.Adequacy.CapabilityStrengthens
          (Runtime.Adequacy.DProg_local protocol.premises.input) c ∧
        Runtime.Adequacy.CapabilityStrengthens
          c (Runtime.Adequacy.DProg_local protocol.premises.input))
  shardedPrincipalCapability :
    Runtime.Adequacy.PrincipalCapabilityProperty
      (Runtime.Adequacy.DProg_shard protocol.premises.input)
      (fun c =>
        Runtime.Adequacy.CapabilityStrengthens
          (Runtime.Adequacy.DProg_shard protocol.premises.input) c ∧
        Runtime.Adequacy.CapabilityStrengthens
          c (Runtime.Adequacy.DProg_shard protocol.premises.input))
  localAdmissionSoundness :
    Runtime.Adequacy.AdmissionSoundness
      (Runtime.Adequacy.DProg_local protocol.premises.input)
      protocol.premises.runtimeComplianceLocal
  localAdmissionCompleteness :
    Runtime.Adequacy.AdmissionCompleteness
      (Runtime.Adequacy.DProg_local protocol.premises.input)
      protocol.premises.runtimeComplianceLocal
  shardedAdmissionSoundness :
    Runtime.Adequacy.AdmissionSoundness
      (Runtime.Adequacy.DProg_shard protocol.premises.input)
      protocol.premises.runtimeComplianceSharded
  shardedAdmissionCompleteness :
    Runtime.Adequacy.AdmissionCompleteness
      (Runtime.Adequacy.DProg_shard protocol.premises.input)
      protocol.premises.runtimeComplianceSharded
  decidability :
    ∀ dUser, Runtime.Adequacy.InferenceAdmissionDecidable protocol.premises.input dUser
  complexity :
    Runtime.Adequacy.InferenceComplexityBound
      protocol.premises.input protocol.premises.complexityBound
  conservativeExtension :
    ∀ baseline, Runtime.Adequacy.ConservativeExtension baseline protocol.premises.input
  necessityMinimality :
    Runtime.Adequacy.HypothesisNecessityMinimality

/-- Packaged protocol-envelope-bridge theorem-family artifact. -/
structure ProtocolEnvelopeBridgeArtifact where
  profile : Adapters.ProtocolEnvelopeBridgeProfile
  roleRenamingInvariant :
    Runtime.Adequacy.ProtocolRoleRenamingEnvelopeInvariant
      profile.bundle.premises.localEnvelope
      profile.bundle.premises.roleRenaming
  compositionalEnvelope :
    Runtime.Adequacy.ProtocolCompositionalEnvelope
      profile.bundle.premises.component₁
      profile.bundle.premises.component₂
      profile.bundle.premises.interaction
      profile.bundle.premises.total
      profile.bundle.premises.composition
  delegationPreserves :
    Runtime.Adequacy.ProtocolDelegationPreservesEnvelope
      profile.bundle.premises.localEnvelope
      profile.bundle.premises.delegation
  spatialMonotonicity :
    Runtime.Adequacy.ProtocolSpatialMonotonicity
      profile.bundle.premises.spatial
      profile.bundle.premises.obligation
  exchangeNormalization :
    Runtime.Adequacy.ProtocolExchangeNormalization
      profile.bundle.premises.localEnvelope
      profile.bundle.premises.exchange
  shardCutPreservation :
    Runtime.Adequacy.ProtocolShardCutPreservation
      profile.bundle.premises.shardedEnvelope
      profile.bundle.premises.shardCut

/-- Packaged VM termination artifact (when liveness bundle is provided). -/
structure TerminationArtifact {store₀ : SessionStore ν} where
  bundle : VMLivenessBundle store₀
  proof :
    ∃ (n : Nat) (store_final : SessionStore ν),
      store_final = executeSchedule bundle.model.step store₀ bundle.fairness.sched n ∧
      AllSessionsComplete store_final ∧
      n ≤ bundle.fairness.k * vmMeasure store₀

/-- Packaged output-condition soundness artifact. -/
structure OutputConditionArtifact where
  witness : OutputConditionWitness
  soundness : ∀ claim, witness.verify claim = true → witness.accepted claim

/-- Theorem pack auto-derived from a profile-carrying VM invariant space. -/

end

end Proofs
end Runtime
