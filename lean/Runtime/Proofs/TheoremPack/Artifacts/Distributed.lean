import Runtime.Proofs.TheoremPack.Artifacts.Core

/-! # Theorem Pack Artifacts: Distributed

Artifact records for distributed theorem families (FLP, CAP, quorum,
partial synchrony, Nakamoto, reconfiguration, CRDT, and related results). -/

set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable [EntropyAPI.AnalysisLaws]

/-! ## FLP Artifacts -/

structure FLPLowerBoundArtifact where
  protocol : Distributed.FLP.ImpossibilityProtocol
  proof : Distributed.FLP.NonDecidingRun protocol

/-- Packaged FLP impossibility artifact. -/
structure FLPImpossibilityArtifact where
  protocol : Distributed.FLP.ImpossibilityProtocol
  proof : ¬ Distributed.FLP.Async.Termination protocol.protocol

/-! ## Consensus Impossibility and Quorum -/

/-- Packaged CAP impossibility artifact. -/
structure CAPImpossibilityArtifact where
  protocol : Distributed.CAP.ImpossibilityProtocol
  proof : ¬ Distributed.CAP.CAPGuarantee protocol

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
      protocol.model protocol.assumptions.FairRun
  boundedPostGST :
    Distributed.PartialSynchrony.BoundedTerminationAfterGST
      protocol.model protocol.assumptions.FairRun
      protocol.assumptions.gst protocol.assumptions.postGSTBound

/-! ## Liveness and Responsiveness -/

/-- Packaged responsiveness artifact. -/
structure ResponsivenessArtifact where
  protocol : Distributed.Responsiveness.ResponsiveProtocol
  eventualDecision :
    Distributed.Responsiveness.TerminatesOnAllFairRuns
      protocol.model protocol.assumptions.FairRun
  timeoutIndependentLatency :
    Distributed.Responsiveness.TimeoutIndependentLatencyBound
      protocol.model protocol.assumptions.FairRun
      protocol.assumptions.gst protocol.assumptions.optimisticBound

/-- Packaged Nakamoto-security artifact. -/
structure NakamotoArtifact where
  protocol : Distributed.Nakamoto.SecurityProtocol
  probabilisticSafety :
    Distributed.Nakamoto.ProbabilisticSafety
      protocol.model protocol.assumptions.AdmissibleRun protocol.assumptions.ε
  settlementFinality :
    Distributed.Nakamoto.SettlementDepthFinality
      protocol.model protocol.assumptions.AdmissibleRun protocol.assumptions.settlementDepth
  chainGrowth :
    Distributed.Nakamoto.ChainGrowthLiveness
      protocol.model protocol.assumptions.AdmissibleRun protocol.assumptions.settlementDepth

/-- Packaged reconfiguration artifact. -/
structure ReconfigurationArtifact where
  protocol : Distributed.Reconfiguration.ReconfigurationProtocol
  noSplitBrain :
    Distributed.Reconfiguration.NoSplitBrainAcrossReconfiguration protocol.model
  safeHandoff :
    Distributed.Reconfiguration.SafeHandoff protocol.model
  livenessPreserved :
    Distributed.Reconfiguration.LivenessPreserved protocol.model protocol.assumptions.byzantine

/-! ## Chain and Reconfiguration Safety -/

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
      protocol.model protocol.detector
  impossibilityBoundary :
    Distributed.FailureDetectors.ImpossibilityBoundary
      protocol.model protocol.detector

/-! ## Accountability and Failure Detectors -/

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

/-! ## Coordination, CALM, and CRDT Monotonicity -/

/-- Packaged CALM characterization artifact. -/
structure CALMArtifact where
  protocol : Distributed.Coordination.CoordinationProtocol
  characterization :
    Distributed.Coordination.CoordinationCharacterization protocol.model
  coordinationFreeWhenMonotone :
    ∀ hMono : Distributed.Coordination.MonotoneUpdates protocol.model,
      Distributed.Coordination.CoordinationFreeSafety protocol.model
  coordinationRequiredWhenNonMonotone :
    ∀ hNonMono : ¬ Distributed.Coordination.MonotoneUpdates protocol.model,
      Distributed.Coordination.CoordinationRequired protocol.model

/-! ## Data Availability and Coordination -/

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

-- Packaged CRDT monotonicity artifact surfaced independently in theorem packs.
/-- Packaged CRDT monotonicity artifact. -/
structure CRDTMonotonicityArtifact where
  protocol : Distributed.CRDT.CRDTProtocol
  mergeInflationary :
    Distributed.CRDT.MergeInflationary protocol.premises.stateSemantics
  mergeMonotone :
    Distributed.CRDT.MergeMonotone protocol.premises.stateSemantics
  strongEventualConvergence :
    Distributed.CRDT.StrongEventualConvergence protocol.premises.stateSemantics
  finiteCausalDeliveryConverges :
    Distributed.CRDT.FiniteCausalDeliveryConverges protocol.premises.stateSemantics
  approximationMonotonicity :
    Distributed.CRDT.ApproximationMonotoneUnderPolicyTightening
      protocol.model protocol.premises.approxPolicy protocol.premises.approxPolicy
      protocol.premises.horizon protocol.premises.epsilon
      protocol.premises.referenceRun protocol.premises.deployedRun
  hcrdtCore : Distributed.CRDT.HcrdtCore protocol.model

/-- Packaged CRDT OpCore-erasure artifact. -/
structure CRDTErasureArtifact where
  protocol : Distributed.CRDT.CRDTErasureProtocol
  weakestOpCoreErasure :
    Distributed.CRDT.WeakestOpCoreErasureTheorem
      protocol.model protocol.premises.evalRich protocol.premises.interp protocol.premises.erase
  replayStable :
    Distributed.CRDT.ReplayStableCoreEval protocol.premises.interp
  serializationInvariant :
    Distributed.CRDT.TransportSerializationInvariant
      protocol.premises.encode protocol.premises.decode
  conformanceGateIffLowered :
    ∀ kr, Distributed.CRDT.conformanceGate protocol.premises.lower kr = true ↔
      ∃ kc, protocol.premises.lower kr = some kc

/-- Packaged triangle-of-forgetting impossibility artifact. -/
structure TriangleOfForgettingArtifact where
  protocol : Distributed.TriangleOfForgetting.ImpossibilityProtocol
  proof : ¬ Distributed.TriangleOfForgetting.TriangleGuarantee protocol.model

end

end Proofs
end Runtime
