import Runtime.Proofs.Adapters.Progress
import Runtime.Proofs.Adapters.Distributed
import Runtime.Proofs.Adapters.Classical
import Runtime.Proofs.CompileTime.DeterminismApi

set_option autoImplicit false

/-! # Runtime.Proofs.TheoremPack

One-shot theorem packaging from a VM invariant space carrying distributed and
classical optional profiles.
-/

/-
The Problem. Users need a single entry point to obtain all applicable runtime
theorems for a given VM state, including optional distributed impossibility
results and classical analysis bounds.

Solution Structure. Defines `VMInvariantSpaceWithProfiles` combining distributed
and classical profiles. Provides projection functions to view the space as
distributed-only or classical-only. The packaging functions generate theorem
bundles from the combined invariant space in one shot.
-/

/-! ## Core Development -/

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-- Combined invariant space carrying distributed and classical profiles. -/
structure VMInvariantSpaceWithProfiles
    (store₀ : SessionStore ν) (State : Type v)
    extends Adapters.VMInvariantSpaceWithDistributed (ν := ν) store₀ State where
  classical : Adapters.ClassicalProfiles State := {}

/-- Forget classical profiles and view the space as distributed-only. -/
def VMInvariantSpaceWithProfiles.toDistributedSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    Adapters.VMInvariantSpaceWithDistributed store₀ State :=
  { toVMInvariantSpace := space.toVMInvariantSpace
  , distributed := space.distributed
  }

/-- Forget distributed profiles and view the space as classical-only. -/
def VMInvariantSpaceWithProfiles.toClassicalSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    Adapters.VMInvariantSpaceWithClassical store₀ State :=
  { toVMInvariantSpace := space.toVMInvariantSpace
  , classical := space.classical
  }

/-- Attach distributed profiles to a combined space. -/
def VMInvariantSpaceWithProfiles.withDistributedProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (distributed : Adapters.DistributedProfiles) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := distributed }

/-- Attach classical profiles to a combined space. -/
def VMInvariantSpaceWithProfiles.withClassicalProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (classical : Adapters.ClassicalProfiles State) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with classical := classical }

/-- Generic distributed-profile updater used by profile-specific setters. -/
private def VMInvariantSpaceWithProfiles.updateDistributedProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (update : Adapters.DistributedProfiles → Adapters.DistributedProfiles) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := update space.distributed }

/-- Generic classical-profile updater used by profile-specific setters. -/
private def VMInvariantSpaceWithProfiles.updateClassicalProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (update : Adapters.ClassicalProfiles State → Adapters.ClassicalProfiles State) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with classical := update space.classical }

/-- Attach an FLP distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFLP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FLPProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with flp? := some p })

/-- Attach a CAP distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withCAP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CAPProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with cap? := some p })

/-- Attach a quorum-geometry distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withQuorumGeometry
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.QuorumGeometryProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with quorumGeometry? := some p })

/-- Attach a partial-synchrony distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withPartialSynchrony
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.PartialSynchronyProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with partialSynchrony? := some p })

/-- Attach a responsiveness distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withResponsiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ResponsivenessProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with responsiveness? := some p })

/-- Attach a Nakamoto distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withNakamoto
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.NakamotoProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with nakamoto? := some p })

/-- Attach a reconfiguration distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withReconfiguration
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ReconfigurationProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with reconfiguration? := some p })

/-- Attach an atomic-broadcast distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withAtomicBroadcast
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.AtomicBroadcastProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with atomicBroadcast? := some p })

/-- Attach an accountable-safety distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withAccountableSafety
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.AccountableSafetyProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with accountableSafety? := some p })

/-- Attach a failure-detector distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFailureDetectors
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FailureDetectorsProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with failureDetectors? := some p })

/-- Attach a data-availability distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withDataAvailability
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.DataAvailabilityProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with dataAvailability? := some p })

/-- Attach a coordination distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withCoordination
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CoordinationProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with coordination? := some p })

/-- Attach a CRDT distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withCRDT
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CRDTProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with crdt? := some p })

/-- Attach a consensus-envelope distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withConsensusEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ConsensusEnvelopeProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with consensusEnvelope? := some p })

/-- Attach a failure-envelope distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFailureEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FailureEnvelopeProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with failureEnvelope? := some p })

/-- Attach a VM-envelope-adherence distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withVMEnvelopeAdherence
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.VMEnvelopeAdherenceProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with vmEnvelopeAdherence? := some p })

/-- Attach a VM-envelope-admission distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withVMEnvelopeAdmission
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.VMEnvelopeAdmissionProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with vmEnvelopeAdmission? := some p })

/-- Attach a protocol-envelope-bridge distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withProtocolEnvelopeBridge
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ProtocolEnvelopeBridgeProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with protocolEnvelopeBridge? := some p })

/-- Attach a Foster profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFoster
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FosterProfile State) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with foster? := some p })

/-- Packaged FLP lower-bound artifact. -/
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

/-- Compact theorem inventory for quick diagnostics. -/
def theoremInventory
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : List (String × Bool) :=
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
  , ("consensus_envelope", pack.consensusEnvelope?.isSome)
  , ("failure_envelope", pack.failureEnvelope?.isSome)
  , ("vm_envelope_adherence", pack.vmEnvelopeAdherence?.isSome)
  , ("vm_envelope_admission", pack.vmEnvelopeAdmission?.isSome)
  , ("protocol_envelope_bridge", pack.protocolEnvelopeBridge?.isSome)
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
  ]

/-- Theorem inventory extended with determinism artifacts. -/
def theoremInventoryWithDeterminism
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space))
    (determinism : VMDeterminismArtifacts) : List (String × Bool) :=
  theoremInventory (space := space) pack ++
    determinismInventory determinism

end

end Proofs
end Runtime
