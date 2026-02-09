import Runtime.Proofs.InvariantSpace
import Distributed.Families.FLP
import Distributed.Families.CAP
import Distributed.Families.QuorumGeometry
import Distributed.Families.PartialSynchrony
import Distributed.Families.Responsiveness
import Distributed.Families.Nakamoto
import Distributed.Families.Reconfiguration
import Distributed.Families.AtomicBroadcast
import Distributed.Families.AccountableSafety
import Distributed.Families.FailureDetectors
import Distributed.Families.DataAvailability
import Distributed.Families.Coordination

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Distributed

Distributed impossibility/lower-bound profiles attached to VM invariant spaces.
-/

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-- FLP profile wrapper for invariant-space attachment. -/
structure FLPProfile where
  protocol : Distributed.FLP.ImpossibilityProtocol

/-- CAP profile wrapper for invariant-space attachment. -/
structure CAPProfile where
  protocol : Distributed.CAP.ImpossibilityProtocol

/-- Quorum-geometry profile wrapper for invariant-space attachment. -/
structure QuorumGeometryProfile where
  protocol : Distributed.QuorumGeometry.SafetyProtocol

/-- Partial-synchrony liveness profile wrapper for invariant-space attachment. -/
structure PartialSynchronyProfile where
  protocol : Distributed.PartialSynchrony.LivenessProtocol

/-- Responsiveness profile wrapper for invariant-space attachment. -/
structure ResponsivenessProfile where
  protocol : Distributed.Responsiveness.ResponsiveProtocol

/-- Nakamoto-security profile wrapper for invariant-space attachment. -/
structure NakamotoProfile where
  protocol : Distributed.Nakamoto.SecurityProtocol

/-- Reconfiguration profile wrapper for invariant-space attachment. -/
structure ReconfigurationProfile where
  protocol : Distributed.Reconfiguration.ReconfigurationProtocol

/-- Atomic-broadcast profile wrapper for invariant-space attachment. -/
structure AtomicBroadcastProfile where
  protocol : Distributed.AtomicBroadcast.AtomicBroadcastProtocol

/-- Accountable-safety profile wrapper for invariant-space attachment. -/
structure AccountableSafetyProfile where
  protocol : Distributed.AccountableSafety.AccountableProtocol

/-- Failure-detector boundary profile wrapper for invariant-space attachment. -/
structure FailureDetectorsProfile where
  protocol : Distributed.FailureDetectors.BoundaryProtocol

/-- Data-availability profile wrapper for invariant-space attachment. -/
structure DataAvailabilityProfile where
  protocol : Distributed.DataAvailability.DAProtocol

/-- Coordination-characterization profile wrapper for invariant-space attachment. -/
structure CoordinationProfile where
  protocol : Distributed.Coordination.CoordinationProtocol

/-- Canonical FLP-class distributed profile constructor.
The `ImpossibilityProtocol` type enforces asynchronous deterministic crash-resilient
assumption packaging structurally. -/
def asyncDeterministicCrashResilientProfile
    (protocol : Distributed.FLP.ImpossibilityProtocol) : FLPProfile :=
  { protocol := protocol }

/-- Canonical CAP-class distributed profile constructor.
The `ImpossibilityProtocol` type enforces async partition-tolerant assumption packaging
structurally. -/
def partitionTolerantAsyncProfile
    (protocol : Distributed.CAP.ImpossibilityProtocol) : CAPProfile :=
  { protocol := protocol }

/-- Optional distributed-theory profiles attached to an invariant space. -/
structure DistributedProfiles where
  flp? : Option FLPProfile := none
  cap? : Option CAPProfile := none
  quorumGeometry? : Option QuorumGeometryProfile := none
  partialSynchrony? : Option PartialSynchronyProfile := none
  responsiveness? : Option ResponsivenessProfile := none
  nakamoto? : Option NakamotoProfile := none
  reconfiguration? : Option ReconfigurationProfile := none
  atomicBroadcast? : Option AtomicBroadcastProfile := none
  accountableSafety? : Option AccountableSafetyProfile := none
  failureDetectors? : Option FailureDetectorsProfile := none
  dataAvailability? : Option DataAvailabilityProfile := none
  coordination? : Option CoordinationProfile := none

/-- VM invariant space extended with optional distributed-theory profiles. -/
structure VMInvariantSpaceWithDistributed
    (store₀ : SessionStore ν) (State : Type v)
    extends VMInvariantSpace (ν := ν) store₀ State where
  distributed : DistributedProfiles := {}

/-- Attach an FLP profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withFLP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : FLPProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with flp? := some p } }

/-- Attach a CAP profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withCAP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : CAPProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with cap? := some p } }

/-- Attach both distributed profiles in one step (profile composition helper). -/
def VMInvariantSpaceWithDistributed.withProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (flp? : Option FLPProfile)
    (cap? : Option CAPProfile)
    (quorumGeometry? : Option QuorumGeometryProfile := none)
    (partialSynchrony? : Option PartialSynchronyProfile := none)
    (responsiveness? : Option ResponsivenessProfile := none)
    (nakamoto? : Option NakamotoProfile := none)
    (reconfiguration? : Option ReconfigurationProfile := none)
    (atomicBroadcast? : Option AtomicBroadcastProfile := none)
    (accountableSafety? : Option AccountableSafetyProfile := none)
    (failureDetectors? : Option FailureDetectorsProfile := none)
    (dataAvailability? : Option DataAvailabilityProfile := none)
    (coordination? : Option CoordinationProfile := none) :
    VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed :=
      { flp? := flp?
      , cap? := cap?
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
      } }

/-- Attach a quorum-geometry profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withQuorumGeometry
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : QuorumGeometryProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with quorumGeometry? := some p } }

/-- Attach a partial-synchrony profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withPartialSynchrony
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : PartialSynchronyProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with partialSynchrony? := some p } }

/-- Attach a responsiveness profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withResponsiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ResponsivenessProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with responsiveness? := some p } }

/-- Attach a Nakamoto-security profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withNakamoto
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : NakamotoProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with nakamoto? := some p } }

/-- Attach a reconfiguration profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withReconfiguration
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ReconfigurationProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with reconfiguration? := some p } }

/-- Attach an atomic-broadcast profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withAtomicBroadcast
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : AtomicBroadcastProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with atomicBroadcast? := some p } }

/-- Attach an accountable-safety profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withAccountableSafety
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : AccountableSafetyProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with accountableSafety? := some p } }

/-- Attach a failure-detector profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withFailureDetectors
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : FailureDetectorsProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with failureDetectors? := some p } }

/-- Attach a data-availability profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withDataAvailability
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : DataAvailabilityProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with dataAvailability? := some p } }

/-- Attach a coordination profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withCoordination
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : CoordinationProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with coordination? := some p } }

/-- FLP lower-bound theorem extracted from an FLP profile. -/
theorem flp_lowerBound_of_profile (p : FLPProfile) :
    ∃ run, p.protocol.premises.FairRun run ∧ ∀ n, p.protocol.premises.Uncommitted (run n) :=
  p.protocol.lowerBound

/-- FLP impossibility theorem extracted from an FLP profile. -/
theorem flp_impossibility_of_profile (p : FLPProfile) :
    ¬ Distributed.FLP.TerminatesOnAllFairRuns p.protocol.model p.protocol.premises.FairRun :=
  p.protocol.impossibility

/-- CAP impossibility theorem extracted from a CAP profile. -/
theorem cap_impossibility_of_profile (p : CAPProfile) :
    ¬ Distributed.CAP.CAPGuarantee p.protocol.model p.protocol.premises.PartitionRun :=
  p.protocol.impossibility

/-- FLP profile satisfies the reusable FLP core assumption summary. -/
theorem flp_coreAssumptions_allPassed (p : FLPProfile) :
    (Distributed.FLP.runAssumptionValidation p.protocol.assumptions Distributed.FLP.coreAssumptions).allPassed = true := by
  rfl

/-- CAP profile satisfies the reusable CAP core assumption summary. -/
theorem cap_coreAssumptions_allPassed (p : CAPProfile) :
    (Distributed.CAP.runAssumptionValidation p.protocol.assumptions Distributed.CAP.coreAssumptions).allPassed = true := by
  rfl

/-- Quorum-geometry profile satisfies reusable core assumptions. -/
theorem quorumGeometry_coreAssumptions_allPassed (p : QuorumGeometryProfile) :
    (Distributed.QuorumGeometry.runAssumptionValidation
      p.protocol.assumptions Distributed.QuorumGeometry.coreAssumptions).allPassed = true := by
  rfl

/-- No-conflicting-commits theorem extracted from a quorum-geometry profile. -/
theorem quorumGeometry_noConflictingCommits_of_profile (p : QuorumGeometryProfile) :
    ∀ {s d₁ d₂},
      Distributed.QuorumGeometry.Committed p.protocol.model s d₁ →
      Distributed.QuorumGeometry.Committed p.protocol.model s d₂ →
      ¬ p.protocol.model.conflicts d₁ d₂ :=
  p.protocol.noConflictingCommits

/-- Fork-exclusion theorem extracted from a quorum-geometry profile. -/
theorem quorumGeometry_forkExclusion_of_profile (p : QuorumGeometryProfile) :
    ∀ s, ¬ Distributed.QuorumGeometry.Forked p.protocol.model s :=
  p.protocol.forkExclusion

/-- Safe-finality theorem extracted from a quorum-geometry profile. -/
theorem quorumGeometry_safeFinality_of_profile (p : QuorumGeometryProfile) :
    ∀ {s d},
      Distributed.QuorumGeometry.Finalized p.protocol.model s d →
      ∀ d', Distributed.QuorumGeometry.Committed p.protocol.model s d' →
        ¬ p.protocol.model.conflicts d d' :=
  p.protocol.safeFinality

/-- Partial-synchrony profile satisfies reusable core assumptions. -/
theorem partialSynchrony_coreAssumptions_allPassed (p : PartialSynchronyProfile) :
    (Distributed.PartialSynchrony.runAssumptionValidation
      p.protocol.assumptions Distributed.PartialSynchrony.coreAssumptions).allPassed = true := by
  rfl

/-- Eventual-decision theorem extracted from a partial-synchrony profile. -/
theorem partialSynchrony_eventualDecision_of_profile (p : PartialSynchronyProfile) :
    Distributed.PartialSynchrony.TerminatesOnAllFairRuns
      p.protocol.model p.protocol.premises.FairRun :=
  p.protocol.eventualDecision

/-- Bounded post-GST termination theorem extracted from a partial-synchrony profile. -/
theorem partialSynchrony_boundedPostGST_of_profile (p : PartialSynchronyProfile) :
    Distributed.PartialSynchrony.BoundedTerminationAfterGST
      p.protocol.model p.protocol.premises.FairRun
      p.protocol.premises.gst p.protocol.premises.postGSTBound :=
  p.protocol.boundedPostGST

/-- Responsiveness profile satisfies reusable core assumptions. -/
theorem responsiveness_coreAssumptions_allPassed (p : ResponsivenessProfile) :
    (Distributed.Responsiveness.runAssumptionValidation
      p.protocol.assumptions Distributed.Responsiveness.coreAssumptions).allPassed = true := by
  rfl

/-- Eventual-decision theorem extracted from a responsiveness profile. -/
theorem responsiveness_eventualDecision_of_profile (p : ResponsivenessProfile) :
    Distributed.Responsiveness.TerminatesOnAllFairRuns
      p.protocol.model p.protocol.premises.FairRun :=
  p.protocol.eventualDecision

/-- Timeout-independent latency theorem extracted from a responsiveness profile. -/
theorem responsiveness_timeoutIndependentLatency_of_profile (p : ResponsivenessProfile) :
    Distributed.Responsiveness.TimeoutIndependentLatencyBound
      p.protocol.model p.protocol.premises.FairRun
      p.protocol.premises.gst p.protocol.premises.optimisticBound :=
  p.protocol.timeoutIndependentLatency

/-- Nakamoto profile satisfies reusable core assumptions. -/
theorem nakamoto_coreAssumptions_allPassed (p : NakamotoProfile) :
    (Distributed.Nakamoto.runAssumptionValidation
      p.protocol.assumptions Distributed.Nakamoto.coreAssumptions).allPassed = true := by
  rfl

/-- Probabilistic-safety theorem extracted from a Nakamoto profile. -/
theorem nakamoto_probabilisticSafety_of_profile (p : NakamotoProfile) :
    Distributed.Nakamoto.ProbabilisticSafety
      p.protocol.model p.protocol.premises.AdmissibleRun p.protocol.premises.ε :=
  p.protocol.probabilisticSafety

/-- Settlement-finality theorem extracted from a Nakamoto profile. -/
theorem nakamoto_settlementFinality_of_profile (p : NakamotoProfile) :
    Distributed.Nakamoto.SettlementDepthFinality
      p.protocol.model p.protocol.premises.AdmissibleRun p.protocol.premises.settlementDepth :=
  p.protocol.settlementFinality

/-- Churn-liveness theorem extracted from a Nakamoto profile. -/
theorem nakamoto_livenessUnderChurn_of_profile (p : NakamotoProfile) :
    Distributed.Nakamoto.LivenessUnderChurn
      p.protocol.model p.protocol.premises.AdmissibleRun p.protocol.premises.churnBudget :=
  p.protocol.livenessUnderChurn

/-- Reconfiguration profile satisfies reusable core assumptions. -/
theorem reconfiguration_coreAssumptions_allPassed (p : ReconfigurationProfile) :
    (Distributed.Reconfiguration.runAssumptionValidation
      p.protocol.assumptions Distributed.Reconfiguration.coreAssumptions).allPassed = true := by
  rfl

/-- No-split-brain theorem extracted from a reconfiguration profile. -/
theorem reconfiguration_noSplitBrain_of_profile (p : ReconfigurationProfile) :
    Distributed.Reconfiguration.NoSplitBrainAcrossReconfiguration p.protocol.model :=
  p.protocol.noSplitBrain

/-- Safe-handoff theorem extracted from a reconfiguration profile. -/
theorem reconfiguration_safeHandoff_of_profile (p : ReconfigurationProfile) :
    Distributed.Reconfiguration.SafeHandoff p.protocol.model :=
  p.protocol.safeHandoff

/-- Liveness-preserved theorem extracted from a reconfiguration profile. -/
theorem reconfiguration_livenessPreserved_of_profile (p : ReconfigurationProfile) :
    Distributed.Reconfiguration.LivenessPreserved p.protocol.model :=
  p.protocol.livenessPreserved

/-- Atomic-broadcast profile satisfies reusable core assumptions. -/
theorem atomicBroadcast_coreAssumptions_allPassed (p : AtomicBroadcastProfile) :
    (Distributed.AtomicBroadcast.runAssumptionValidation
      p.protocol.assumptions Distributed.AtomicBroadcast.coreAssumptions).allPassed = true := by
  rfl

/-- Total-order-consistency theorem extracted from an atomic-broadcast profile. -/
theorem atomicBroadcast_totalOrderConsistency_of_profile (p : AtomicBroadcastProfile) :
    Distributed.AtomicBroadcast.TotalOrderConsistency p.protocol.model :=
  p.protocol.totalOrderConsistency

/-- Log-prefix-compatibility theorem extracted from an atomic-broadcast profile. -/
theorem atomicBroadcast_logPrefixCompatibility_of_profile (p : AtomicBroadcastProfile) :
    Distributed.AtomicBroadcast.LogPrefixCompatibility p.protocol.model :=
  p.protocol.logPrefixCompatibility

/-- Consensus/AB bridge theorem extracted from an atomic-broadcast profile. -/
theorem atomicBroadcast_bridge_of_profile (p : AtomicBroadcastProfile) :
    Distributed.AtomicBroadcast.ConsensusAtomicBroadcastBridge p.protocol.model :=
  p.protocol.consensusAtomicBroadcastBridge

/-- Accountable-safety profile satisfies reusable core assumptions. -/
theorem accountableSafety_coreAssumptions_allPassed (p : AccountableSafetyProfile) :
    (Distributed.AccountableSafety.runAssumptionValidation
      p.protocol.assumptions Distributed.AccountableSafety.coreAssumptions).allPassed = true := by
  rfl

/-- Accountable-safety theorem extracted from an accountable-safety profile. -/
theorem accountableSafety_of_profile (p : AccountableSafetyProfile) :
    Distributed.AccountableSafety.AccountableSafety p.protocol.model :=
  p.protocol.accountableSafety

/-- Failure-detector profile satisfies reusable core assumptions. -/
theorem failureDetectors_coreAssumptions_allPassed (p : FailureDetectorsProfile) :
    (Distributed.FailureDetectors.runAssumptionValidation
      p.protocol.assumptions Distributed.FailureDetectors.coreAssumptions).allPassed = true := by
  rfl

/-- Solvability-boundary theorem extracted from a failure-detector profile. -/
theorem failureDetectors_solvabilityBoundary_of_profile (p : FailureDetectorsProfile) :
    Distributed.FailureDetectors.SolvableBoundary
      p.protocol.model p.protocol.premises.detector :=
  p.protocol.solvabilityBoundary

/-- Impossibility-boundary theorem extracted from a failure-detector profile. -/
theorem failureDetectors_impossibilityBoundary_of_profile (p : FailureDetectorsProfile) :
    Distributed.FailureDetectors.ImpossibilityBoundary
      p.protocol.model p.protocol.premises.detector :=
  p.protocol.impossibilityBoundary

/-- Data-availability profile satisfies reusable core assumptions. -/
theorem dataAvailability_coreAssumptions_allPassed (p : DataAvailabilityProfile) :
    (Distributed.DataAvailability.runAssumptionValidation
      p.protocol.assumptions Distributed.DataAvailability.coreAssumptions).allPassed = true := by
  rfl

/-- Data-availability theorem extracted from a DA profile. -/
theorem dataAvailability_availability_of_profile (p : DataAvailabilityProfile) :
    Distributed.DataAvailability.DataAvailability p.protocol.model :=
  p.protocol.availability

/-- Data-retrievability theorem extracted from a DA profile. -/
theorem dataAvailability_retrievability_of_profile (p : DataAvailabilityProfile) :
    Distributed.DataAvailability.DataRetrievability p.protocol.model :=
  p.protocol.retrievability

/-- Coordination profile satisfies reusable core assumptions. -/
theorem coordination_coreAssumptions_allPassed (p : CoordinationProfile) :
    (Distributed.Coordination.runAssumptionValidation
      p.protocol.assumptions Distributed.Coordination.coreAssumptions).allPassed = true := by
  rfl

/-- Coordination characterization extracted from a coordination profile. -/
theorem coordination_characterization_of_profile (p : CoordinationProfile) :
    Distributed.Coordination.CoordinationCharacterization p.protocol.model :=
  p.protocol.characterization

end

end Adapters
end Proofs
end Runtime
