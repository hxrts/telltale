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
import Distributed.Families.CRDT
import Distributed.Model.ConsensusEnvelope
import Runtime.Adequacy.EnvelopeCore

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Distributed

Distributed impossibility/lower-bound profiles attached to VM invariant spaces.
-/

/-
The Problem. Distributed computing impossibility results (FLP, CAP) and protocol
families (quorum-geometry, partial-synchrony, Nakamoto consensus) need to be
connected to the VM invariant space so that when designing protocols we can identify
which constraints apply.

Solution Structure. Provides profile wrappers for each distributed computing family
(FLPProfile, CAPProfile, QuorumGeometryProfile, etc.) and attachment functions that
link these profiles to specific invariant spaces, enabling impossibility checking
during protocol verification.
-/

/-! ## Core Development -/

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

/-- CRDT theorem-family profile wrapper for invariant-space attachment. -/
structure CRDTProfile where
  protocol : Distributed.CRDT.CRDTProtocol

/-- Consensus-envelope theorem-family profile wrapper for invariant-space attachment. -/
structure ConsensusEnvelopeProfile where
  protocol : Distributed.ConsensusEnvelope.ConsensusEnvelopeProtocol

/-- Failure-envelope theorem-family profile wrapper for invariant-space attachment. -/
structure FailureEnvelopeProfile where
  protocol : Runtime.Adequacy.FailureEnvelopeProtocol

/-- VM envelope-adherence theorem-family profile wrapper for invariant-space attachment. -/
structure VMEnvelopeAdherenceProfile where
  protocol : Runtime.Adequacy.VMEnvelopeAdherenceProtocol

/-- VM envelope-admission theorem-family profile wrapper for invariant-space attachment. -/
structure VMEnvelopeAdmissionProfile where
  protocol : Runtime.Adequacy.VMEnvelopeAdmissionProtocol

/-- Protocol envelope-bridge theorem-family profile wrapper for invariant-space attachment. -/
structure ProtocolEnvelopeBridgeProfile where
  Protocol : Type
  Placement : Type
  Deployment : Type
  State : Type
  Obs : Type
  bundle :
    Runtime.Adequacy.ProtocolEnvelopeBridgeBundle
      Protocol Placement Deployment State Obs

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
  crdt? : Option CRDTProfile := none
  consensusEnvelope? : Option ConsensusEnvelopeProfile := none
  failureEnvelope? : Option FailureEnvelopeProfile := none
  vmEnvelopeAdherence? : Option VMEnvelopeAdherenceProfile := none
  vmEnvelopeAdmission? : Option VMEnvelopeAdmissionProfile := none
  protocolEnvelopeBridge? : Option ProtocolEnvelopeBridgeProfile := none

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
    (coordination? : Option CoordinationProfile := none)
    (crdt? : Option CRDTProfile := none)
    (consensusEnvelope? : Option ConsensusEnvelopeProfile := none)
    (failureEnvelope? : Option FailureEnvelopeProfile := none)
    (vmEnvelopeAdherence? : Option VMEnvelopeAdherenceProfile := none)
    (vmEnvelopeAdmission? : Option VMEnvelopeAdmissionProfile := none)
    (protocolEnvelopeBridge? : Option ProtocolEnvelopeBridgeProfile := none) :
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
      , crdt? := crdt?
      , consensusEnvelope? := consensusEnvelope?
      , failureEnvelope? := failureEnvelope?
      , vmEnvelopeAdherence? := vmEnvelopeAdherence?
      , vmEnvelopeAdmission? := vmEnvelopeAdmission?
      , protocolEnvelopeBridge? := protocolEnvelopeBridge?
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

/-- Attach a CRDT theorem-family profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withCRDT
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : CRDTProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with crdt? := some p } }

/-- Attach a consensus-envelope theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withConsensusEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ConsensusEnvelopeProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with consensusEnvelope? := some p } }

/-- Attach a failure-envelope theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withFailureEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : FailureEnvelopeProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with failureEnvelope? := some p } }

/-- Attach a VM envelope-adherence theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withVMEnvelopeAdherence
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : VMEnvelopeAdherenceProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with vmEnvelopeAdherence? := some p } }

/-- Attach a VM envelope-admission theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withVMEnvelopeAdmission
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : VMEnvelopeAdmissionProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with vmEnvelopeAdmission? := some p } }

/-- Attach a protocol-envelope-bridge theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withProtocolEnvelopeBridge
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ProtocolEnvelopeBridgeProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with protocolEnvelopeBridge? := some p } }

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

/-- CRDT profile satisfies reusable core assumptions. -/
theorem crdt_coreAssumptions_allPassed (p : CRDTProfile) :
    (Distributed.CRDT.runAssumptionValidation
      p.protocol.assumptions Distributed.CRDT.coreAssumptions).allPassed = true := by
  rfl

/-- Exact CRDT envelope characterization extracted from a CRDT profile. -/
theorem crdt_exactEnvelope_of_profile (p : CRDTProfile) :
    Distributed.CRDT.ExactEnvelopeCharacterization
      p.protocol.model p.protocol.premises.RefRun p.protocol.premises.ImplRun :=
  p.protocol.exactEnvelope

/-- CRDT observational adequacy modulo envelope extracted from a profile. -/
theorem crdt_adequacy_of_profile (p : CRDTProfile) :
    Distributed.CRDT.ObservationalAdequacyModuloEnvelope
      p.protocol.model p.protocol.premises.RefRun p.protocol.premises.ImplRun :=
  p.protocol.adequacy

/-- CRDT principal capability extracted from a profile. -/
theorem crdt_principalCapability_of_profile (p : CRDTProfile) :
    Distributed.CRDT.PrincipalCapability
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.principalCapability

/-- CRDT admission soundness extracted from a profile. -/
theorem crdt_admissionSoundness_of_profile (p : CRDTProfile) :
    Distributed.CRDT.AdmissionSoundness
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.admissionSoundness

/-- CRDT admission completeness extracted from a profile. -/
theorem crdt_admissionCompleteness_of_profile (p : CRDTProfile) :
    Distributed.CRDT.AdmissionCompleteness
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.admissionCompleteness

/-- CRDT op/state equivalence extracted from a profile. -/
theorem crdt_opStateEquivalence_of_profile (p : CRDTProfile) :
    Distributed.CRDT.OpStateEquivalence
      p.protocol.model p.protocol.premises.opRun p.protocol.premises.stateRun :=
  p.protocol.opStateEquivalence

/-- CRDT GC-safety iff causal-dominance theorem extracted from a profile. -/
theorem crdt_gcSafetyIff_of_profile (p : CRDTProfile) :
    Distributed.CRDT.GCSafetyIffCausalDominance
      p.protocol.premises.GCSafe p.protocol.premises.CausalDominanceEstablished :=
  p.protocol.gcSafetyIffCausalDominance

/-- CRDT bounded-metadata approximation theorem extracted from a profile. -/
theorem crdt_boundedApproximation_of_profile (p : CRDTProfile) :
    Distributed.CRDT.BoundedMetadataApproximation
      p.protocol.model p.protocol.premises.approxPolicy p.protocol.premises.horizon
      p.protocol.premises.epsilon p.protocol.premises.referenceRun p.protocol.premises.deployedRun :=
  p.protocol.boundedApproximation

/-- CRDT approximation-monotonicity theorem extracted from a profile. -/
theorem crdt_approximationMonotonicity_of_profile (p : CRDTProfile) :
    Distributed.CRDT.ApproximationMonotoneUnderPolicyTightening
      p.protocol.model p.protocol.premises.approxPolicy p.protocol.premises.approxPolicy
      p.protocol.premises.horizon p.protocol.premises.epsilon
      p.protocol.premises.referenceRun p.protocol.premises.deployedRun :=
  p.protocol.approximationMonotonicity

/-- CRDT exact-SEC-as-limit theorem extracted from a profile. -/
theorem crdt_exactSECAsLimit_of_profile (p : CRDTProfile) :
    Distributed.CRDT.ExactSECRecoveryAsLimit
      p.protocol.model p.protocol.premises.approxPolicy
      p.protocol.premises.referenceRun p.protocol.premises.deployedRun :=
  p.protocol.exactSECAsLimit

/-- `H_crdt_core` extracted from a CRDT profile. -/
theorem crdt_hcrdtCore_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtCore p.protocol.model :=
  p.protocol.hcrdtCore

/-- `H_crdt_foundation` extracted from a CRDT profile. -/
theorem crdt_hcrdtFoundation_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtFoundation p.protocol.model :=
  p.protocol.hcrdtFoundation

/-- `H_crdt_dynamics` extracted from a CRDT profile. -/
theorem crdt_hcrdtDynamics_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtDynamics p.protocol.model :=
  p.protocol.hcrdtDynamics

/-- `H_crdt_extensions` extracted from a CRDT profile. -/
theorem crdt_hcrdtExtensions_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtExtensions p.protocol.model :=
  p.protocol.hcrdtExtensions

/-- `H_crdt_limits` extracted from a CRDT profile. -/
theorem crdt_hcrdtLimits_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtLimits p.protocol.model :=
  p.protocol.hcrdtLimits

/-- Exact consensus envelope characterization extracted from a profile. -/
theorem consensusEnvelope_exact_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.ExactEnvelopeCharacterization_consensus
      p.protocol.observe p.protocol.premises.RefRun p.protocol.premises.ImplRun :=
  p.protocol.exactEnvelope

/-- Consensus observational adequacy modulo envelope extracted from a profile. -/
theorem consensusEnvelope_adequacy_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.ObservationalAdequacyModuloEnvelope_consensus
      p.protocol.observe p.protocol.premises.RefRun p.protocol.premises.ImplRun :=
  p.protocol.adequacy

/-- Consensus principal capability extracted from a profile. -/
theorem consensusEnvelope_principalCapability_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.PrincipalCapability_consensus
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.principalCapability

/-- Consensus admission soundness extracted from a profile. -/
theorem consensusEnvelope_admissionSoundness_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.AdmissionSoundness_consensus
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.admissionSoundness

/-- Consensus admission completeness extracted from a profile. -/
theorem consensusEnvelope_admissionCompleteness_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.AdmissionCompleteness_consensus
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.admissionCompleteness

/-- Abstract recovery-action safety theorem extracted from a failure-envelope profile. -/
theorem failureEnvelope_recoveryActionSafety_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.RecoveryActionSafety
      p.protocol.premises.Safe p.protocol.premises.recoveryStep :=
  p.protocol.recoveryActionSafety

/-- Abstract no-unsafe-replay theorem extracted from a failure-envelope profile. -/
theorem failureEnvelope_noUnsafeReplay_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.NoUnsafeReplay
      p.protocol.premises.Safe p.protocol.premises.replayPre p.protocol.premises.replay :=
  p.protocol.noUnsafeReplay

/-- Checkpoint-restart refinement theorem extracted from a failure-envelope profile. -/
theorem failureEnvelope_checkpointRestartRefinement_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.CheckpointRestartRefinement
      p.protocol.premises.Refines p.protocol.premises.checkpoint p.protocol.premises.restart :=
  p.protocol.checkpointRestartRefinement

/-- Failure-envelope soundness extension extracted from a failure-envelope profile. -/
theorem failureEnvelope_soundness_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.FailureEnvelopeSoundnessExtension
      p.protocol.premises.localEnvelope
      p.protocol.premises.RefRun
      p.protocol.premises.ImplRun
      p.protocol.premises.injectFailure :=
  p.protocol.failureEnvelopeSoundness

/-- Failure-envelope maximality extension extracted from a failure-envelope profile. -/
theorem failureEnvelope_maximality_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.FailureEnvelopeMaximalityExtension
      p.protocol.premises.localEnvelope
      p.protocol.premises.RefRun
      p.protocol.premises.ImplRun
      p.protocol.premises.injectFailure :=
  p.protocol.failureEnvelopeMaximality

/-- VM local adherence theorem extracted from a VM-envelope-adherence profile. -/
theorem vmEnvelope_localAdherence_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.LocalEnvelopeSoundness
      p.protocol.premises.localHypotheses.localEnvelope
      p.protocol.premises.localHypotheses.refRun
      p.protocol.premises.localHypotheses.vmRun :=
  p.protocol.localAdherence

/-- VM sharded adherence theorem extracted from a VM-envelope-adherence profile. -/
theorem vmEnvelope_shardedAdherence_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.ShardedEnvelopeSoundness
      p.protocol.premises.shardedHypotheses.shardedEnvelope
      p.protocol.premises.shardedHypotheses.refRun
      p.protocol.premises.shardedHypotheses.vmRun :=
  p.protocol.shardedAdherence

/-- VM local scheduler determinism modulo certified exchange from profile. -/
theorem vmEnvelope_schedulerDeterminismLocal_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.ExchangeNormalization
      p.protocol.premises.localHypotheses.localEnvelope
      p.protocol.premises.localHypotheses.certifiedExchange :=
  p.protocol.schedulerDeterminismLocal

/-- VM sharded scheduler determinism modulo certified exchange from profile. -/
theorem vmEnvelope_schedulerDeterminismSharded_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.ShardedExchangeNormalization
      p.protocol.premises.shardedHypotheses.shardedEnvelope
      p.protocol.premises.shardedHypotheses.certifiedExchange :=
  p.protocol.schedulerDeterminismSharded

/-- VM adherence monotonicity under spatial refinement extracted from profile. -/
theorem vmEnvelope_monotonicity_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.SpatialSubtypingMonotonicity
      p.protocol.premises.subtype p.protocol.premises.obligation :=
  p.protocol.monotonicity

/-- VM local adequacy modulo envelope extracted from profile. -/
theorem vmEnvelope_localAdequacy_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.VMObservationalAdequacyModuloEnvelope
      (Runtime.Adequacy.EqEnvLocal p.protocol.premises.localHypotheses.localEnvelope)
      p.protocol.premises.localHypotheses.refRun
      p.protocol.premises.localHypotheses.vmRun :=
  p.protocol.localAdequacy

/-- VM sharded adequacy modulo envelope extracted from profile. -/
theorem vmEnvelope_shardedAdequacy_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.VMObservationalAdequacyModuloEnvelope
      (Runtime.Adequacy.EqEnvShard p.protocol.premises.shardedHypotheses.shardedEnvelope)
      p.protocol.premises.shardedHypotheses.refRun
      p.protocol.premises.shardedHypotheses.vmRun :=
  p.protocol.shardedAdequacy

/-- VM local full-abstraction/adequacy extracted from profile. -/
theorem vmEnvelope_localFullAbstraction_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.EnvelopeFullAbstraction
      p.protocol.premises.localHypotheses.localEnvelope.toEnvelope.observe
      (Runtime.Adequacy.EqEnvLocal p.protocol.premises.localHypotheses.localEnvelope) :=
  p.protocol.localFullAbstraction

/-- VM sharded full-abstraction/adequacy extracted from profile. -/
theorem vmEnvelope_shardedFullAbstraction_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.EnvelopeFullAbstraction
      p.protocol.premises.shardedHypotheses.shardedEnvelope.toEnvelope.observe
      (Runtime.Adequacy.EqEnvShard p.protocol.premises.shardedHypotheses.shardedEnvelope) :=
  p.protocol.shardedFullAbstraction

/-- VM capability monotonicity theorem extracted from profile. -/
theorem vmEnvelope_capabilityMonotonicity_of_profile (p : VMEnvelopeAdherenceProfile) :
    p.protocol.premises.guarantee p.protocol.premises.weakCapability →
    p.protocol.premises.guarantee p.protocol.premises.strongCapability :=
  p.protocol.capabilityMonotonicity

/-- VM local capability-inference soundness extracted from admission profile. -/
theorem vmAdmission_localInferenceSoundness_of_profile (p : VMEnvelopeAdmissionProfile) :
    Runtime.Adequacy.DProgInferenceSoundness_local
      p.protocol.premises.input p.protocol.premises.localHypotheses :=
  p.protocol.localInferenceSoundness

/-- VM sharded capability-inference soundness extracted from admission profile. -/
theorem vmAdmission_shardedInferenceSoundness_of_profile (p : VMEnvelopeAdmissionProfile) :
    Runtime.Adequacy.DProgInferenceSoundness_shard
      p.protocol.premises.input p.protocol.premises.shardedHypotheses :=
  p.protocol.shardedInferenceSoundness

/-- VM local principal-capability theorem extracted from admission profile. -/
theorem vmAdmission_localPrincipal_of_profile (p : VMEnvelopeAdmissionProfile) :
    Runtime.Adequacy.PrincipalCapabilityProperty
      (Runtime.Adequacy.DProg_local p.protocol.premises.input)
      (fun c =>
        Runtime.Adequacy.CapabilityStrengthens
          (Runtime.Adequacy.DProg_local p.protocol.premises.input) c ∧
        Runtime.Adequacy.CapabilityStrengthens
          c (Runtime.Adequacy.DProg_local p.protocol.premises.input)) :=
  p.protocol.localPrincipalCapability

/-- VM local admission soundness extracted from admission profile. -/
theorem vmAdmission_localAdmissionSoundness_of_profile (p : VMEnvelopeAdmissionProfile) :
    Runtime.Adequacy.AdmissionSoundness
      (Runtime.Adequacy.DProg_local p.protocol.premises.input)
      p.protocol.premises.runtimeComplianceLocal :=
  p.protocol.localAdmissionSoundness

/-- VM local admission completeness extracted from admission profile. -/
theorem vmAdmission_localAdmissionCompleteness_of_profile (p : VMEnvelopeAdmissionProfile) :
    Runtime.Adequacy.AdmissionCompleteness
      (Runtime.Adequacy.DProg_local p.protocol.premises.input)
      p.protocol.premises.runtimeComplianceLocal :=
  p.protocol.localAdmissionCompleteness

/-- VM admission decidability extracted from admission profile. -/
def vmAdmission_decidability_of_profile (p : VMEnvelopeAdmissionProfile) :
    ∀ dUser, Runtime.Adequacy.InferenceAdmissionDecidable p.protocol.premises.input dUser :=
  p.protocol.decidability

/-- VM admission complexity bound extracted from admission profile. -/
theorem vmAdmission_complexity_of_profile (p : VMEnvelopeAdmissionProfile) :
    Runtime.Adequacy.InferenceComplexityBound
      p.protocol.premises.input p.protocol.premises.complexityBound :=
  p.protocol.complexity

/-- VM admission conservative-extension theorem extracted from admission profile. -/
theorem vmAdmission_conservativeExtension_of_profile (p : VMEnvelopeAdmissionProfile) :
    ∀ baseline, Runtime.Adequacy.ConservativeExtension baseline p.protocol.premises.input :=
  p.protocol.conservativeExtension

/-- VM admission hypothesis-necessity/minimality theorem extracted from profile. -/
theorem vmAdmission_necessityMinimality_of_profile (p : VMEnvelopeAdmissionProfile) :
    Runtime.Adequacy.HypothesisNecessityMinimality :=
  p.protocol.necessityMinimality

/-- Protocol-bridge role-renaming invariance extracted from profile. -/
theorem protocolBridge_roleRenamingInvariant_of_profile
    (p : ProtocolEnvelopeBridgeProfile) :
    Runtime.Adequacy.ProtocolRoleRenamingEnvelopeInvariant
      p.bundle.premises.localEnvelope p.bundle.premises.roleRenaming :=
  p.bundle.roleRenamingInvariant

/-- Protocol-bridge compositional-envelope theorem extracted from profile. -/
theorem protocolBridge_compositionalEnvelope_of_profile
    (p : ProtocolEnvelopeBridgeProfile) :
    Runtime.Adequacy.ProtocolCompositionalEnvelope
      p.bundle.premises.component₁
      p.bundle.premises.component₂
      p.bundle.premises.interaction
      p.bundle.premises.total
      p.bundle.premises.composition :=
  p.bundle.compositionalEnvelope

/-- Protocol-bridge delegation-preserves theorem extracted from profile. -/
theorem protocolBridge_delegationPreserves_of_profile
    (p : ProtocolEnvelopeBridgeProfile) :
    Runtime.Adequacy.ProtocolDelegationPreservesEnvelope
      p.bundle.premises.localEnvelope p.bundle.premises.delegation :=
  p.bundle.delegationPreserves

/-- Protocol-bridge spatial monotonicity theorem extracted from profile. -/
theorem protocolBridge_spatialMonotonicity_of_profile
    (p : ProtocolEnvelopeBridgeProfile) :
    Runtime.Adequacy.ProtocolSpatialMonotonicity
      p.bundle.premises.spatial p.bundle.premises.obligation :=
  p.bundle.spatialMonotonicity

/-- Protocol-bridge exchange-normalization theorem extracted from profile. -/
theorem protocolBridge_exchangeNormalization_of_profile
    (p : ProtocolEnvelopeBridgeProfile) :
    Runtime.Adequacy.ProtocolExchangeNormalization
      p.bundle.premises.localEnvelope p.bundle.premises.exchange :=
  p.bundle.exchangeNormalization

/-- Protocol-bridge shard-cut preservation theorem extracted from profile. -/
theorem protocolBridge_shardCutPreservation_of_profile
    (p : ProtocolEnvelopeBridgeProfile) :
    Runtime.Adequacy.ProtocolShardCutPreservation
      p.bundle.premises.shardedEnvelope p.bundle.premises.shardCut :=
  p.bundle.shardCutPreservation

end

end Adapters
end Proofs
end Runtime
