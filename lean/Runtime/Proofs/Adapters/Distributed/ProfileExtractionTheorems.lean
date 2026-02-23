import Runtime.Proofs.Adapters.Distributed.ProfileWrappers

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Distributed.ProfileExtractionTheorems

Extraction lemmas from distributed profile wrappers.
-/

/-
The Problem. Consumers of profile wrappers need direct access to theorems
packaged in each protocol family without reopening family-specific structures.

Solution Structure. Re-exports profile theorem payloads as named extraction
theorems grouped by distributed family.
-/

namespace Runtime
namespace Proofs
namespace Adapters

section

/-! ## Theorem Extraction: FLP/CAP/Quorum -/

/-- FLP lower-bound theorem extracted from an FLP profile. -/
theorem flp_lower_bound_of_profile (p : FLPProfile) :
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
theorem flp_core_assumptions_all_passed (p : FLPProfile) :
    (Distributed.FLP.runAssumptionValidation p.protocol.assumptions Distributed.FLP.coreAssumptions).allPassed = true := by
  rfl

/-- CAP profile satisfies the reusable CAP core assumption summary. -/
theorem cap_core_assumptions_all_passed (p : CAPProfile) :
    (Distributed.CAP.runAssumptionValidation p.protocol.assumptions Distributed.CAP.coreAssumptions).allPassed = true := by
  rfl

/-- Quorum-geometry profile satisfies reusable core assumptions. -/
theorem quorum_geometry_core_assumptions_all_passed (p : QuorumGeometryProfile) :
    (Distributed.QuorumGeometry.runAssumptionValidation
      p.protocol.assumptions Distributed.QuorumGeometry.coreAssumptions).allPassed = true := by
  rfl

/-- No-conflicting-commits theorem extracted from a quorum-geometry profile. -/
theorem quorum_geometry_no_conflicting_commits_of_profile (p : QuorumGeometryProfile) :
    ∀ {s d₁ d₂},
      Distributed.QuorumGeometry.Committed p.protocol.model s d₁ →
      Distributed.QuorumGeometry.Committed p.protocol.model s d₂ →
      ¬ p.protocol.model.conflicts d₁ d₂ :=
  p.protocol.noConflictingCommits

/-- Fork-exclusion theorem extracted from a quorum-geometry profile. -/
theorem quorum_geometry_fork_exclusion_of_profile (p : QuorumGeometryProfile) :
    ∀ s, ¬ Distributed.QuorumGeometry.Forked p.protocol.model s :=
  p.protocol.forkExclusion

/-- Safe-finality theorem extracted from a quorum-geometry profile. -/
theorem quorum_geometry_safe_finality_of_profile (p : QuorumGeometryProfile) :
    ∀ {s d},
      Distributed.QuorumGeometry.Finalized p.protocol.model s d →
      ∀ d', Distributed.QuorumGeometry.Committed p.protocol.model s d' →
        ¬ p.protocol.model.conflicts d d' :=
  p.protocol.safeFinality

/-! ## Theorem Extraction: Synchrony and Responsiveness -/

/-- Partial-synchrony profile satisfies reusable core assumptions. -/
theorem partial_synchrony_core_assumptions_all_passed (p : PartialSynchronyProfile) :
    (Distributed.PartialSynchrony.runAssumptionValidation
      p.protocol.assumptions Distributed.PartialSynchrony.coreAssumptions).allPassed = true := by
  rfl

/-- Eventual-decision theorem extracted from a partial-synchrony profile. -/
theorem partial_synchrony_eventual_decision_of_profile (p : PartialSynchronyProfile) :
    Distributed.PartialSynchrony.TerminatesOnAllFairRuns
      p.protocol.model p.protocol.premises.FairRun :=
  p.protocol.eventualDecision

/-- Bounded post-GST termination theorem extracted from a partial-synchrony profile. -/
theorem partial_synchrony_bounded_post_gst_of_profile (p : PartialSynchronyProfile) :
    Distributed.PartialSynchrony.BoundedTerminationAfterGST
      p.protocol.model p.protocol.premises.FairRun
      p.protocol.premises.gst p.protocol.premises.postGSTBound :=
  p.protocol.boundedPostGST

/-- Responsiveness profile satisfies reusable core assumptions. -/
theorem responsiveness_core_assumptions_all_passed (p : ResponsivenessProfile) :
    (Distributed.Responsiveness.runAssumptionValidation
      p.protocol.assumptions Distributed.Responsiveness.coreAssumptions).allPassed = true := by
  rfl

/-- Eventual-decision theorem extracted from a responsiveness profile. -/
theorem responsiveness_eventual_decision_of_profile (p : ResponsivenessProfile) :
    Distributed.Responsiveness.TerminatesOnAllFairRuns
      p.protocol.model p.protocol.premises.FairRun :=
  p.protocol.eventualDecision

/-- Timeout-independent latency theorem extracted from a responsiveness profile. -/
theorem responsiveness_timeout_independent_latency_of_profile (p : ResponsivenessProfile) :
    Distributed.Responsiveness.TimeoutIndependentLatencyBound
      p.protocol.model p.protocol.premises.FairRun
      p.protocol.premises.gst p.protocol.premises.optimisticBound :=
  p.protocol.timeoutIndependentLatency

/-! ## Theorem Extraction: Nakamoto and Reconfiguration -/

/-- Nakamoto profile satisfies reusable core assumptions. -/
theorem nakamoto_core_assumptions_all_passed (p : NakamotoProfile) :
    (Distributed.Nakamoto.runAssumptionValidation
      p.protocol.assumptions Distributed.Nakamoto.coreAssumptions).allPassed = true := by
  rfl

/-- Probabilistic-safety theorem extracted from a Nakamoto profile. -/
theorem nakamoto_probabilistic_safety_of_profile (p : NakamotoProfile) :
    Distributed.Nakamoto.ProbabilisticSafety
      p.protocol.model p.protocol.premises.AdmissibleRun p.protocol.premises.ε :=
  p.protocol.probabilisticSafety

/-- Settlement-finality theorem extracted from a Nakamoto profile. -/
theorem nakamoto_settlement_finality_of_profile (p : NakamotoProfile) :
    Distributed.Nakamoto.SettlementDepthFinality
      p.protocol.model p.protocol.premises.AdmissibleRun p.protocol.premises.settlementDepth :=
  p.protocol.settlementFinality

/-- Churn-liveness theorem extracted from a Nakamoto profile. -/
theorem nakamoto_liveness_under_churn_of_profile (p : NakamotoProfile) :
    Distributed.Nakamoto.LivenessUnderChurn
      p.protocol.model p.protocol.premises.AdmissibleRun p.protocol.premises.churnBudget :=
  p.protocol.livenessUnderChurn

/-- Reconfiguration profile satisfies reusable core assumptions. -/
theorem reconfiguration_core_assumptions_all_passed (p : ReconfigurationProfile) :
    (Distributed.Reconfiguration.runAssumptionValidation
      p.protocol.assumptions Distributed.Reconfiguration.coreAssumptions).allPassed = true := by
  rfl

/-- No-split-brain theorem extracted from a reconfiguration profile. -/
theorem reconfiguration_no_split_brain_of_profile (p : ReconfigurationProfile) :
    Distributed.Reconfiguration.NoSplitBrainAcrossReconfiguration p.protocol.model :=
  p.protocol.noSplitBrain

/-- Safe-handoff theorem extracted from a reconfiguration profile. -/
theorem reconfiguration_safe_handoff_of_profile (p : ReconfigurationProfile) :
    Distributed.Reconfiguration.SafeHandoff p.protocol.model :=
  p.protocol.safeHandoff

/-- Liveness-preserved theorem extracted from a reconfiguration profile. -/
theorem reconfiguration_liveness_preserved_of_profile (p : ReconfigurationProfile) :
    Distributed.Reconfiguration.LivenessPreserved p.protocol.model :=
  p.protocol.livenessPreserved

/-! ## Theorem Extraction: Atomic Broadcast -/

/-- Atomic-broadcast profile satisfies reusable core assumptions. -/
theorem atomic_broadcast_core_assumptions_all_passed (p : AtomicBroadcastProfile) :
    (Distributed.AtomicBroadcast.runAssumptionValidation
      p.protocol.assumptions Distributed.AtomicBroadcast.coreAssumptions).allPassed = true := by
  rfl

/-- Total-order-consistency theorem extracted from an atomic-broadcast profile. -/
theorem atomic_broadcast_total_order_consistency_of_profile (p : AtomicBroadcastProfile) :
    Distributed.AtomicBroadcast.TotalOrderConsistency p.protocol.model :=
  p.protocol.totalOrderConsistency

/-- Log-prefix-compatibility theorem extracted from an atomic-broadcast profile. -/
theorem atomic_broadcast_log_prefix_compatibility_of_profile (p : AtomicBroadcastProfile) :
    Distributed.AtomicBroadcast.LogPrefixCompatibility p.protocol.model :=
  p.protocol.logPrefixCompatibility

/-- Consensus/AB bridge theorem extracted from an atomic-broadcast profile. -/
theorem atomic_broadcast_bridge_of_profile (p : AtomicBroadcastProfile) :
    Distributed.AtomicBroadcast.ConsensusAtomicBroadcastBridge p.protocol.model :=
  p.protocol.consensusAtomicBroadcastBridge

/-! ## Theorem Extraction: Byzantine Safety -/

/-- Byzantine-safety profile satisfies the reusable model-level assumption gate. -/
theorem byzantine_safety_assumptions_all_passed (p : ByzantineSafetyProfile) :
    (Distributed.runAssumptionValidation
      p.protocol.protocolSpec
      (Distributed.byzantineSafetyAssumptionsFor p.protocol.protocolSpec)).allPassed = true := by
  -- Reuse the theorem exported by the Byzantine-safety API bundle.
  simpa using Distributed.ByzantineSafety.byzantine_assumptions_all_passed p.protocol

/-- Exact Byzantine safety characterization extracted from a profile. -/
theorem byzantine_safety_exact_characterization_of_profile (p : ByzantineSafetyProfile) :
    Distributed.ByzantineSafety.ExactByzantineSafetyCharacterization p.protocol.model :=
  p.protocol.exactCharacterization

/-- Committed-side Byzantine safety extracted from a profile. -/
theorem byzantine_safety_of_profile (p : ByzantineSafetyProfile) :
    Distributed.ByzantineSafety.ByzantineSafety p.protocol.model :=
  Distributed.ByzantineSafety.byzantine_safety_of_protocol p.protocol

/-- Certified-side characterization condition extracted from a profile. -/
theorem byzantine_safety_characterization_of_profile (p : ByzantineSafetyProfile) :
    Distributed.ByzantineSafety.CharacterizationCondition p.protocol.model :=
  Distributed.ByzantineSafety.characterization_of_protocol p.protocol

end

end Adapters
end Proofs
end Runtime
