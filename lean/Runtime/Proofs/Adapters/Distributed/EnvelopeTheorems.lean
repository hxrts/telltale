import Runtime.Proofs.Adapters.Distributed.CoreProfiles
import Protocol.Coherence.EdgeCoherenceCore
import Runtime.Proofs.Adapters.Distributed.EnvelopeTheoremsAdmissionBridge

/-! # Runtime.Proofs.Adapters.Distributed.EnvelopeTheorems

Envelope/profile theorem layer for distributed adapter profiles.
-/

/-
The Problem. The adapter module includes a large theorem surface mapping profile
premises to derived guarantees; grouping those separately improves navigation.

Solution Structure. Keeps the profile structures/builders in `CoreProfiles` and
collects derived theorem bridges in this focused module.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-! ## Accountable Safety Theorems -/

theorem accountable_safety_core_assumptions_all_passed (p : AccountableSafetyProfile) :
    (Distributed.AccountableSafety.runAssumptionValidation
      p.protocol.assumptions Distributed.AccountableSafety.coreAssumptions).allPassed = true := by
  rfl

/-- Accountable-safety theorem extracted from an accountable-safety profile. -/
theorem accountable_safety_of_profile (p : AccountableSafetyProfile) :
    Distributed.AccountableSafety.AccountableSafety p.protocol.model :=
  p.protocol.accountableSafety

/-! ## Failure-Detector, DA, and Coordination Theorems -/

/-- Failure-detector profile satisfies reusable core assumptions. -/
theorem failure_detectors_core_assumptions_all_passed (p : FailureDetectorsProfile) :
    (Distributed.FailureDetectors.runAssumptionValidation
      p.protocol.assumptions Distributed.FailureDetectors.coreAssumptions).allPassed = true := by
  rfl

/-- Solvability-boundary theorem extracted from a failure-detector profile. -/
theorem failure_detectors_solvability_boundary_of_profile (p : FailureDetectorsProfile) :
    Distributed.FailureDetectors.SolvableBoundary
      p.protocol.model p.protocol.premises.detector :=
  p.protocol.solvabilityBoundary

/-- Impossibility-boundary theorem extracted from a failure-detector profile. -/
theorem failure_detectors_impossibility_boundary_of_profile (p : FailureDetectorsProfile) :
    Distributed.FailureDetectors.ImpossibilityBoundary
      p.protocol.model p.protocol.premises.detector :=
  p.protocol.impossibilityBoundary

/-- Data-availability profile satisfies reusable core assumptions. -/
theorem data_availability_core_assumptions_all_passed (p : DataAvailabilityProfile) :
    (Distributed.DataAvailability.runAssumptionValidation
      p.protocol.assumptions Distributed.DataAvailability.coreAssumptions).allPassed = true := by
  rfl

/-- Data-availability theorem extracted from a DA profile. -/
theorem data_availability_availability_of_profile (p : DataAvailabilityProfile) :
    Distributed.DataAvailability.DataAvailability p.protocol.model :=
  p.protocol.availability

/-- Data-retrievability theorem extracted from a DA profile. -/
theorem data_availability_retrievability_of_profile (p : DataAvailabilityProfile) :
    Distributed.DataAvailability.DataRetrievability p.protocol.model :=
  p.protocol.retrievability

/-- Coordination profile satisfies reusable core assumptions. -/
theorem coordination_core_assumptions_all_passed (p : CoordinationProfile) :
    (Distributed.Coordination.runAssumptionValidation
      p.protocol.assumptions Distributed.Coordination.coreAssumptions).allPassed = true := by
  rfl

/-- Coordination characterization extracted from a coordination profile. -/
theorem coordination_characterization_of_profile (p : CoordinationProfile) :
    Distributed.Coordination.CoordinationCharacterization p.protocol.model :=
  p.protocol.characterization

/-! ## CRDT Envelope Theorems -/

/-- CRDT profile satisfies reusable core assumptions. -/
theorem crdt_core_assumptions_all_passed (p : CRDTProfile) :
    (Distributed.CRDT.runAssumptionValidation
      p.protocol.assumptions Distributed.CRDT.coreAssumptions).allPassed = true := by
  rfl

/-- Exact CRDT envelope characterization extracted from a CRDT profile. -/
theorem crdt_exact_envelope_of_profile (p : CRDTProfile) :
    Distributed.CRDT.ExactEnvelopeCharacterization
      p.protocol.model p.protocol.premises.RefRun p.protocol.premises.ImplRun :=
  p.protocol.exactEnvelope

/-- CRDT observational adequacy modulo envelope extracted from a profile. -/
theorem crdt_adequacy_of_profile (p : CRDTProfile) :
    Distributed.CRDT.ObservationalAdequacyModuloEnvelope
      p.protocol.model p.protocol.premises.RefRun p.protocol.premises.ImplRun :=
  p.protocol.adequacy

/-- CRDT principal capability extracted from a profile. -/
theorem crdt_principal_capability_of_profile (p : CRDTProfile) :
    Distributed.CRDT.PrincipalCapability
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.principalCapability

/-- CRDT admission soundness extracted from a profile. -/
theorem crdt_admission_soundness_of_profile (p : CRDTProfile) :
    Distributed.CRDT.AdmissionSoundness
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.admissionSoundness

/-- CRDT admission completeness extracted from a profile. -/
theorem crdt_admission_completeness_of_profile (p : CRDTProfile) :
    Distributed.CRDT.AdmissionCompleteness
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.admissionCompleteness

/-- CRDT op/state equivalence extracted from a profile. -/
theorem crdt_op_state_equivalence_of_profile (p : CRDTProfile) :
    Distributed.CRDT.OpStateEquivalence
      p.protocol.model p.protocol.premises.opRun p.protocol.premises.stateRun :=
  p.protocol.opStateEquivalence

/-! ## CRDT Approximation and Limit Theorems -/

/-- CRDT GC-safety iff causal-dominance theorem extracted from a profile. -/
theorem crdt_gc_safety_iff_of_profile (p : CRDTProfile) :
    Distributed.CRDT.GCSafetyIffCausalDominance
      p.protocol.premises.GCSafe p.protocol.premises.CausalDominanceEstablished :=
  p.protocol.gcSafetyIffCausalDominance

/-- CRDT bounded-metadata approximation theorem extracted from a profile. -/
theorem crdt_bounded_approximation_of_profile (p : CRDTProfile) :
    Distributed.CRDT.BoundedMetadataApproximation
      p.protocol.model p.protocol.premises.approxPolicy p.protocol.premises.horizon
      p.protocol.premises.epsilon p.protocol.premises.referenceRun p.protocol.premises.deployedRun :=
  p.protocol.boundedApproximation

/-- CRDT approximation-monotonicity theorem extracted from a profile. -/
theorem crdt_approximation_monotonicity_of_profile (p : CRDTProfile) :
    Distributed.CRDT.ApproximationMonotoneUnderPolicyTightening
      p.protocol.model p.protocol.premises.approxPolicy p.protocol.premises.approxPolicy
      p.protocol.premises.horizon p.protocol.premises.epsilon
      p.protocol.premises.referenceRun p.protocol.premises.deployedRun :=
  p.protocol.approximationMonotonicity

/-- CRDT exact-SEC-as-limit theorem extracted from a profile. -/
theorem crdt_exact_sec_as_limit_of_profile (p : CRDTProfile) :
    Distributed.CRDT.ExactSECRecoveryAsLimit
      p.protocol.model p.protocol.premises.approxPolicy
      p.protocol.premises.referenceRun p.protocol.premises.deployedRun :=
  p.protocol.exactSECAsLimit

/-- `H_crdt_core` extracted from a CRDT profile. -/
theorem crdt_hcrdt_core_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtCore p.protocol.model :=
  p.protocol.hcrdtCore

/-- `H_crdt_foundation` extracted from a CRDT profile. -/
theorem crdt_hcrdt_foundation_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtFoundation p.protocol.model :=
  p.protocol.hcrdtFoundation

/-- `H_crdt_dynamics` extracted from a CRDT profile. -/
theorem crdt_hcrdt_dynamics_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtDynamics p.protocol.model :=
  p.protocol.hcrdtDynamics

/-- `H_crdt_extensions` extracted from a CRDT profile. -/
theorem crdt_hcrdt_extensions_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtExtensions p.protocol.model :=
  p.protocol.hcrdtExtensions

/-- `H_crdt_limits` extracted from a CRDT profile. -/
theorem crdt_hcrdt_limits_of_profile (p : CRDTProfile) :
    Distributed.CRDT.HcrdtLimits p.protocol.model :=
  p.protocol.hcrdtLimits

/-! ## Byzantine Safety Theorems -/

/-- Byzantine interface well-formedness used by the paper-level safety interface.
It is exactly the active-edge Coherence invariant. -/
abbrev ByzIfaceWF (G : GEnv) (D : DEnv) : Prop :=
  Coherent G D

/-- `ByzIfaceWF` is definitionally equivalent to `Coherent`. -/
@[simp] theorem byz_iface_wf_iff_coherent {G : GEnv} {D : DEnv} :
    ByzIfaceWF G D ↔ Coherent G D :=
  Iff.rfl

/-- BZ-1: interface well-formedness gives the exact edge-local `Consume` obligation. -/
theorem bz1_byzantine_interface_well_formedness
    {G : GEnv} {D : DEnv} {e : Edge} {Lrecv : LocalType}
    (hWF : ByzIfaceWF G D)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv)
    (hActive : ActiveEdge G e) :
    ∃ Lsender,
      lookupG G { sid := e.sid, role := e.sender } = some Lsender ∧
      (Consume e.sender Lrecv (lookupD D e)).isSome := by
  exact coherent_edge_of_receiver hWF hGrecv hActive

/-- Byzantine-safety profile satisfies the model-level assumption gate. -/
theorem byzantine_safety_assumptions_passed_of_profile (p : ByzantineSafetyProfile) :
    (Distributed.runAssumptionValidation
      p.protocol.protocolSpec
      (Distributed.byzantineSafetyAssumptionsFor p.protocol.protocolSpec)).allPassed = true := by
  -- Reuse the API-level extraction theorem for assumption summary coherence.
  simpa using Distributed.ByzantineSafety.byzantine_assumptions_all_passed p.protocol

/-- Exact Byzantine safety characterization extracted from a profile. -/
theorem byzantine_safety_exact_of_profile (p : ByzantineSafetyProfile) :
    Distributed.ByzantineSafety.ExactByzantineSafetyCharacterization p.protocol.model :=
  p.protocol.exactCharacterization

/-- Byzantine committed-side safety theorem extracted from a profile. -/
theorem byzantine_safety_safe_of_profile (p : ByzantineSafetyProfile) :
    Distributed.ByzantineSafety.ByzantineSafety p.protocol.model :=
  Distributed.ByzantineSafety.byzantine_safety_of_protocol p.protocol

/-! ## Byzantine VM/Envelope Bridge Theorems -/

/-- VM-level observation erasure induced by the Byzantine-safe observation map. -/
def vmByzantineObservationErase
    (p : ByzantineSafetyProfile)
    (r : Runtime.Adequacy.Run p.protocol.State) :
    Nat → p.protocol.Obs :=
  Runtime.Adequacy.eraseObs
    (fun s => Distributed.ByzantineSafety.Obs_safe_byz p.protocol.model s) r

/-- Erasure equality implies pointwise Byzantine-safe equivalence. -/
theorem vm_byzantine_eq_of_erasure_eq
    (p : ByzantineSafetyProfile)
    {r₁ r₂ : Runtime.Adequacy.Run p.protocol.State}
    (hEq : vmByzantineObservationErase p r₁ = vmByzantineObservationErase p r₂) :
    ∀ n, Distributed.ByzantineSafety.Eq_safe_byz p.protocol.model (r₁ n) (r₂ n) := by
  -- Pointwise projection of erased-run equality yields the required observation equality.
  intro n
  have hPoint := congrArg (fun f => f n) hEq
  simpa [vmByzantineObservationErase, Distributed.ByzantineSafety.Eq_safe_byz,
    Distributed.ByzantineSafety.Obs_safe_byz] using hPoint

/-- Pointwise Byzantine-safe equivalence implies erasure equality. -/
theorem erasure_eq_of_vm_byzantine_eq
    (p : ByzantineSafetyProfile)
    {r₁ r₂ : Runtime.Adequacy.Run p.protocol.State}
    (hEq : ∀ n, Distributed.ByzantineSafety.Eq_safe_byz p.protocol.model (r₁ n) (r₂ n)) :
    vmByzantineObservationErase p r₁ = vmByzantineObservationErase p r₂ := by
  -- Functional extensionality lifts pointwise equality back to erased-run equality.
  funext n
  simpa [vmByzantineObservationErase, Distributed.ByzantineSafety.Eq_safe_byz,
    Distributed.ByzantineSafety.Obs_safe_byz] using hEq n

/-! ### VM Envelope Adherence Contracts -/

/-- VM-level adherence contract for Byzantine-safe envelopes. -/
def VMByzantineEnvelopeAdherence
    (p : ByzantineSafetyProfile)
    (RefRun VMRun : Runtime.Adequacy.Run p.protocol.State → Prop) : Prop :=
  ∀ ref vm, RefRun ref → VMRun vm →
    Distributed.ByzantineSafety.Envelope_byz p.protocol.model ref vm

/-- Extract VM-level Byzantine envelope adherence from an explicit witness. -/
theorem vm_byzantine_envelope_adherence_of_witness
    (p : ByzantineSafetyProfile)
    {RefRun VMRun : Runtime.Adequacy.Run p.protocol.State → Prop}
    (hEnvelope :
      ∀ ref vm, RefRun ref → VMRun vm →
        Distributed.ByzantineSafety.Envelope_byz p.protocol.model ref vm) :
    VMByzantineEnvelopeAdherence p RefRun VMRun :=
  hEnvelope

/-! ### Cross-Target Conformance Contracts -/

/-- Cross-target conformance contract under the Byzantine-safe envelope. -/
def ByzantineCrossTargetConformance
    (p : ByzantineSafetyProfile)
    (RefRun SingleRun MultiRun ShardedRun :
      Runtime.Adequacy.Run p.protocol.State → Prop) : Prop :=
  ∀ ref single multi shard,
    RefRun ref →
    SingleRun single →
    MultiRun multi →
    ShardedRun shard →
      Distributed.ByzantineSafety.Envelope_byz p.protocol.model ref single ∧
      Distributed.ByzantineSafety.Envelope_byz p.protocol.model ref multi ∧
      Distributed.ByzantineSafety.Envelope_byz p.protocol.model ref shard

/-- Build cross-target conformance from per-target envelope-adherence witnesses. -/
theorem byzantine_cross_target_conformance_of_witnesses
    (p : ByzantineSafetyProfile)
    {RefRun SingleRun MultiRun ShardedRun :
      Runtime.Adequacy.Run p.protocol.State → Prop}
    (hSingle :
      ∀ ref single, RefRun ref → SingleRun single →
        Distributed.ByzantineSafety.Envelope_byz p.protocol.model ref single)
    (hMulti :
      ∀ ref multi, RefRun ref → MultiRun multi →
        Distributed.ByzantineSafety.Envelope_byz p.protocol.model ref multi)
    (hSharded :
      ∀ ref shard, RefRun ref → ShardedRun shard →
        Distributed.ByzantineSafety.Envelope_byz p.protocol.model ref shard) :
    ByzantineCrossTargetConformance p RefRun SingleRun MultiRun ShardedRun := by
  -- Compose the three adherence witnesses into one cross-target conformance package.
  intro ref single multi shard hRef hSingleRun hMultiRun hShardedRun
  exact ⟨hSingle ref single hRef hSingleRun,
    hMulti ref multi hRef hMultiRun,
    hSharded ref shard hRef hShardedRun⟩

/-! ## Consensus Envelope Theorems -/

/-- Exact consensus envelope characterization extracted from a profile. -/
theorem consensus_envelope_exact_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.ExactEnvelopeCharacterization_consensus
      p.protocol.observe p.protocol.premises.RefRun p.protocol.premises.ImplRun :=
  p.protocol.exactEnvelope

/-- Consensus observational adequacy modulo envelope extracted from a profile. -/
theorem consensus_envelope_adequacy_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.ObservationalAdequacyModuloEnvelope_consensus
      p.protocol.observe p.protocol.premises.RefRun p.protocol.premises.ImplRun :=
  p.protocol.adequacy

/-- Consensus principal capability extracted from a profile. -/
theorem consensus_envelope_principal_capability_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.PrincipalCapability_consensus
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.principalCapability

/-- Consensus admission soundness extracted from a profile. -/
theorem consensus_envelope_admission_soundness_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.AdmissionSoundness_consensus
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.admissionSoundness

/-- Consensus admission completeness extracted from a profile. -/
theorem consensus_envelope_admission_completeness_of_profile (p : ConsensusEnvelopeProfile) :
    Distributed.ConsensusEnvelope.AdmissionCompleteness_consensus
      p.protocol.premises.inferredBudget p.protocol.premises.envelopeBudget :=
  p.protocol.admissionCompleteness

/-! ## Failure Envelope Theorems -/

/-- Abstract recovery-action safety theorem extracted from a failure-envelope profile. -/
theorem failure_envelope_recovery_action_safety_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.RecoveryActionSafety
      p.protocol.premises.Safe p.protocol.premises.recoveryStep :=
  p.protocol.recoveryActionSafety

/-- Abstract no-harmful-replay theorem extracted from a failure-envelope profile. -/
theorem failure_envelope_no_unsafe_replay_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.NoUnsafeReplay
      p.protocol.premises.Safe p.protocol.premises.replayPre p.protocol.premises.replay :=
  p.protocol.noUnsafeReplay

/-- Checkpoint-restart refinement theorem extracted from a failure-envelope profile. -/
theorem failure_envelope_checkpoint_restart_refinement_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.CheckpointRestartRefinement
      p.protocol.premises.Refines p.protocol.premises.checkpoint p.protocol.premises.restart :=
  p.protocol.checkpointRestartRefinement

/-- Cross-target failure-envelope conformance theorem extracted from a profile. -/
theorem failure_envelope_cross_target_conformance_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.CrossTargetFailureConformance
      p.protocol.premises.failureVisible
      p.protocol.premises.singleThreadRun
      p.protocol.premises.multiThreadRun
      p.protocol.premises.shardedRun :=
  p.protocol.crossTargetConformance

/-- Restart-refinement + structured-error adequacy theorem extracted from a profile. -/
theorem failure_envelope_restart_structured_error_adequacy_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.RestartRefinementStructuredErrorAdequacy
      p.protocol.premises.Refines
      p.protocol.premises.checkpoint
      p.protocol.premises.restart
      p.protocol.premises.structuredErrors :=
  p.protocol.restartStructuredErrorAdequacy

/-- Failure-envelope soundness extension extracted from a failure-envelope profile. -/
theorem failure_envelope_soundness_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.FailureEnvelopeSoundnessExtension
      p.protocol.premises.localEnvelope
      p.protocol.premises.RefRun
      p.protocol.premises.ImplRun
      p.protocol.premises.injectFailure :=
  p.protocol.failureEnvelopeSoundness

/-- Failure-envelope maximality extension extracted from a failure-envelope profile. -/
theorem failure_envelope_maximality_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.FailureEnvelopeMaximalityExtension
      p.protocol.premises.localEnvelope
      p.protocol.premises.RefRun
      p.protocol.premises.ImplRun
      p.protocol.premises.injectFailure :=
  p.protocol.failureEnvelopeMaximality

/-! ## VM Envelope Adherence Theorems -/

/-- VM local adherence theorem extracted from a VM-envelope-adherence profile. -/
theorem vm_envelope_local_adherence_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.LocalEnvelopeSoundness
      p.protocol.premises.localHypotheses.localEnvelope
      p.protocol.premises.localHypotheses.refRun
      p.protocol.premises.localHypotheses.vmRun :=
  p.protocol.localAdherence

/-- VM sharded adherence theorem extracted from a VM-envelope-adherence profile. -/
theorem vm_envelope_sharded_adherence_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.ShardedEnvelopeSoundness
      p.protocol.premises.shardedHypotheses.shardedEnvelope
      p.protocol.premises.shardedHypotheses.refRun
      p.protocol.premises.shardedHypotheses.vmRun :=
  p.protocol.shardedAdherence

/-- VM local scheduler determinism modulo certified exchange from profile. -/
theorem vm_envelope_scheduler_determinism_local_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.ExchangeNormalization
      p.protocol.premises.localHypotheses.localEnvelope
      p.protocol.premises.localHypotheses.certifiedExchange :=
  p.protocol.schedulerDeterminismLocal

/-- VM sharded scheduler determinism modulo certified exchange from profile. -/
theorem vm_envelope_scheduler_determinism_sharded_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.ShardedExchangeNormalization
      p.protocol.premises.shardedHypotheses.shardedEnvelope
      p.protocol.premises.shardedHypotheses.certifiedExchange :=
  p.protocol.schedulerDeterminismSharded

/-! ### VM Envelope Adequacy and Full-Abstraction -/

/-- VM adherence monotonicity under spatial refinement extracted from profile. -/
theorem vm_envelope_monotonicity_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.SpatialSubtypingMonotonicity
      p.protocol.premises.subtype p.protocol.premises.obligation :=
  p.protocol.monotonicity

/-- VM local adequacy modulo envelope extracted from profile. -/
theorem vm_envelope_local_adequacy_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.VMObservationalAdequacyModuloEnvelope
      (Runtime.Adequacy.EqEnvLocal p.protocol.premises.localHypotheses.localEnvelope)
      p.protocol.premises.localHypotheses.refRun
      p.protocol.premises.localHypotheses.vmRun :=
  p.protocol.localAdequacy

/-- VM sharded adequacy modulo envelope extracted from profile. -/
theorem vm_envelope_sharded_adequacy_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.VMObservationalAdequacyModuloEnvelope
      (Runtime.Adequacy.EqEnvShard p.protocol.premises.shardedHypotheses.shardedEnvelope)
      p.protocol.premises.shardedHypotheses.refRun
      p.protocol.premises.shardedHypotheses.vmRun :=
  p.protocol.shardedAdequacy

/-- VM local full-abstraction/adequacy extracted from profile. -/
theorem vm_envelope_local_full_abstraction_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.EnvelopeFullAbstraction
      p.protocol.premises.localHypotheses.localEnvelope.toEnvelope.observe
      (Runtime.Adequacy.EqEnvLocal p.protocol.premises.localHypotheses.localEnvelope) :=
  p.protocol.localFullAbstraction

/-- VM sharded full-abstraction/adequacy extracted from profile. -/
theorem vm_envelope_sharded_full_abstraction_of_profile (p : VMEnvelopeAdherenceProfile) :
    Runtime.Adequacy.EnvelopeFullAbstraction
      p.protocol.premises.shardedHypotheses.shardedEnvelope.toEnvelope.observe
      (Runtime.Adequacy.EqEnvShard p.protocol.premises.shardedHypotheses.shardedEnvelope) :=
  p.protocol.shardedFullAbstraction

end

/-! ### VM Envelope Capability Ordering -/

/-- VM capability monotonicity theorem extracted from profile. -/
theorem vm_envelope_capability_monotonicity_of_profile (p : VMEnvelopeAdherenceProfile) :
    p.protocol.premises.guarantee p.protocol.premises.weakCapability →
    p.protocol.premises.guarantee p.protocol.premises.strongCapability :=
  p.protocol.capabilityMonotonicity

end Adapters
end Proofs
end Runtime
