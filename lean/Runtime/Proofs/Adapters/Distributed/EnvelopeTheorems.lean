import Runtime.Proofs.Adapters.Distributed.CoreProfiles

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

theorem accountableSafety_coreAssumptions_allPassed (p : AccountableSafetyProfile) :
    (Distributed.AccountableSafety.runAssumptionValidation
      p.protocol.assumptions Distributed.AccountableSafety.coreAssumptions).allPassed = true := by
  rfl

/-- Accountable-safety theorem extracted from an accountable-safety profile. -/
theorem accountableSafety_of_profile (p : AccountableSafetyProfile) :
    Distributed.AccountableSafety.AccountableSafety p.protocol.model :=
  p.protocol.accountableSafety

/-! ## Failure-Detector, DA, and Coordination Theorems -/

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

/-! ## CRDT Envelope Theorems -/

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

/-! ## CRDT Approximation and Limit Theorems -/

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

/-! ## Byzantine Safety Theorems -/

/-- Byzantine-safety profile satisfies the model-level assumption gate. -/
theorem byzantineSafety_assumptionsPassed_of_profile (p : ByzantineSafetyProfile) :
    (Distributed.runAssumptionValidation
      p.protocol.protocolSpec
      (Distributed.byzantineSafetyAssumptionsFor p.protocol.protocolSpec)).allPassed = true := by
  -- Reuse the API-level extraction theorem for assumption summary coherence.
  simpa using Distributed.ByzantineSafety.byzantineAssumptions_allPassed p.protocol

/-- Exact Byzantine safety characterization extracted from a profile. -/
theorem byzantineSafety_exact_of_profile (p : ByzantineSafetyProfile) :
    Distributed.ByzantineSafety.ExactByzantineSafetyCharacterization p.protocol.model :=
  p.protocol.exactCharacterization

/-- Byzantine committed-side safety theorem extracted from a profile. -/
theorem byzantineSafety_safe_of_profile (p : ByzantineSafetyProfile) :
    Distributed.ByzantineSafety.ByzantineSafety p.protocol.model :=
  Distributed.ByzantineSafety.byzantineSafety_of_protocol p.protocol

/-! ## Byzantine VM/Envelope Bridge Theorems -/

/-- VM-level observation erasure induced by the Byzantine-safe observation map. -/
def vmByzantineObservationErase
    (p : ByzantineSafetyProfile)
    (r : Runtime.Adequacy.Run p.protocol.State) :
    Nat → p.protocol.Obs :=
  Runtime.Adequacy.eraseObs
    (fun s => Distributed.ByzantineSafety.Obs_safe_byz p.protocol.model s) r

/-- Erasure equality implies pointwise Byzantine-safe equivalence. -/
theorem vmByzantineEq_of_erasureEq
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
theorem erasureEq_of_vmByzantineEq
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
theorem vmByzantineEnvelopeAdherence_of_witness
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
theorem byzantineCrossTargetConformance_of_witnesses
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

/-! ## Failure Envelope Theorems -/

/-- Abstract recovery-action safety theorem extracted from a failure-envelope profile. -/
theorem failureEnvelope_recoveryActionSafety_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.RecoveryActionSafety
      p.protocol.premises.Safe p.protocol.premises.recoveryStep :=
  p.protocol.recoveryActionSafety

/-- Abstract no-harmful-replay theorem extracted from a failure-envelope profile. -/
theorem failureEnvelope_noUnsafeReplay_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.NoUnsafeReplay
      p.protocol.premises.Safe p.protocol.premises.replayPre p.protocol.premises.replay :=
  p.protocol.noUnsafeReplay

/-- Checkpoint-restart refinement theorem extracted from a failure-envelope profile. -/
theorem failureEnvelope_checkpointRestartRefinement_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.CheckpointRestartRefinement
      p.protocol.premises.Refines p.protocol.premises.checkpoint p.protocol.premises.restart :=
  p.protocol.checkpointRestartRefinement

/-- Cross-target failure-envelope conformance theorem extracted from a profile. -/
theorem failureEnvelope_crossTargetConformance_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.CrossTargetFailureConformance
      p.protocol.premises.failureVisible
      p.protocol.premises.singleThreadRun
      p.protocol.premises.multiThreadRun
      p.protocol.premises.shardedRun :=
  p.protocol.crossTargetConformance

/-- Restart-refinement + structured-error adequacy theorem extracted from a profile. -/
theorem failureEnvelope_restartStructuredErrorAdequacy_of_profile (p : FailureEnvelopeProfile) :
    Runtime.Adequacy.RestartRefinementStructuredErrorAdequacy
      p.protocol.premises.Refines
      p.protocol.premises.checkpoint
      p.protocol.premises.restart
      p.protocol.premises.structuredErrors :=
  p.protocol.restartStructuredErrorAdequacy

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

/-! ## VM Envelope Adherence Theorems -/

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

/-! ### VM Envelope Adequacy and Full-Abstraction -/

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

/-! ### VM Envelope Capability Ordering -/

/-- VM capability monotonicity theorem extracted from profile. -/
theorem vmEnvelope_capabilityMonotonicity_of_profile (p : VMEnvelopeAdherenceProfile) :
    p.protocol.premises.guarantee p.protocol.premises.weakCapability →
    p.protocol.premises.guarantee p.protocol.premises.strongCapability :=
  p.protocol.capabilityMonotonicity

/-! ## VM Admission Theorems -/

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

/-! ## Protocol Envelope Bridge Theorems -/

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
