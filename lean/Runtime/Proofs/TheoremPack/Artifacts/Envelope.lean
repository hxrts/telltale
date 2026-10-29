import Runtime.Proofs.TheoremPack.Artifacts.Distributed

/-! # Theorem Pack Artifacts: Envelope

Byzantine and consensus envelopes, protocol-machine envelope adherence and
admission, and bridge/runtime artifacts. -/

set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable [EntropyAPI.AnalysisLaws]

/-! ## Byzantine and Consensus Envelope Families -/

/-- Packaged Byzantine-safety theorem-family artifact. -/
structure ByzantineSafetyArtifact where
  protocol : Distributed.ByzantineSafety.SafetyProtocol
  exactCharacterization :
    Distributed.ByzantineSafety.ExactByzantineSafetyCharacterization protocol.model
  byzantineSafety :
    Distributed.ByzantineSafety.ByzantineSafety protocol.model
  characterization :
    Distributed.ByzantineSafety.CharacterizationCondition protocol.model
  assumptionsPassed :
    (Distributed.runAssumptionValidation
      protocol.protocolSpec
      (Distributed.byzantineSafetyAssumptionsFor protocol.protocolSpec)).allPassed = true

/-! ## CRDT and Consensus Envelope Families -/

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

/-! ## Failure and protocol machine Envelope Families -/

/-- Packaged failure-envelope theorem-family artifact. -/
structure FailureEnvelopeArtifact where
  protocol : Runtime.Adequacy.FailureEnvelopeProtocol
  /-- Assumed premise (`assumedRecoveryActionSafety`), not proved. -/
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

/-! ## protocol machine Envelope Adherence -/

/-- Packaged protocol machine envelope-adherence theorem-family artifact. -/
structure ProtocolMachineEnvelopeAdherenceArtifact where
  protocol : Runtime.Adequacy.ProtocolMachineEnvelopeAdherenceProtocol
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
  /-- Assumed premise (`assumedSpatialMonotonicity`), not proved. -/
  monotonicity :
    Runtime.Adequacy.SpatialSubtypingMonotonicity
      protocol.premises.subtype protocol.premises.obligation
  /-- Derived from `localAdherence` (`protocol_machine_local_adequacy_of_adherence`). -/
  localAdequacy :
    Runtime.Adequacy.ProtocolMachineObservationalAdequacyModuloEnvelope
      (Runtime.Adequacy.EqEnvLocal protocol.premises.localHypotheses.localEnvelope)
      protocol.premises.localHypotheses.refRun
      protocol.premises.localHypotheses.vmRun
  /-- Derived from `shardedAdherence`. -/
  shardedAdequacy :
    Runtime.Adequacy.ProtocolMachineObservationalAdequacyModuloEnvelope
      (Runtime.Adequacy.EqEnvShard protocol.premises.shardedHypotheses.shardedEnvelope)
      protocol.premises.shardedHypotheses.refRun
      protocol.premises.shardedHypotheses.vmRun
  /-- Proved for every envelope (`local_envelope_full_abstraction`). -/
  localFullAbstraction :
    Runtime.Adequacy.EnvelopeFullAbstraction
      protocol.premises.localHypotheses.localEnvelope.toEnvelope.observe
      (Runtime.Adequacy.EqEnvLocal protocol.premises.localHypotheses.localEnvelope)
  /-- Proved for every envelope (`sharded_envelope_full_abstraction`). -/
  shardedFullAbstraction :
    Runtime.Adequacy.EnvelopeFullAbstraction
      protocol.premises.shardedHypotheses.shardedEnvelope.toEnvelope.observe
      (Runtime.Adequacy.EqEnvShard protocol.premises.shardedHypotheses.shardedEnvelope)
  /-- Instance of the assumed `assumedCapabilityMonotonicity` premise. -/
  capabilityMonotonicity :
    protocol.premises.guarantee protocol.premises.weakCapability →
    protocol.premises.guarantee protocol.premises.strongCapability

/-! ## protocol machine Envelope Admission -/

/-- Packaged protocol machine envelope-admission theorem-family artifact. -/
structure ProtocolMachineEnvelopeAdmissionArtifact where
  protocol : Runtime.Adequacy.ProtocolMachineEnvelopeAdmissionProtocol
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

/-! ## Bridge and Runtime Artifacts -/

/-- Packaged protocol-envelope-bridge artifact.

Every proposition field re-exposes an assumed `assumed*` premise of
`ProtocolEnvelopeBridgePremises`; none is proved from protocol semantics. -/
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

/-- Packaged protocol machine termination artifact (when liveness bundle is provided). -/
structure TerminationArtifact {store₀ : SessionStore ν} where
  bundle : ProtocolMachineLivenessBundle store₀
  proof :
    ∃ (n : Nat) (store_final : SessionStore ν),
      store_final = executeSchedule bundle.model.step store₀ bundle.fairness.sched n ∧
      AllSessionsComplete store_final ∧
      n ≤ bundle.fairness.k * protocolMachineMeasure store₀

/-- Packaged output-condition soundness artifact. -/
structure OutputConditionArtifact where
  condition : OutputConditionWitness
  soundness : ∀ claim, condition.verify claim = true → condition.accepted claim

end

end Proofs
end Runtime
