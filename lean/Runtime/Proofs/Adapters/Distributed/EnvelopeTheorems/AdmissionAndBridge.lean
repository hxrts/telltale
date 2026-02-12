import Runtime.Proofs.Adapters.Distributed.CoreProfiles

/-! # Runtime.Proofs.Adapters.Distributed.EnvelopeTheorems.AdmissionAndBridge

VM admission and protocol-envelope bridge theorem extractions.
-/

/-
The Problem. Admission and protocol-bridge theorem extractions are numerous and
obscure the core envelope/profile theorem layer when kept in one file.

Solution Structure. Keep base envelope/profile extraction theorems in
`EnvelopeTheorems` and place VM-admission/protocol-bridge extraction theorems
in this companion module.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

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
