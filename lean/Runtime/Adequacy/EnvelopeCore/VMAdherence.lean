import Runtime.Adequacy.EnvelopeCore.ReconfigurationBridge

/-! # VM Envelope Adherence

Determinism profiles, certified envelope capabilities, and admission
checking infrastructure for VM-to-envelope correspondence. -/

/-
The Problem. The VM must adhere to declared envelope bounds. We need
to classify determinism guarantees (full, trace-modulo, commutativity-
modulo) and check that user-requested capabilities (`D_user`) are
contained within certified program capabilities (`D_prog`).

Solution Structure. Define `DeterminismProfileClass` enum. Define
`CertifiedEnvelopeCapability` and `DUser` structures. Provide
`dUserContained` decision procedure for admission checking.
-/

set_option autoImplicit false

namespace Runtime
namespace Adequacy

universe u v

/-! ## Determinism Profiles -/

inductive DeterminismProfileClass where
  | full
  | traceModulo
  | commutativityModulo
  deriving Repr, DecidableEq, Inhabited

/-- Certified envelope capability summary used for admission checks. -/
structure CertifiedEnvelopeCapability where
  maxDiff : Nat
  supportsEqSafeOnly : Bool := true
  supportedProfiles : List DeterminismProfileClass := []
  deriving Repr, DecidableEq, Inhabited

/-- User-requested diff policy language (`D_user`). -/
structure DUser where
  maxRequestedDiff : Nat
  eqSafeOnly : Bool := true
  requiredProfiles : List DeterminismProfileClass := []
  deriving Repr, DecidableEq, Inhabited

def profilesContained
    (required available : List DeterminismProfileClass) : Bool :=
  required.all (fun p => p ∈ available)

/-- Decidable containment of `D_user` inside a certified envelope capability. -/
def dUserContained (d : DUser) (cap : CertifiedEnvelopeCapability) : Bool :=
  (d.maxRequestedDiff <= cap.maxDiff) &&
  (!d.eqSafeOnly || cap.supportsEqSafeOnly) &&
  profilesContained d.requiredProfiles cap.supportedProfiles

/-- E3: scheduler determinism modulo certified exchange in sharded mode. -/
def ShardedExchangeNormalization {State : Type u} {Obs : Type v}
    (E : ShardedEnvelope State Obs)
    (exchange : AdmissibleExchange State) : Prop :=
  ∀ ref₁ ref₂ impl₁ impl₂,
    exchange ref₁ ref₂ →
    exchange impl₁ impl₂ →
      EqEnvShard E ref₁ impl₁ → EqEnvShard E ref₂ impl₂

/-- E3: VM-side local determinism/envelope hypothesis bundle. -/
structure VMLocalEnvelopeHypotheses (State : Type u) (Obs : Type v) where
  localEnvelope : LocalEnvelope State Obs
  refRun : Run State → Prop
  vmRun : Run State → Prop
  certifiedExchange : AdmissibleExchange State
  adherenceWitness :
    LocalEnvelopeSoundness localEnvelope refRun vmRun
  schedulerDeterminismWitness :
    ExchangeNormalization localEnvelope certifiedExchange

/-- E3: VM-side sharded determinism/envelope hypothesis bundle. -/
structure VMShardedEnvelopeHypotheses (State : Type u) (Obs : Type v) where
  shardedEnvelope : ShardedEnvelope State Obs
  refRun : Run State → Prop
  vmRun : Run State → Prop
  certifiedExchange : AdmissibleExchange State
  adherenceWitness :
    ShardedEnvelopeSoundness shardedEnvelope refRun vmRun
  schedulerDeterminismWitness :
    ShardedExchangeNormalization shardedEnvelope certifiedExchange

/-- E3: extract VM local adherence from local hypothesis bundle assumptions. -/
theorem vmLocalAdherence_of_hypotheses
    {State : Type u} {Obs : Type v}
    (h : VMLocalEnvelopeHypotheses State Obs) :
    LocalEnvelopeSoundness h.localEnvelope h.refRun h.vmRun :=
  h.adherenceWitness

/-- E3: extract VM sharded adherence from sharded hypothesis bundle assumptions. -/
theorem vmShardedAdherence_of_hypotheses
    {State : Type u} {Obs : Type v}
    (h : VMShardedEnvelopeHypotheses State Obs) :
    ShardedEnvelopeSoundness h.shardedEnvelope h.refRun h.vmRun :=
  h.adherenceWitness

/-- E3: extract scheduler determinism modulo certified exchange (local). -/
theorem schedulerDeterminismLocal_of_hypotheses
    {State : Type u} {Obs : Type v}
    (h : VMLocalEnvelopeHypotheses State Obs) :
    ExchangeNormalization h.localEnvelope h.certifiedExchange :=
  h.schedulerDeterminismWitness

/-- E3: extract scheduler determinism modulo certified exchange (sharded). -/
theorem schedulerDeterminismSharded_of_hypotheses
    {State : Type u} {Obs : Type v}
    (h : VMShardedEnvelopeHypotheses State Obs) :
    ShardedExchangeNormalization h.shardedEnvelope h.certifiedExchange :=
  h.schedulerDeterminismWitness

/-- E3: adequacy statement form between reference and VM semantics modulo envelope. -/
def VMObservationalAdequacyModuloEnvelope {State : Type u}
    (R : Run State → Run State → Prop)
    (refRun vmRun : Run State → Prop) : Prop :=
  ∀ ref vm, refRun ref → vmRun vm → R ref vm

/-- E3: full-abstraction/adequacy statement over safety-visible observations. -/
def EnvelopeFullAbstraction {State : Type u} {Obs : Type v}
    (observe : State → Obs)
    (R : Run State → Run State → Prop) : Prop :=
  (∀ ref vm, R ref vm → eraseObs observe ref = eraseObs observe vm) ∧
  (∀ ref vm, eraseObs observe ref = eraseObs observe vm → R ref vm)

/-- E3: capability-strength relation ("stronger" provides at least weak guarantees). -/
def CapabilityStrengthens
    (strong weak : CertifiedEnvelopeCapability) : Prop :=
  weak.maxDiff ≤ strong.maxDiff ∧
  (weak.supportsEqSafeOnly → strong.supportsEqSafeOnly) ∧
  (∀ p, p ∈ weak.supportedProfiles → p ∈ strong.supportedProfiles)

/-- E3: monotonicity statement for capability-indexed envelope guarantees. -/
def CapabilityMonotonicity
    (guarantee : CertifiedEnvelopeCapability → Prop) : Prop :=
  ∀ weak strong,
    CapabilityStrengthens strong weak →
    guarantee weak →
    guarantee strong

/-- E3: VM adherence + adequacy premise bundle for theorem extraction. -/
structure VMEnvelopeAdherencePremises
    (State : Type u) (Obs : Type v) (Placement : Type (max u v)) where
  localHypotheses : VMLocalEnvelopeHypotheses State Obs
  shardedHypotheses : VMShardedEnvelopeHypotheses State Obs
  subtype : SpatialSubtype Placement
  obligation : Placement → Run State → Run State → Prop
  monotonicityWitness :
    SpatialSubtypingMonotonicity subtype obligation
  localAdequacyWitness :
    VMObservationalAdequacyModuloEnvelope
      (EqEnvLocal localHypotheses.localEnvelope)
      localHypotheses.refRun localHypotheses.vmRun
  shardedAdequacyWitness :
    VMObservationalAdequacyModuloEnvelope
      (EqEnvShard shardedHypotheses.shardedEnvelope)
      shardedHypotheses.refRun shardedHypotheses.vmRun
  localFullAbstractionWitness :
    EnvelopeFullAbstraction
      localHypotheses.localEnvelope.toEnvelope.observe
      (EqEnvLocal localHypotheses.localEnvelope)
  shardedFullAbstractionWitness :
    EnvelopeFullAbstraction
      shardedHypotheses.shardedEnvelope.toEnvelope.observe
      (EqEnvShard shardedHypotheses.shardedEnvelope)
  guarantee : CertifiedEnvelopeCapability → Prop
  weakCapability : CertifiedEnvelopeCapability
  strongCapability : CertifiedEnvelopeCapability
  capabilityMonotonicityWitness : CapabilityMonotonicity guarantee
  strongStrengthensWeak :
    CapabilityStrengthens strongCapability weakCapability

/-- E3: extract local observational adequacy modulo envelope from VM premises. -/
theorem vmLocalAdequacy_of_premises
    {State : Type u} {Obs : Type v} {Placement : Type (max u v)}
    (p : VMEnvelopeAdherencePremises State Obs Placement) :
    VMObservationalAdequacyModuloEnvelope
      (EqEnvLocal p.localHypotheses.localEnvelope)
      p.localHypotheses.refRun p.localHypotheses.vmRun :=
  p.localAdequacyWitness

/-- E3: extract sharded observational adequacy modulo envelope from VM premises. -/
theorem vmShardedAdequacy_of_premises
    {State : Type u} {Obs : Type v} {Placement : Type (max u v)}
    (p : VMEnvelopeAdherencePremises State Obs Placement) :
    VMObservationalAdequacyModuloEnvelope
      (EqEnvShard p.shardedHypotheses.shardedEnvelope)
      p.shardedHypotheses.refRun p.shardedHypotheses.vmRun :=
  p.shardedAdequacyWitness

/-- E3: extract local full-abstraction/adequacy witness from VM premises. -/
theorem vmLocalFullAbstraction_of_premises
    {State : Type u} {Obs : Type v} {Placement : Type (max u v)}
    (p : VMEnvelopeAdherencePremises State Obs Placement) :
    EnvelopeFullAbstraction
      p.localHypotheses.localEnvelope.toEnvelope.observe
      (EqEnvLocal p.localHypotheses.localEnvelope) :=
  p.localFullAbstractionWitness

/-- E3: extract sharded full-abstraction/adequacy witness from VM premises. -/
theorem vmShardedFullAbstraction_of_premises
    {State : Type u} {Obs : Type v} {Placement : Type (max u v)}
    (p : VMEnvelopeAdherencePremises State Obs Placement) :
    EnvelopeFullAbstraction
      p.shardedHypotheses.shardedEnvelope.toEnvelope.observe
      (EqEnvShard p.shardedHypotheses.shardedEnvelope) :=
  p.shardedFullAbstractionWitness

/-- E3: extract VM adherence monotonicity under spatial refinement. -/
theorem vmAdherenceMonotonicity_of_premises
    {State : Type u} {Obs : Type v} {Placement : Type (max u v)}
    (p : VMEnvelopeAdherencePremises State Obs Placement) :
    SpatialSubtypingMonotonicity p.subtype p.obligation :=
  p.monotonicityWitness

/-- E3: extract capability monotonicity theorem from VM premises. -/
theorem vmCapabilityMonotonicity_of_premises
    {State : Type u} {Obs : Type v} {Placement : Type (max u v)}
    (p : VMEnvelopeAdherencePremises State Obs Placement) :
    p.guarantee p.weakCapability → p.guarantee p.strongCapability := by
  intro hWeak
  exact p.capabilityMonotonicityWitness
    p.weakCapability p.strongCapability p.strongStrengthensWeak hWeak

/-- E3: packaged VM adherence/adequacy protocol-level theorem family. -/
structure VMEnvelopeAdherenceProtocol where
  State : Type u
  Obs : Type v
  Placement : Type (max u v)
  premises : VMEnvelopeAdherencePremises State Obs Placement
  localAdherence :
    LocalEnvelopeSoundness
      premises.localHypotheses.localEnvelope
      premises.localHypotheses.refRun
      premises.localHypotheses.vmRun :=
        vmLocalAdherence_of_hypotheses premises.localHypotheses
  shardedAdherence :
    ShardedEnvelopeSoundness
      premises.shardedHypotheses.shardedEnvelope
      premises.shardedHypotheses.refRun
      premises.shardedHypotheses.vmRun :=
        vmShardedAdherence_of_hypotheses premises.shardedHypotheses
  schedulerDeterminismLocal :
    ExchangeNormalization
      premises.localHypotheses.localEnvelope
      premises.localHypotheses.certifiedExchange :=
        schedulerDeterminismLocal_of_hypotheses premises.localHypotheses
  schedulerDeterminismSharded :
    ShardedExchangeNormalization
      premises.shardedHypotheses.shardedEnvelope
      premises.shardedHypotheses.certifiedExchange :=
        schedulerDeterminismSharded_of_hypotheses premises.shardedHypotheses
  monotonicity :
    SpatialSubtypingMonotonicity premises.subtype premises.obligation :=
      vmAdherenceMonotonicity_of_premises premises
  localAdequacy :
    VMObservationalAdequacyModuloEnvelope
      (EqEnvLocal premises.localHypotheses.localEnvelope)
      premises.localHypotheses.refRun
      premises.localHypotheses.vmRun :=
        vmLocalAdequacy_of_premises premises
  shardedAdequacy :
    VMObservationalAdequacyModuloEnvelope
      (EqEnvShard premises.shardedHypotheses.shardedEnvelope)
      premises.shardedHypotheses.refRun
      premises.shardedHypotheses.vmRun :=
        vmShardedAdequacy_of_premises premises
  localFullAbstraction :
    EnvelopeFullAbstraction
      premises.localHypotheses.localEnvelope.toEnvelope.observe
      (EqEnvLocal premises.localHypotheses.localEnvelope) :=
        vmLocalFullAbstraction_of_premises premises
  shardedFullAbstraction :
    EnvelopeFullAbstraction
      premises.shardedHypotheses.shardedEnvelope.toEnvelope.observe
      (EqEnvShard premises.shardedHypotheses.shardedEnvelope) :=
        vmShardedFullAbstraction_of_premises premises
  capabilityMonotonicity :
    premises.guarantee premises.weakCapability →
    premises.guarantee premises.strongCapability :=
      vmCapabilityMonotonicity_of_premises premises

/-- E4: input to inferred program-capability construction. -/

end Adequacy
end Runtime
