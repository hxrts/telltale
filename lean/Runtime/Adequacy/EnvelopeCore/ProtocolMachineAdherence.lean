
import Runtime.Adequacy.EnvelopeCore.ReconfigurationBridge

/-! # Protocol-Machine Envelope Adherence

Determinism profiles, certified envelope capabilities, and admission
checking infrastructure for protocol-machine-to-envelope correspondence. -/

/-
The Problem. The protocol machine must adhere to declared envelope bounds. We need
to classify determinism guarantees (full, trace-modulo, commutativity-
modulo) and check that user-requested capabilities (`D_user`) are
contained within certified program capabilities (`D_prog`).

Solution Structure. Define `DeterminismProfileClass` enum. Define
`CertifiedEnvelopeCapability` and `DUser` structures. Provide
`dUserContained` decision procedure for admission checking.
-/

/- ## Structured Block 1 -/
set_option autoImplicit false

namespace Runtime
namespace Adequacy

universe u v

-- Determinism Profiles

inductive DeterminismProfileClass where
  | full
  | traceModulo
  | commutativityModulo
  deriving Repr, DecidableEq, Inhabited

-- Capability Objects and Admission Predicate

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

-- Protocol-Machine Local/Sharded Hypothesis Bundles

/-- E3: protocol-machine local determinism/envelope hypothesis bundle. -/
structure ProtocolMachineLocalEnvelopeHypotheses (State : Type u) (Obs : Type v) where
  localEnvelope : LocalEnvelope State Obs
  refRun : Run State → Prop
  vmRun : Run State → Prop
  certifiedExchange : AdmissibleExchange State
  adherenceWitness :
    LocalEnvelopeSoundness localEnvelope refRun vmRun
  schedulerDeterminismWitness :
    ExchangeNormalization localEnvelope certifiedExchange

/-- E3: protocol-machine sharded determinism/envelope hypothesis bundle. -/
structure ProtocolMachineShardedEnvelopeHypotheses (State : Type u) (Obs : Type v) where
  shardedEnvelope : ShardedEnvelope State Obs
  refRun : Run State → Prop
  vmRun : Run State → Prop
  certifiedExchange : AdmissibleExchange State
  adherenceWitness :
    ShardedEnvelopeSoundness shardedEnvelope refRun vmRun
  schedulerDeterminismWitness :
/- ## Structured Block 2 -/
    ShardedExchangeNormalization shardedEnvelope certifiedExchange

/-- E3: extract protocol-machine local adherence from local hypothesis bundle assumptions. -/
theorem protocol_machine_local_adherence_of_hypotheses
    {State : Type u} {Obs : Type v}
    (h : ProtocolMachineLocalEnvelopeHypotheses State Obs) :
    LocalEnvelopeSoundness h.localEnvelope h.refRun h.vmRun :=
  h.adherenceWitness

/-- E3: extract protocol-machine sharded adherence from sharded hypothesis bundle assumptions. -/
theorem protocol_machine_sharded_adherence_of_hypotheses
    {State : Type u} {Obs : Type v}
    (h : ProtocolMachineShardedEnvelopeHypotheses State Obs) :
    ShardedEnvelopeSoundness h.shardedEnvelope h.refRun h.vmRun :=
  h.adherenceWitness

/-- E3: extract scheduler determinism modulo certified exchange (local). -/
theorem scheduler_determinism_local_of_hypotheses
    {State : Type u} {Obs : Type v}
    (h : ProtocolMachineLocalEnvelopeHypotheses State Obs) :
    ExchangeNormalization h.localEnvelope h.certifiedExchange :=
  h.schedulerDeterminismWitness

/-- E3: extract scheduler determinism modulo certified exchange (sharded). -/
theorem scheduler_determinism_sharded_of_hypotheses
    {State : Type u} {Obs : Type v}
    (h : ProtocolMachineShardedEnvelopeHypotheses State Obs) :
    ShardedExchangeNormalization h.shardedEnvelope h.certifiedExchange :=
  h.schedulerDeterminismWitness

-- Adequacy and Capability Relations

/-- E3: adequacy statement form between reference and protocol-machine semantics modulo envelope. -/
def ProtocolMachineObservationalAdequacyModuloEnvelope {State : Type u}
    (R : Run State → Run State → Prop)
    (refRun machineRun : Run State → Prop) : Prop :=
  ∀ ref pm, refRun ref → machineRun pm → R ref pm

/-- E3: full-abstraction/adequacy statement over safety-visible observations. -/
def EnvelopeFullAbstraction {State : Type u} {Obs : Type v}
    (observe : State → Obs)
    (R : Run State → Run State → Prop) : Prop :=
  (∀ ref pm, R ref pm → eraseObs observe ref = eraseObs observe pm) ∧
  (∀ ref pm, eraseObs observe ref = eraseObs observe pm → R ref pm)

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

-- Protocol-Machine Adherence Premises

/-- E3: protocol-machine adherence premise bundle.

Observational adequacy and full abstraction are not premises: they are
derived below from the hypothesis bundles and the definition of `EqEnv*`.
The `assumed*` fields remain genuinely assumed inputs. -/
structure ProtocolMachineEnvelopeAdherencePremises
    (State : Type u) (Obs : Type v) (Placement : Type (max u v)) where
  localHypotheses : ProtocolMachineLocalEnvelopeHypotheses State Obs
  shardedHypotheses : ProtocolMachineShardedEnvelopeHypotheses State Obs
  subtype : SpatialSubtype Placement
  obligation : Placement → Run State → Run State → Prop
  /-- Assumed input: spatial-subtyping monotonicity of `obligation`. -/
  assumedSpatialMonotonicity :
    SpatialSubtypingMonotonicity subtype obligation
  guarantee : CertifiedEnvelopeCapability → Prop
  weakCapability : CertifiedEnvelopeCapability
  strongCapability : CertifiedEnvelopeCapability
  /-- Assumed input: monotonicity of `guarantee` in capability strength. -/
  assumedCapabilityMonotonicity : CapabilityMonotonicity guarantee
  strongStrengthensWeak :
    CapabilityStrengthens strongCapability weakCapability

-- Derived Adequacy and Full Abstraction

/-- E3: local observational adequacy follows from local adherence (soundness). -/
theorem protocol_machine_local_adequacy_of_adherence
    {State : Type u} {Obs : Type v}
    (h : ProtocolMachineLocalEnvelopeHypotheses State Obs) :
    ProtocolMachineObservationalAdequacyModuloEnvelope
      (EqEnvLocal h.localEnvelope) h.refRun h.vmRun :=
  fun ref pm hRef hPm => h.adherenceWitness ref pm hRef hPm

/-- E3: sharded observational adequacy follows from sharded adherence (soundness). -/
theorem protocol_machine_sharded_adequacy_of_adherence
    {State : Type u} {Obs : Type v}
    (h : ProtocolMachineShardedEnvelopeHypotheses State Obs) :
    ProtocolMachineObservationalAdequacyModuloEnvelope
      (EqEnvShard h.shardedEnvelope) h.refRun h.vmRun :=
  fun ref pm hRef hPm => h.adherenceWitness ref pm hRef hPm

/-- E3: every local envelope is fully abstract for its own erased observations. -/
theorem local_envelope_full_abstraction
    {State : Type u} {Obs : Type v} (E : LocalEnvelope State Obs) :
    EnvelopeFullAbstraction E.toEnvelope.observe (EqEnvLocal E) :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

/-- E3: every sharded envelope is fully abstract for its own erased observations. -/
theorem sharded_envelope_full_abstraction
    {State : Type u} {Obs : Type v} (E : ShardedEnvelope State Obs) :
    EnvelopeFullAbstraction E.toEnvelope.observe (EqEnvShard E) :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

-- Capability-Monotonicity Projection

/-- E3: instantiate the assumed capability monotonicity at the strong/weak pair. -/
theorem protocol_machine_capability_monotonicity_of_premises
    {State : Type u} {Obs : Type v} {Placement : Type (max u v)}
    (p : ProtocolMachineEnvelopeAdherencePremises State Obs Placement) :
    p.guarantee p.weakCapability → p.guarantee p.strongCapability := by
  intro hWeak
  exact p.assumedCapabilityMonotonicity
    p.weakCapability p.strongCapability p.strongStrengthensWeak hWeak

-- Packaged Protocol-Machine Adherence Protocol

/-- E3: packaged protocol-machine adherence/adequacy protocol-level theorem family. -/
structure ProtocolMachineEnvelopeAdherenceProtocol where
  State : Type u
  Obs : Type v
  Placement : Type (max u v)
  premises : ProtocolMachineEnvelopeAdherencePremises State Obs Placement
  localAdherence :
    LocalEnvelopeSoundness
      premises.localHypotheses.localEnvelope
      premises.localHypotheses.refRun
      premises.localHypotheses.vmRun :=
        protocol_machine_local_adherence_of_hypotheses premises.localHypotheses
  shardedAdherence :
    ShardedEnvelopeSoundness
      premises.shardedHypotheses.shardedEnvelope
      premises.shardedHypotheses.refRun
      premises.shardedHypotheses.vmRun :=
        protocol_machine_sharded_adherence_of_hypotheses premises.shardedHypotheses
  schedulerDeterminismLocal :
    ExchangeNormalization
      premises.localHypotheses.localEnvelope
      premises.localHypotheses.certifiedExchange :=
        scheduler_determinism_local_of_hypotheses premises.localHypotheses
  schedulerDeterminismSharded :
    ShardedExchangeNormalization
      premises.shardedHypotheses.shardedEnvelope
      premises.shardedHypotheses.certifiedExchange :=
        scheduler_determinism_sharded_of_hypotheses premises.shardedHypotheses

  -- Packaged Protocol-Machine Adherence Protocol: Adequacy Fields

  /-- Assumed (re-exposed from `premises.assumedSpatialMonotonicity`). -/
  monotonicity :
    SpatialSubtypingMonotonicity premises.subtype premises.obligation :=
      premises.assumedSpatialMonotonicity
  localAdequacy :
    ProtocolMachineObservationalAdequacyModuloEnvelope
      (EqEnvLocal premises.localHypotheses.localEnvelope)
      premises.localHypotheses.refRun
      premises.localHypotheses.vmRun :=
        protocol_machine_local_adequacy_of_adherence premises.localHypotheses
  shardedAdequacy :
    ProtocolMachineObservationalAdequacyModuloEnvelope
      (EqEnvShard premises.shardedHypotheses.shardedEnvelope)
/- ## Structured Block 5 -/
      premises.shardedHypotheses.refRun
      premises.shardedHypotheses.vmRun :=
        protocol_machine_sharded_adequacy_of_adherence premises.shardedHypotheses

  -- Packaged Protocol-Machine Adherence Protocol: Full-Abstraction Fields

  localFullAbstraction :
    EnvelopeFullAbstraction
      premises.localHypotheses.localEnvelope.toEnvelope.observe
      (EqEnvLocal premises.localHypotheses.localEnvelope) :=
        local_envelope_full_abstraction premises.localHypotheses.localEnvelope
  shardedFullAbstraction :
    EnvelopeFullAbstraction
      premises.shardedHypotheses.shardedEnvelope.toEnvelope.observe
      (EqEnvShard premises.shardedHypotheses.shardedEnvelope) :=
        sharded_envelope_full_abstraction premises.shardedHypotheses.shardedEnvelope
  capabilityMonotonicity :
    premises.guarantee premises.weakCapability →
    premises.guarantee premises.strongCapability :=
      protocol_machine_capability_monotonicity_of_premises premises

end Adequacy
end Runtime
