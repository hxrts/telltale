import Runtime.VM.Model.State
import Runtime.VM.Runtime.Failure

set_option autoImplicit false

/-! # Runtime.Adequacy.EnvelopeCore

Core abstract objects for envelope-based adequacy and recovery taxonomy.
-/

namespace Runtime
namespace Adequacy

universe u v

/-- Canonical run type used by local/sharded envelope relations. -/
abbrev Run (State : Type u) := Nat → State

/-- Erasure map from states to safety-visible observations. -/
def eraseObs {State : Type u} {Obs : Type v}
    (observe : State → Obs) (r : Run State) : Nat → Obs :=
  fun t => observe (r t)

/-- Strict safety-visible state equivalence. -/
def EqSafe {State : Type u} {Obs : Type v}
    (observe : State → Obs) (s₁ s₂ : State) : Prop :=
  observe s₁ = observe s₂

/-- First-class envelope relation object. -/
structure EnvelopeRelation (State : Type u) (Obs : Type v) where
  observe : State → Obs
  rel : Run State → Run State → Prop

/-- Local-mode envelope relation object. -/
structure LocalEnvelope (State : Type u) (Obs : Type v) where
  toEnvelope : EnvelopeRelation State Obs

/-- Sharded-mode envelope relation object. -/
structure ShardedEnvelope (State : Type u) (Obs : Type v) where
  toEnvelope : EnvelopeRelation State Obs

/-- Local-mode equivalence modulo erasure to safety-visible observations. -/
def EqEnvLocal {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs) (r₁ r₂ : Run State) : Prop :=
  eraseObs E.toEnvelope.observe r₁ = eraseObs E.toEnvelope.observe r₂

/-- Sharded-mode equivalence modulo erasure to safety-visible observations. -/
def EqEnvShard {State : Type u} {Obs : Type v}
    (E : ShardedEnvelope State Obs) (r₁ r₂ : Run State) : Prop :=
  eraseObs E.toEnvelope.observe r₁ = eraseObs E.toEnvelope.observe r₂

/-- Local envelope soundness in the abstract erasure-first setting. -/
def LocalEnvelopeSoundness {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → ImplRun impl → EqEnvLocal E ref impl

/-- Sharded envelope soundness in the abstract erasure-first setting. -/
def ShardedEnvelopeSoundness {State : Type u} {Obs : Type v}
    (E : ShardedEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → ImplRun impl → EqEnvShard E ref impl

/-- Local envelope realizability/completeness in the abstract setting. -/
def LocalEnvelopeRealizability {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → EqEnvLocal E ref impl → ImplRun impl

/-- Sharded envelope realizability/completeness in the abstract setting. -/
def ShardedEnvelopeRealizability {State : Type u} {Obs : Type v}
    (E : ShardedEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → EqEnvShard E ref impl → ImplRun impl

/-- Relative maximality for local envelopes in the abstract setting. -/
def LocalEnvelopeMaximality {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ R : Run State → Run State → Prop,
    (∀ ref impl, RefRun ref → ImplRun impl → R ref impl → EqEnvLocal E ref impl) →
      (∀ ref impl, RefRun ref → ImplRun impl → R ref impl →
        EqEnvLocal E ref impl)

/-- Relative maximality for sharded envelopes in the abstract setting. -/
def ShardedEnvelopeMaximality {State : Type u} {Obs : Type v}
    (E : ShardedEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ R : Run State → Run State → Prop,
    (∀ ref impl, RefRun ref → ImplRun impl → R ref impl → EqEnvShard E ref impl) →
      (∀ ref impl, RefRun ref → ImplRun impl → R ref impl →
        EqEnvShard E ref impl)

/-- Local exact characterization theorem form. -/
def LocalExactEnvelopeCharacterization {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  LocalEnvelopeSoundness E RefRun ImplRun ∧
  LocalEnvelopeRealizability E RefRun ImplRun ∧
  LocalEnvelopeMaximality E RefRun ImplRun

/-- Sharded exact characterization theorem form. -/
def ShardedExactEnvelopeCharacterization {State : Type u} {Obs : Type v}
    (E : ShardedEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ShardedEnvelopeSoundness E RefRun ImplRun ∧
  ShardedEnvelopeRealizability E RefRun ImplRun ∧
  ShardedEnvelopeMaximality E RefRun ImplRun

/-- Premises bundle for Phase E1 local/sharded exact-characterization extraction. -/
structure EnvelopePhaseE1Premises (State : Type u) (Obs : Type v) where
  localEnvelope : LocalEnvelope State Obs
  shardedEnvelope : ShardedEnvelope State Obs
  localRefRun : Run State → Prop
  localImplRun : Run State → Prop
  shardedRefRun : Run State → Prop
  shardedImplRun : Run State → Prop
  localSoundnessWitness :
    LocalEnvelopeSoundness localEnvelope localRefRun localImplRun
  shardedSoundnessWitness :
    ShardedEnvelopeSoundness shardedEnvelope shardedRefRun shardedImplRun
  localRealizabilityWitness :
    LocalEnvelopeRealizability localEnvelope localRefRun localImplRun
  shardedRealizabilityWitness :
    ShardedEnvelopeRealizability shardedEnvelope shardedRefRun shardedImplRun
  localMaximalityWitness :
    LocalEnvelopeMaximality localEnvelope localRefRun localImplRun
  shardedMaximalityWitness :
    ShardedEnvelopeMaximality shardedEnvelope shardedRefRun shardedImplRun

/-- Extract local envelope soundness from E1 premises. -/
theorem localEnvelopeSoundness_of_e1Premises
    {State : Type u} {Obs : Type v}
    (p : EnvelopePhaseE1Premises State Obs) :
    LocalEnvelopeSoundness p.localEnvelope p.localRefRun p.localImplRun :=
  p.localSoundnessWitness

/-- Extract sharded envelope soundness from E1 premises. -/
theorem shardedEnvelopeSoundness_of_e1Premises
    {State : Type u} {Obs : Type v}
    (p : EnvelopePhaseE1Premises State Obs) :
    ShardedEnvelopeSoundness p.shardedEnvelope p.shardedRefRun p.shardedImplRun :=
  p.shardedSoundnessWitness

/-- Extract local envelope realizability/completeness from E1 premises. -/
theorem localEnvelopeRealizability_of_e1Premises
    {State : Type u} {Obs : Type v}
    (p : EnvelopePhaseE1Premises State Obs) :
    LocalEnvelopeRealizability p.localEnvelope p.localRefRun p.localImplRun :=
  p.localRealizabilityWitness

/-- Extract sharded envelope realizability/completeness from E1 premises. -/
theorem shardedEnvelopeRealizability_of_e1Premises
    {State : Type u} {Obs : Type v}
    (p : EnvelopePhaseE1Premises State Obs) :
    ShardedEnvelopeRealizability p.shardedEnvelope p.shardedRefRun p.shardedImplRun :=
  p.shardedRealizabilityWitness

/-- Extract local envelope maximality from E1 premises. -/
theorem localEnvelopeMaximality_of_e1Premises
    {State : Type u} {Obs : Type v}
    (p : EnvelopePhaseE1Premises State Obs) :
    LocalEnvelopeMaximality p.localEnvelope p.localRefRun p.localImplRun :=
  p.localMaximalityWitness

/-- Extract sharded envelope maximality from E1 premises. -/
theorem shardedEnvelopeMaximality_of_e1Premises
    {State : Type u} {Obs : Type v}
    (p : EnvelopePhaseE1Premises State Obs) :
    ShardedEnvelopeMaximality p.shardedEnvelope p.shardedRefRun p.shardedImplRun :=
  p.shardedMaximalityWitness

/-- Package local exact characterization from E1 premises. -/
theorem localExactEnvelopeCharacterization_of_e1Premises
    {State : Type u} {Obs : Type v}
    (p : EnvelopePhaseE1Premises State Obs) :
    LocalExactEnvelopeCharacterization
      p.localEnvelope p.localRefRun p.localImplRun := by
  exact ⟨p.localSoundnessWitness, p.localRealizabilityWitness, p.localMaximalityWitness⟩

/-- Package sharded exact characterization from E1 premises. -/
theorem shardedExactEnvelopeCharacterization_of_e1Premises
    {State : Type u} {Obs : Type v}
    (p : EnvelopePhaseE1Premises State Obs) :
    ShardedExactEnvelopeCharacterization
      p.shardedEnvelope p.shardedRefRun p.shardedImplRun := by
  exact ⟨p.shardedSoundnessWitness, p.shardedRealizabilityWitness, p.shardedMaximalityWitness⟩

/-- Bijective role renaming used for role-equivalence invariance statements. -/
structure RoleRenaming (Role : Type u) where
  rename : Role → Role
  inverse : Role → Role
  leftInverse : ∀ r, inverse (rename r) = r
  rightInverse : ∀ r, rename (inverse r) = r

/-- State-level action of role renaming. -/
class RoleRenamableState (Role : Type u) (State : Type v) where
  renameState : RoleRenaming Role → State → State

/-- Rename every state in a run. -/
def renameRun {Role : Type u} {State : Type v}
    [RoleRenamableState Role State]
    (ρ : RoleRenaming Role) (r : Run State) : Run State :=
  fun t => RoleRenamableState.renameState ρ (r t)

/-- Envelope-bound functional form used for composition/invariance theorems. -/
abbrev EnvelopeBound (State : Type u) := Run State → Run State → Nat

/-- Role-equivalence invariance of envelope bounds. -/
def RoleEquivalenceInvariantBound {Role : Type u} {State : Type v}
    [RoleRenamableState Role State]
    (bound : EnvelopeBound State) : Prop :=
  ∀ ρ ref impl,
    bound
      (renameRun (Role := Role) (State := State) ρ ref)
      (renameRun (Role := Role) (State := State) ρ impl) =
      bound ref impl

/-- Compositional envelope bound with explicit interaction term. -/
def CompositionalEnvelopeBound {State : Type u}
    (component₁ component₂ interaction total : EnvelopeBound State) : Prop :=
  ∀ ref impl,
    total ref impl = component₁ ref impl + component₂ ref impl + interaction ref impl

/-- Non-interference assumption for two envelope components. -/
def NonInterference {State : Type u}
    (component₁ component₂ : EnvelopeBound State) : Prop :=
  ∀ ref impl, component₁ ref impl = 0 ∨ component₂ ref impl = 0

/-- Compositional exactness under explicit non-interference assumptions. -/
def CompositionalExactnessUnderNonInterference {State : Type u}
    (component₁ component₂ interaction total : EnvelopeBound State) : Prop :=
  NonInterference component₁ component₂ →
    (∀ ref impl, interaction ref impl = 0) →
      ∀ ref impl, total ref impl = component₁ ref impl + component₂ ref impl

/-- Exactness follows when the composed bound is exact and interaction vanishes. -/
theorem compositionalExactness_of_zeroInteraction
    {State : Type u}
    {component₁ component₂ interaction total : EnvelopeBound State}
    (hComp : CompositionalEnvelopeBound component₁ component₂ interaction total) :
    CompositionalExactnessUnderNonInterference component₁ component₂ interaction total := by
  intro _hNI hZero ref impl
  simpa [hZero ref impl] using hComp ref impl

/-- Delegation/handoff preserves local envelope equivalence. -/
def DelegationPreservesEnvelope {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (delegate : Run State → Run State) : Prop :=
  ∀ ref impl, EqEnvLocal E ref impl → EqEnvLocal E (delegate ref) (delegate impl)

/-- Generic spatial-subtyping relation. -/
abbrev SpatialSubtype (Placement : Type u) := Placement → Placement → Prop

/-- Monotonicity of envelope obligations under spatial-subtyping refinement. -/
def SpatialSubtypingMonotonicity {Placement : Type u} {State : Type v}
    (subtype : SpatialSubtype Placement)
    (obligation : Placement → Run State → Run State → Prop) : Prop :=
  ∀ p₁ p₂, subtype p₁ p₂ →
    ∀ ref impl, obligation p₁ ref impl → obligation p₂ ref impl

/-- Admissible run reordering/exchange relation. -/
abbrev AdmissibleExchange (State : Type u) := Run State → Run State → Prop

/-- Exchange-normalization theorem form for determinism modulo admissible reorderings. -/
def ExchangeNormalization {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (exchange : AdmissibleExchange State) : Prop :=
  ∀ ref₁ ref₂ impl₁ impl₂,
    exchange ref₁ ref₂ →
    exchange impl₁ impl₂ →
      EqEnvLocal E ref₁ impl₁ → EqEnvLocal E ref₂ impl₂

/-- Premises bundle for advanced E1 envelope-bridge theorem extraction. -/
structure EnvelopePhaseE1BridgePremises
    (Role : Type u) (State : Type v) (Obs : Type (max u v))
    [RoleRenamableState Role State] where
  localEnvelope : LocalEnvelope State Obs
  bound : EnvelopeBound State
  component₁ : EnvelopeBound State
  component₂ : EnvelopeBound State
  interaction : EnvelopeBound State
  total : EnvelopeBound State
  delegate : Run State → Run State
  Placement : Type (max u v)
  subtype : SpatialSubtype Placement
  obligation : Placement → Run State → Run State → Prop
  exchange : AdmissibleExchange State
  roleInvarianceWitness :
    RoleEquivalenceInvariantBound (Role := Role) bound
  compositionalBoundWitness :
    CompositionalEnvelopeBound component₁ component₂ interaction total
  delegationWitness :
    DelegationPreservesEnvelope localEnvelope delegate
  spatialMonotonicityWitness :
    SpatialSubtypingMonotonicity subtype obligation
  exchangeNormalizationWitness :
    ExchangeNormalization localEnvelope exchange

/-- Extract role-equivalence invariance from E1 bridge premises. -/
theorem roleEquivalenceInvariant_of_e1BridgePremises
    {Role : Type u} {State : Type v} {Obs : Type (max u v)}
    [RoleRenamableState Role State]
    (p : EnvelopePhaseE1BridgePremises Role State Obs) :
    RoleEquivalenceInvariantBound (Role := Role) p.bound :=
  p.roleInvarianceWitness

/-- Extract compositional envelope bound from E1 bridge premises. -/
theorem compositionalEnvelopeBound_of_e1BridgePremises
    {Role : Type u} {State : Type v} {Obs : Type (max u v)}
    [RoleRenamableState Role State]
    (p : EnvelopePhaseE1BridgePremises Role State Obs) :
    CompositionalEnvelopeBound p.component₁ p.component₂ p.interaction p.total :=
  p.compositionalBoundWitness

/-- Extract delegation-preserves-envelope from E1 bridge premises. -/
theorem delegationPreservesEnvelope_of_e1BridgePremises
    {Role : Type u} {State : Type v} {Obs : Type (max u v)}
    [RoleRenamableState Role State]
    (p : EnvelopePhaseE1BridgePremises Role State Obs) :
    DelegationPreservesEnvelope p.localEnvelope p.delegate :=
  p.delegationWitness

/-- Extract spatial-subtyping monotonicity from E1 bridge premises. -/
theorem spatialSubtypingMonotonicity_of_e1BridgePremises
    {Role : Type u} {State : Type v} {Obs : Type (max u v)}
    [RoleRenamableState Role State]
    (p : EnvelopePhaseE1BridgePremises Role State Obs) :
    SpatialSubtypingMonotonicity p.subtype p.obligation :=
  p.spatialMonotonicityWitness

/-- Extract exchange-normalization theorem from E1 bridge premises. -/
theorem exchangeNormalization_of_e1BridgePremises
    {Role : Type u} {State : Type v} {Obs : Type (max u v)}
    [RoleRenamableState Role State]
    (p : EnvelopePhaseE1BridgePremises Role State Obs) :
    ExchangeNormalization p.localEnvelope p.exchange :=
  p.exchangeNormalizationWitness

/-- Protocol-level role-renaming semantics over runs. -/
structure ProtocolRoleRenamingSemantics (Protocol : Type u) (State : Type v) where
  renameRun : Protocol → Run State → Run State

/-- Protocol-level composition/linking semantics over runs. -/
structure ProtocolCompositionSemantics (Protocol : Type u) (State : Type v) where
  composeRun : Protocol → Protocol → Run State → Run State

/-- Protocol-level delegation semantics over runs. -/
structure ProtocolDelegationSemantics (Protocol : Type u) (State : Type v) where
  delegateRun : Protocol → Run State → Run State

/-- Protocol-level spatial subtyping relation. -/
structure ProtocolSpatialSemantics
    (Protocol : Type u) (Placement : Type v) where
  subtype : Protocol → Placement → Placement → Prop

/-- Protocol-level exchange/coherence normalization relation over runs. -/
structure ProtocolExchangeSemantics (Protocol : Type u) (State : Type v) where
  exchange : Protocol → AdmissibleExchange State

/-- Protocol-level shard-cut/linking model. -/
structure ProtocolShardCutSemantics
    (Protocol : Type u) (Deployment : Type v) (State : Type (max u v)) where
  cut : Protocol → Deployment → Deployment → Prop
  runOf : Deployment → Run State

/-- E2.1: instantiate role-equivalence invariance for protocol role renaming. -/
def ProtocolRoleRenamingEnvelopeInvariant
    {Protocol : Type u} {State : Type v} {Obs : Type (max u v)}
    (E : LocalEnvelope State Obs)
    (ρ : ProtocolRoleRenamingSemantics Protocol State) : Prop :=
  ∀ p ref impl, EqEnvLocal E ref impl →
    EqEnvLocal E (ρ.renameRun p ref) (ρ.renameRun p impl)

/-- E2.2: instantiate compositional envelope theorem via protocol composition. -/
def ProtocolCompositionalEnvelope
    {Protocol : Type u} {State : Type v}
    (component₁ component₂ interaction total : EnvelopeBound State)
    (compose : ProtocolCompositionSemantics Protocol State) : Prop :=
  ∀ p₁ p₂ ref impl,
    total (compose.composeRun p₁ p₂ ref) (compose.composeRun p₁ p₂ impl) =
      component₁ ref impl + component₂ ref impl + interaction ref impl

/-- E2.3: instantiate delegation-preserves-envelope via protocol delegation semantics. -/
def ProtocolDelegationPreservesEnvelope
    {Protocol : Type u} {State : Type v} {Obs : Type (max u v)}
    (E : LocalEnvelope State Obs)
    (δ : ProtocolDelegationSemantics Protocol State) : Prop :=
  ∀ p ref impl, EqEnvLocal E ref impl →
    EqEnvLocal E (δ.delegateRun p ref) (δ.delegateRun p impl)

/-- E2.4: instantiate spatial-subtyping monotonicity via protocol spatial typing. -/
def ProtocolSpatialMonotonicity
    {Protocol : Type u} {Placement : Type v} {State : Type (max u v)}
    (spatialSem : ProtocolSpatialSemantics Protocol Placement)
    (obligation : Placement → Run State → Run State → Prop) : Prop :=
  ∀ p pl₁ pl₂, spatialSem.subtype p pl₁ pl₂ →
    ∀ ref impl, obligation pl₁ ref impl → obligation pl₂ ref impl

/-- E2.5: instantiate exchange-normalization via protocol exchange/coherence lemmas. -/
def ProtocolExchangeNormalization
    {Protocol : Type u} {State : Type v} {Obs : Type (max u v)}
    (E : LocalEnvelope State Obs)
    (Ξ : ProtocolExchangeSemantics Protocol State) : Prop :=
  ∀ p ref₁ ref₂ impl₁ impl₂,
    (Ξ.exchange p) ref₁ ref₂ →
    (Ξ.exchange p) impl₁ impl₂ →
      EqEnvLocal E ref₁ impl₁ → EqEnvLocal E ref₂ impl₂

/-- E2.6: shard-cut preservation over protocol-level deployment/linking objects. -/
def ProtocolShardCutPreservation
    {Protocol : Type u} {Deployment : Type v} {State : Type (max u v)} {Obs : Type (max u v)}
    (E : ShardedEnvelope State Obs)
    (S : ProtocolShardCutSemantics Protocol Deployment State) : Prop :=
  ∀ p d₁ d₂, S.cut p d₁ d₂ →
    EqEnvShard E (S.runOf d₁) (S.runOf d₂)

/-- Premises bundle for protocol bridge theorem extraction (Phase E2). -/
structure ProtocolEnvelopeBridgePremises
    (Protocol : Type u) (Placement : Type v)
    (Deployment : Type (max u v))
    (State : Type (max u v)) (Obs : Type (max u v)) where
  localEnvelope : LocalEnvelope State Obs
  shardedEnvelope : ShardedEnvelope State Obs
  roleRenaming : ProtocolRoleRenamingSemantics Protocol State
  composition : ProtocolCompositionSemantics Protocol State
  delegation : ProtocolDelegationSemantics Protocol State
  spatial : ProtocolSpatialSemantics Protocol Placement
  exchange : ProtocolExchangeSemantics Protocol State
  shardCut : ProtocolShardCutSemantics Protocol Deployment State
  component₁ : EnvelopeBound State
  component₂ : EnvelopeBound State
  interaction : EnvelopeBound State
  total : EnvelopeBound State
  obligation : Placement → Run State → Run State → Prop
  roleRenamingInvariantWitness :
    ProtocolRoleRenamingEnvelopeInvariant localEnvelope roleRenaming
  compositionalEnvelopeWitness :
    ProtocolCompositionalEnvelope component₁ component₂ interaction total composition
  delegationPreservesWitness :
    ProtocolDelegationPreservesEnvelope localEnvelope delegation
  spatialMonotonicityWitness :
    ProtocolSpatialMonotonicity spatial obligation
  exchangeNormalizationWitness :
    ProtocolExchangeNormalization localEnvelope exchange
  shardCutPreservationWitness :
    ProtocolShardCutPreservation shardedEnvelope shardCut

/-- Extract E2 role-renaming invariance from protocol bridge premises. -/
theorem protocolRoleRenamingInvariant_of_premises
    {Protocol : Type u} {Placement : Type v}
    {Deployment : Type (max u v)}
    {State : Type (max u v)} {Obs : Type (max u v)}
    (p : ProtocolEnvelopeBridgePremises Protocol Placement Deployment State Obs) :
    ProtocolRoleRenamingEnvelopeInvariant p.localEnvelope p.roleRenaming :=
  p.roleRenamingInvariantWitness

/-- Extract E2 compositional-envelope theorem from protocol bridge premises. -/
theorem protocolCompositionalEnvelope_of_premises
    {Protocol : Type u} {Placement : Type v}
    {Deployment : Type (max u v)}
    {State : Type (max u v)} {Obs : Type (max u v)}
    (p : ProtocolEnvelopeBridgePremises Protocol Placement Deployment State Obs) :
    ProtocolCompositionalEnvelope
      p.component₁ p.component₂ p.interaction p.total p.composition :=
  p.compositionalEnvelopeWitness

/-- Extract E2 delegation-preserves-envelope from protocol bridge premises. -/
theorem protocolDelegationPreserves_of_premises
    {Protocol : Type u} {Placement : Type v}
    {Deployment : Type (max u v)}
    {State : Type (max u v)} {Obs : Type (max u v)}
    (p : ProtocolEnvelopeBridgePremises Protocol Placement Deployment State Obs) :
    ProtocolDelegationPreservesEnvelope p.localEnvelope p.delegation :=
  p.delegationPreservesWitness

/-- Extract E2 spatial-monotonicity instantiation from protocol bridge premises. -/
theorem protocolSpatialMonotonicity_of_premises
    {Protocol : Type u} {Placement : Type v}
    {Deployment : Type (max u v)}
    {State : Type (max u v)} {Obs : Type (max u v)}
    (p : ProtocolEnvelopeBridgePremises Protocol Placement Deployment State Obs) :
    ProtocolSpatialMonotonicity p.spatial p.obligation :=
  p.spatialMonotonicityWitness

/-- Extract E2 exchange-normalization instantiation from protocol bridge premises. -/
theorem protocolExchangeNormalization_of_premises
    {Protocol : Type u} {Placement : Type v}
    {Deployment : Type (max u v)}
    {State : Type (max u v)} {Obs : Type (max u v)}
    (p : ProtocolEnvelopeBridgePremises Protocol Placement Deployment State Obs) :
    ProtocolExchangeNormalization p.localEnvelope p.exchange :=
  p.exchangeNormalizationWitness

/-- Extract E2 shard-cut preservation theorem from protocol bridge premises. -/
theorem protocolShardCutPreservation_of_premises
    {Protocol : Type u} {Placement : Type v}
    {Deployment : Type (max u v)}
    {State : Type (max u v)} {Obs : Type (max u v)}
    (p : ProtocolEnvelopeBridgePremises Protocol Placement Deployment State Obs) :
    ProtocolShardCutPreservation p.shardedEnvelope p.shardCut :=
  p.shardCutPreservationWitness

/-- E2.7: protocol-level theorem bundle collecting all bridge instantiations. -/
structure ProtocolEnvelopeBridgeBundle
    (Protocol : Type u) (Placement : Type v)
    (Deployment : Type (max u v))
    (State : Type (max u v)) (Obs : Type (max u v)) where
  premises : ProtocolEnvelopeBridgePremises Protocol Placement Deployment State Obs
  roleRenamingInvariant :
    ProtocolRoleRenamingEnvelopeInvariant premises.localEnvelope premises.roleRenaming :=
      protocolRoleRenamingInvariant_of_premises premises
  compositionalEnvelope :
    ProtocolCompositionalEnvelope
      premises.component₁ premises.component₂
      premises.interaction premises.total premises.composition :=
      protocolCompositionalEnvelope_of_premises premises
  delegationPreserves :
    ProtocolDelegationPreservesEnvelope premises.localEnvelope premises.delegation :=
      protocolDelegationPreserves_of_premises premises
  spatialMonotonicity :
    ProtocolSpatialMonotonicity premises.spatial premises.obligation :=
      protocolSpatialMonotonicity_of_premises premises
  exchangeNormalization :
    ProtocolExchangeNormalization premises.localEnvelope premises.exchange :=
      protocolExchangeNormalization_of_premises premises
  shardCutPreservation :
    ProtocolShardCutPreservation premises.shardedEnvelope premises.shardCut :=
      protocolShardCutPreservation_of_premises premises

/-- Determinism profile classes used for capability/theorem gating. -/
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

private def profilesContained
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
structure ProgramCapabilityInput where
  localMaxDiff : Nat
  shardedMaxDiff : Nat
  requiresEqSafeOnly : Bool := true
  localProfiles : List DeterminismProfileClass := []
  shardedProfiles : List DeterminismProfileClass := []
  deriving Repr, DecidableEq, Inhabited

/-- E4: inferred local program capability (`D_prog_local`). -/
def DProg_local (input : ProgramCapabilityInput) : CertifiedEnvelopeCapability :=
  { maxDiff := input.localMaxDiff
  , supportsEqSafeOnly := input.requiresEqSafeOnly
  , supportedProfiles := input.localProfiles
  }

/-- E4: inferred sharded program capability (`D_prog_shard`). -/
def DProg_shard (input : ProgramCapabilityInput) : CertifiedEnvelopeCapability :=
  { maxDiff := input.shardedMaxDiff
  , supportsEqSafeOnly := input.requiresEqSafeOnly
  , supportedProfiles := input.shardedProfiles
  }

/-- E4: soundness form for local capability inference. -/
def DProgInferenceSoundness_local
    {State : Type u} {Obs : Type v}
    (input : ProgramCapabilityInput)
    (h : VMLocalEnvelopeHypotheses State Obs) : Prop :=
  ∀ dUser, dUserContained dUser (DProg_local input) = true →
    LocalEnvelopeSoundness h.localEnvelope h.refRun h.vmRun

/-- E4: soundness form for sharded capability inference. -/
def DProgInferenceSoundness_shard
    {State : Type u} {Obs : Type v}
    (input : ProgramCapabilityInput)
    (h : VMShardedEnvelopeHypotheses State Obs) : Prop :=
  ∀ dUser, dUserContained dUser (DProg_shard input) = true →
    ShardedEnvelopeSoundness h.shardedEnvelope h.refRun h.vmRun

/-- E4: principal-capability property over an inferred capability. -/
def PrincipalCapabilityProperty
    (inferred : CertifiedEnvelopeCapability)
    (precise : CertifiedEnvelopeCapability → Prop) : Prop :=
  precise inferred ∧ ∀ c, precise c → CapabilityStrengthens inferred c

/-- E4: admission soundness form (containment implies runtime compliance). -/
def AdmissionSoundness
    (dProg : CertifiedEnvelopeCapability)
    (runtimeCompliance : DUser → Prop) : Prop :=
  ∀ dUser, dUserContained dUser dProg = true → runtimeCompliance dUser

/-- E4: admission completeness form (admitted iff principal containment). -/
def AdmissionCompleteness
    (dProg : CertifiedEnvelopeCapability)
    (runtimeCompliance : DUser → Prop) : Prop :=
  ∀ dUser, runtimeCompliance dUser ↔ dUserContained dUser dProg = true

/-- E4: admission-check obligations used by diagnostics. -/
inductive AdmissionObligation where
  | withinMaxDiff
  | eqSafeSupported
  | requiredProfilesSupported
  deriving Repr, DecidableEq, Inhabited

/-- E4: machine-visible rejection reasons for failed admission checks. -/
inductive AdmissionRejectionReason where
  | maxDiffExceeded
  | eqSafeNotSupported
  | missingRequiredProfiles
  deriving Repr, DecidableEq, Inhabited

/-- E4: rejection reason to failed obligation correspondence. -/
def rejectionReasonObligation : AdmissionRejectionReason → AdmissionObligation
  | .maxDiffExceeded => .withinMaxDiff
  | .eqSafeNotSupported => .eqSafeSupported
  | .missingRequiredProfiles => .requiredProfilesSupported

/-- E4: derive rejection reasons from user capability request + inferred capability. -/
def admissionRejectionReasons
    (dUser : DUser) (dProg : CertifiedEnvelopeCapability) :
    List AdmissionRejectionReason :=
  let r₁ :=
    if dUser.maxRequestedDiff ≤ dProg.maxDiff then [] else [.maxDiffExceeded]
  let r₂ :=
    if (!dUser.eqSafeOnly || dProg.supportsEqSafeOnly) then [] else [.eqSafeNotSupported]
  let r₃ :=
    if dUser.requiredProfiles.all (fun p => p ∈ dProg.supportedProfiles) then [] else [.missingRequiredProfiles]
  r₁ ++ r₂ ++ r₃

/-- E4: diagnostics theorem/spec form for rejection reasons. -/
def DiagnosticsSoundness
    (dUser : DUser) (dProg : CertifiedEnvelopeCapability)
    (failed : AdmissionObligation → Prop) : Prop :=
  ∀ r, r ∈ admissionRejectionReasons dUser dProg → failed (rejectionReasonObligation r)

/-- E4: diagnostics completeness form (every failed obligation is diagnosed). -/
def DiagnosticsCompleteness
    (dUser : DUser) (dProg : CertifiedEnvelopeCapability)
    (failed : AdmissionObligation → Prop) : Prop :=
  ∀ o, failed o → ∃ r, r ∈ admissionRejectionReasons dUser dProg ∧
    rejectionReasonObligation r = o

/-- E4: decidability theorem form for inference/admission procedures. -/
def InferenceAdmissionDecidable
    (input : ProgramCapabilityInput)
    (dUser : DUser) : Type :=
  Prod
    (Decidable (dUserContained dUser (DProg_local input) = true))
    (Decidable (dUserContained dUser (DProg_shard input) = true))

/-- E4: complexity-bound theorem form for inference/admission procedures. -/
def InferenceComplexityBound
    (input : ProgramCapabilityInput)
    (bound : Nat) : Prop :=
  input.localProfiles.length + input.shardedProfiles.length ≤ bound

/-- E4: conservative-extension theorem form for reduced-regime collapse. -/
def ConservativeExtension
    (baseline strengthened : ProgramCapabilityInput) : Prop :=
  baseline = strengthened →
    DProg_local baseline = DProg_local strengthened ∧
    DProg_shard baseline = DProg_shard strengthened

/-- E4: major hypotheses tracked for necessity/minimality analysis. -/
inductive EnvelopeMajorHypothesis where
  | localAdherence
  | shardedAdherence
  | schedulerDeterminism
  | monotonicity
  | fullAbstraction
  deriving Repr, DecidableEq, Inhabited

/-- E4: explicit counterexample witness object for dropped hypotheses. -/
structure HypothesisCounterexample where
  witnessId : String
  explanation : String
  deriving Repr, DecidableEq, Inhabited

/-- E4: hypothesis necessity/minimality theorem form with explicit counterexamples. -/
def HypothesisNecessityMinimality : Prop :=
  ∀ h : EnvelopeMajorHypothesis, ∃ cex : HypothesisCounterexample, cex.explanation ≠ ""

/-- E4: premise bundle for capability inference/admission theorem extraction. -/
structure VMEnvelopeAdmissionPremises (State : Type u) (Obs : Type v) where
  input : ProgramCapabilityInput
  localHypotheses : VMLocalEnvelopeHypotheses State Obs
  shardedHypotheses : VMShardedEnvelopeHypotheses State Obs
  runtimeComplianceLocal : DUser → Prop
  runtimeComplianceSharded : DUser → Prop
  failedObligation : AdmissionObligation → Prop
  localInferenceSoundnessWitness :
    DProgInferenceSoundness_local input localHypotheses
  shardedInferenceSoundnessWitness :
    DProgInferenceSoundness_shard input shardedHypotheses
  localPrincipalCapabilityWitness :
    PrincipalCapabilityProperty (DProg_local input)
      (fun c => CapabilityStrengthens (DProg_local input) c ∧
                CapabilityStrengthens c (DProg_local input))
  shardedPrincipalCapabilityWitness :
    PrincipalCapabilityProperty (DProg_shard input)
      (fun c => CapabilityStrengthens (DProg_shard input) c ∧
                CapabilityStrengthens c (DProg_shard input))
  localAdmissionSoundnessWitness :
    AdmissionSoundness (DProg_local input) runtimeComplianceLocal
  shardedAdmissionSoundnessWitness :
    AdmissionSoundness (DProg_shard input) runtimeComplianceSharded
  localAdmissionCompletenessWitness :
    AdmissionCompleteness (DProg_local input) runtimeComplianceLocal
  shardedAdmissionCompletenessWitness :
    AdmissionCompleteness (DProg_shard input) runtimeComplianceSharded
  diagnosticsSoundnessLocal :
    ∀ dUser, DiagnosticsSoundness dUser (DProg_local input) failedObligation
  diagnosticsSoundnessSharded :
    ∀ dUser, DiagnosticsSoundness dUser (DProg_shard input) failedObligation
  diagnosticsCompletenessLocal :
    ∀ dUser, DiagnosticsCompleteness dUser (DProg_local input) failedObligation
  diagnosticsCompletenessSharded :
    ∀ dUser, DiagnosticsCompleteness dUser (DProg_shard input) failedObligation
  decidabilityWitness :
    ∀ dUser, InferenceAdmissionDecidable input dUser
  complexityBound : Nat
  complexityBoundWitness :
    InferenceComplexityBound input complexityBound
  conservativeExtensionWitness :
    ∀ baseline, ConservativeExtension baseline input
  necessityMinimalityWitness : HypothesisNecessityMinimality

/-- E4: packaged capability inference/admission theorem family. -/
structure VMEnvelopeAdmissionProtocol where
  State : Type u
  Obs : Type v
  premises : VMEnvelopeAdmissionPremises State Obs
  localInferenceSoundness :
    DProgInferenceSoundness_local premises.input premises.localHypotheses :=
      premises.localInferenceSoundnessWitness
  shardedInferenceSoundness :
    DProgInferenceSoundness_shard premises.input premises.shardedHypotheses :=
      premises.shardedInferenceSoundnessWitness
  localPrincipalCapability :
    PrincipalCapabilityProperty (DProg_local premises.input)
      (fun c => CapabilityStrengthens (DProg_local premises.input) c ∧
                CapabilityStrengthens c (DProg_local premises.input)) :=
      premises.localPrincipalCapabilityWitness
  shardedPrincipalCapability :
    PrincipalCapabilityProperty (DProg_shard premises.input)
      (fun c => CapabilityStrengthens (DProg_shard premises.input) c ∧
                CapabilityStrengthens c (DProg_shard premises.input)) :=
      premises.shardedPrincipalCapabilityWitness
  localAdmissionSoundness :
    AdmissionSoundness (DProg_local premises.input) premises.runtimeComplianceLocal :=
      premises.localAdmissionSoundnessWitness
  shardedAdmissionSoundness :
    AdmissionSoundness (DProg_shard premises.input) premises.runtimeComplianceSharded :=
      premises.shardedAdmissionSoundnessWitness
  localAdmissionCompleteness :
    AdmissionCompleteness (DProg_local premises.input) premises.runtimeComplianceLocal :=
      premises.localAdmissionCompletenessWitness
  shardedAdmissionCompleteness :
    AdmissionCompleteness (DProg_shard premises.input) premises.runtimeComplianceSharded :=
      premises.shardedAdmissionCompletenessWitness
  decidability :
    ∀ dUser, InferenceAdmissionDecidable premises.input dUser :=
      premises.decidabilityWitness
  complexity :
    InferenceComplexityBound premises.input premises.complexityBound :=
      premises.complexityBoundWitness
  conservativeExtension :
    ∀ baseline, ConservativeExtension baseline premises.input :=
      premises.conservativeExtensionWitness
  necessityMinimality : HypothesisNecessityMinimality :=
    premises.necessityMinimalityWitness

/-- Abstract failure taxonomy shared across Lean/Rust runtime surfaces. -/
inductive FailureClass where
  | typeViolation
  | unknownLabel
  | channelClosed
  | signatureInvalid
  | verificationFailed
  | guardFault
  | invokeFault
  | transferFault
  | closeFault
  | specFault
  | flowViolation
  | noProgressToken
  | outputConditionFault
  | outOfRegisters
  | pcOutOfBounds
  | bufferFull
  | outOfCredits
  | topologyMutation
  | transportCorruption
  | transportTimeout
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- Commit certainty abstraction used by failure/recovery reasoning. -/
inductive CommitCertainty where
  | certain
  | boundedDiff
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- Abstract recovery action vocabulary (policy-level). -/
inductive RecoveryAction where
  | continue
  | retryAfter (ticks : Nat)
  | closeSession (sid : Nat)
  | quarantineEdge
  | abort
  deriving Repr, DecidableEq, Inhabited

/-- Machine-stable error code schema shared by Lean model and Rust runtime. -/
inductive ErrorCode where
  | typeViolation
  | unknownLabel
  | channelClosed
  | invalidSignature
  | verificationFailed
  | acquireFault
  | invokeFault
  | transferFault
  | closeFault
  | specFault
  | flowViolation
  | noProgressToken
  | outputConditionFault
  | outOfRegisters
  | pcOutOfBounds
  | bufferFull
  | outOfCredits
  | topologyMutation
  | transportCorruption
  | transportTimeout
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- Stable wire/string representation for cross-target artifacts. -/
def errorCodeString : ErrorCode → String
  | .typeViolation => "type_violation"
  | .unknownLabel => "unknown_label"
  | .channelClosed => "channel_closed"
  | .invalidSignature => "invalid_signature"
  | .verificationFailed => "verification_failed"
  | .acquireFault => "acquire_fault"
  | .invokeFault => "invoke_fault"
  | .transferFault => "transfer_fault"
  | .closeFault => "close_fault"
  | .specFault => "spec_fault"
  | .flowViolation => "flow_violation"
  | .noProgressToken => "no_progress_token"
  | .outputConditionFault => "output_condition_fault"
  | .outOfRegisters => "out_of_registers"
  | .pcOutOfBounds => "pc_out_of_bounds"
  | .bufferFull => "buffer_full"
  | .outOfCredits => "out_of_credits"
  | .topologyMutation => "topology_mutation"
  | .transportCorruption => "transport_corruption"
  | .transportTimeout => "transport_timeout"
  | .unknown => "unknown_fault"

/-- Structured evidence record for deterministic recovery decisions. -/
structure RecoveryEvidence where
  code : ErrorCode
  failureClass : FailureClass
  certainty : CommitCertainty
  detail : String
  tick : Nat
  source : String
  deriving Repr, DecidableEq, Inhabited

/-- Map abstract failure classes to machine-stable error codes. -/
def errorCodeOfFailureClass : FailureClass → ErrorCode
  | .typeViolation => .typeViolation
  | .unknownLabel => .unknownLabel
  | .channelClosed => .channelClosed
  | .signatureInvalid => .invalidSignature
  | .verificationFailed => .verificationFailed
  | .guardFault => .acquireFault
  | .invokeFault => .invokeFault
  | .transferFault => .transferFault
  | .closeFault => .closeFault
  | .specFault => .specFault
  | .flowViolation => .flowViolation
  | .noProgressToken => .noProgressToken
  | .outputConditionFault => .outputConditionFault
  | .outOfRegisters => .outOfRegisters
  | .pcOutOfBounds => .pcOutOfBounds
  | .bufferFull => .bufferFull
  | .outOfCredits => .outOfCredits
  | .topologyMutation => .topologyMutation
  | .transportCorruption => .transportCorruption
  | .transportTimeout => .transportTimeout
  | .unknown => .unknown

/-- Total mapping from Lean VM instruction faults to abstract failure classes. -/
def failureClassOfLeanFault {γ : Type u} : _root_.Fault γ → FailureClass
  | .typeViolation _ _ => .typeViolation
  | .unknownLabel _ => .unknownLabel
  | .channelClosed _ => .channelClosed
  | .invalidSignature _ => .signatureInvalid
  | .acquireFault _ _ => .guardFault
  | .invokeFault _ => .invokeFault
  | .transferFault _ => .transferFault
  | .closeFault _ => .closeFault
  | .specFault _ => .specFault
  | .flowViolation _ => .flowViolation
  | .noProgressToken _ => .noProgressToken
  | .outOfCredits => .outOfCredits
  | .outOfRegisters => .outOfRegisters

/-- Total mapping from Lean ingress failure events to abstract failure classes. -/
def failureClassOfLeanIngressFailure {ι : Type u} [IdentityModel ι] :
    _root_.Failure ι → FailureClass
  | .siteCrash _ => .topologyMutation
  | .partition _ => .topologyMutation
  | .heal _ => .topologyMutation
  | .corrupt _ _ => .transportCorruption
  | .timeout _ _ => .transportTimeout

/-- Rust fault tags mirrored for total cross-target classification mapping. -/
inductive RustFaultTag where
  | typeViolation
  | unknownLabel
  | channelClosed
  | invalidSignature
  | verificationFailed
  | invokeFault
  | acquireFault
  | transferFault
  | specFault
  | closeFault
  | flowViolation
  | noProgressToken
  | outputConditionFault
  | outOfRegisters
  | pcOutOfBounds
  | bufferFull
  | outOfCredits
  deriving Repr, DecidableEq, Inhabited

/-- Total mapping from Rust fault tags to abstract failure classes. -/
def failureClassOfRustFaultTag : RustFaultTag → FailureClass
  | .typeViolation => .typeViolation
  | .unknownLabel => .unknownLabel
  | .channelClosed => .channelClosed
  | .invalidSignature => .signatureInvalid
  | .verificationFailed => .verificationFailed
  | .invokeFault => .invokeFault
  | .acquireFault => .guardFault
  | .transferFault => .transferFault
  | .specFault => .specFault
  | .closeFault => .closeFault
  | .flowViolation => .flowViolation
  | .noProgressToken => .noProgressToken
  | .outputConditionFault => .outputConditionFault
  | .outOfRegisters => .outOfRegisters
  | .pcOutOfBounds => .pcOutOfBounds
  | .bufferFull => .bufferFull
  | .outOfCredits => .outOfCredits

/-- Lean fault mapped to a machine-stable shared error code. -/
def errorCodeOfLeanFault {γ : Type u} (f : _root_.Fault γ) : ErrorCode :=
  errorCodeOfFailureClass (failureClassOfLeanFault f)

/-- Rust fault tag mapped to a machine-stable shared error code. -/
def errorCodeOfRustFaultTag (f : RustFaultTag) : ErrorCode :=
  errorCodeOfFailureClass (failureClassOfRustFaultTag f)

/-- Abstract state transformer used by recovery/action theorems. -/
abbrev RecoveryStep (State : Type u) := State → RecoveryAction → State

/-- Abstract safety theorem form for deterministic recovery actions. -/
def RecoveryActionSafety {State : Type u}
    (Safe : State → Prop)
    (step : RecoveryStep State) : Prop :=
  ∀ st act, Safe st → Safe (step st act)

/-- Preconditions used by no-unsafe-replay theorem forms. -/
structure ReplayPreconditions (State : Type u) where
  nonceFresh : State → Nat → Prop
  reconciled : State → Prop

/-- Abstract no-unsafe-replay theorem form under nonce/reconciliation preconditions. -/
def NoUnsafeReplay {State : Type u}
    (Safe : State → Prop)
    (pre : ReplayPreconditions State)
    (replay : State → Nat → State) : Prop :=
  ∀ st nonce,
    pre.nonceFresh st nonce →
    pre.reconciled st →
    Safe (replay st nonce)

/-- Checkpoint-restart refinement theorem form. -/
def CheckpointRestartRefinement {State : Type u}
    (Refines : State → State → Prop)
    (checkpoint restart : State → State) : Prop :=
  ∀ st, Refines (restart (checkpoint st)) st

/-- Failure-envelope soundness extension over local envelopes. -/
def FailureEnvelopeSoundnessExtension {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop)
    (injectFailure : Run State → Run State) : Prop :=
  ∀ ref impl,
    RefRun ref → ImplRun impl →
    EqEnvLocal E (injectFailure ref) (injectFailure impl)

/-- Failure-envelope maximality extension over local envelopes. -/
def FailureEnvelopeMaximalityExtension {State : Type u} {Obs : Type v}
    (E : LocalEnvelope State Obs)
    (RefRun ImplRun : Run State → Prop)
    (injectFailure : Run State → Run State) : Prop :=
  ∀ R : Run State → Run State → Prop,
    (∀ ref impl,
      RefRun ref → ImplRun impl →
      R ref impl →
      EqEnvLocal E (injectFailure ref) (injectFailure impl)) →
    ∀ ref impl,
      RefRun ref → ImplRun impl →
      R ref impl →
      EqEnvLocal E (injectFailure ref) (injectFailure impl)

/-- Premise bundle for abstract Phase-E8 failure/recovery theorem extraction. -/
structure FailureEnvelopePremises (State : Type u) (Obs : Type v) where
  localEnvelope : LocalEnvelope State Obs
  Safe : State → Prop
  recoveryStep : RecoveryStep State
  replayPre : ReplayPreconditions State
  replay : State → Nat → State
  Refines : State → State → Prop
  checkpoint : State → State
  restart : State → State
  RefRun : Run State → Prop
  ImplRun : Run State → Prop
  injectFailure : Run State → Run State
  recoveryActionSafetyWitness :
    RecoveryActionSafety Safe recoveryStep
  noUnsafeReplayWitness :
    NoUnsafeReplay Safe replayPre replay
  checkpointRestartRefinementWitness :
    CheckpointRestartRefinement Refines checkpoint restart
  failureEnvelopeSoundnessWitness :
    FailureEnvelopeSoundnessExtension localEnvelope RefRun ImplRun injectFailure
  failureEnvelopeMaximalityWitness :
    FailureEnvelopeMaximalityExtension localEnvelope RefRun ImplRun injectFailure

/-- Extract abstract recovery-action safety theorem from failure premises. -/
theorem recoveryActionSafety_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    RecoveryActionSafety p.Safe p.recoveryStep :=
  p.recoveryActionSafetyWitness

/-- Extract abstract no-unsafe-replay theorem from failure premises. -/
theorem noUnsafeReplay_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    NoUnsafeReplay p.Safe p.replayPre p.replay :=
  p.noUnsafeReplayWitness

/-- Extract checkpoint-restart refinement theorem from failure premises. -/
theorem checkpointRestartRefinement_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    CheckpointRestartRefinement p.Refines p.checkpoint p.restart :=
  p.checkpointRestartRefinementWitness

/-- Extract failure-envelope soundness extension theorem from failure premises. -/
theorem failureEnvelopeSoundness_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    FailureEnvelopeSoundnessExtension
      p.localEnvelope p.RefRun p.ImplRun p.injectFailure :=
  p.failureEnvelopeSoundnessWitness

/-- Extract failure-envelope maximality extension theorem from failure premises. -/
theorem failureEnvelopeMaximality_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    FailureEnvelopeMaximalityExtension
      p.localEnvelope p.RefRun p.ImplRun p.injectFailure :=
  p.failureEnvelopeMaximalityWitness

/-- Packaged abstract failure/recovery theorem family. -/
structure FailureEnvelopeProtocol where
  State : Type u
  Obs : Type v
  premises : FailureEnvelopePremises State Obs
  recoveryActionSafety :
    RecoveryActionSafety premises.Safe premises.recoveryStep :=
      recoveryActionSafety_of_failurePremises premises
  noUnsafeReplay :
    NoUnsafeReplay premises.Safe premises.replayPre premises.replay :=
      noUnsafeReplay_of_failurePremises premises
  checkpointRestartRefinement :
    CheckpointRestartRefinement
      premises.Refines premises.checkpoint premises.restart :=
      checkpointRestartRefinement_of_failurePremises premises
  failureEnvelopeSoundness :
    FailureEnvelopeSoundnessExtension
      premises.localEnvelope premises.RefRun premises.ImplRun premises.injectFailure :=
      failureEnvelopeSoundness_of_failurePremises premises
  failureEnvelopeMaximality :
    FailureEnvelopeMaximalityExtension
      premises.localEnvelope premises.RefRun premises.ImplRun premises.injectFailure :=
      failureEnvelopeMaximality_of_failurePremises premises

end Adequacy
end Runtime
