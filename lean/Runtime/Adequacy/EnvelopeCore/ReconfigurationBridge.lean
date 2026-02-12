import Runtime.Adequacy.EnvelopeCore.CoreFoundations

/-! # Reconfiguration Bridge

Role renaming, envelope bound composition, and reconfiguration invariants
for envelope-preserving protocol transformations. -/

/-
The Problem. Protocol reconfigurations (role swaps, state migrations)
must preserve envelope bounds. We need to formalize what transformations
are envelope-safe and prove composition properties.

Solution Structure. Define `RoleRenaming` with inverse proofs. Provide
`RoleRenamableState` class for state-level renaming. Define invariance
and compositional bound properties for envelope analysis.
-/

set_option autoImplicit false

namespace Runtime
namespace Adequacy

universe u v

/-! ## Role Renaming -/

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

/-! ## Envelope Bound Composition -/

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

/-- Non-vacuous exactness conclusion used by strictness/counterexample statements. -/
def CompositionalExactnessConclusion {State : Type u}
    (component₁ component₂ total : EnvelopeBound State) : Prop :=
  ∀ ref impl, total ref impl = component₁ ref impl + component₂ ref impl

/-- Boundary witness for the non-interference converse:
    a concrete pair where both components are active and exactness fails. -/
structure NonInterferenceConverseWitness {State : Type u}
    (component₁ component₂ interaction total : EnvelopeBound State) where
  ref : Run State
  impl : Run State
  component₁_active : component₁ ref impl ≠ 0
  component₂_active : component₂ ref impl ≠ 0
  interaction_zero : interaction ref impl = 0
  exactness_failure : total ref impl ≠ component₁ ref impl + component₂ ref impl

/-! ## Non-Interference Converse -/

/-- Oracle packaging: if non-interference is dropped, a strict witness can be produced. -/
def NonInterferenceConverseOracle {State : Type u}
    (component₁ component₂ interaction total : EnvelopeBound State) : Prop :=
  ¬ NonInterference component₁ component₂ →
    Nonempty (NonInterferenceConverseWitness component₁ component₂ interaction total)

/-- Exactness follows when the composed bound is exact and interaction vanishes. -/
theorem compositionalExactness_of_zeroInteraction
    {State : Type u}
    {component₁ component₂ interaction total : EnvelopeBound State}
    (hComp : CompositionalEnvelopeBound component₁ component₂ interaction total) :
    CompositionalExactnessUnderNonInterference component₁ component₂ interaction total := by
  intro _hNI hZero ref impl
  simpa [hZero ref impl] using hComp ref impl

/-- Any strict converse witness certifies that unconditional compositional exactness fails. -/
theorem not_compositionalExactnessConclusion_of_nonInterferenceConverseWitness
    {State : Type u}
    {component₁ component₂ interaction total : EnvelopeBound State}
    (w : NonInterferenceConverseWitness component₁ component₂ interaction total) :
    ¬ CompositionalExactnessConclusion component₁ component₂ total := by
  intro hExact
  exact w.exactness_failure (hExact w.ref w.impl)

/-- Converse strictness packaging used by S2:
    if non-interference is absent and a witness oracle is available,
    the exactness conclusion is not derivable. -/
theorem nonInterference_converse_strictness_of_oracle
    {State : Type u}
    {component₁ component₂ interaction total : EnvelopeBound State}
    (hOracle : NonInterferenceConverseOracle component₁ component₂ interaction total)
    (hNotNI : ¬ NonInterference component₁ component₂) :
    ¬ CompositionalExactnessConclusion component₁ component₂ total := by
  rcases hOracle hNotNI with ⟨w⟩
  exact not_compositionalExactnessConclusion_of_nonInterferenceConverseWitness w

/-! ## Reconfiguration Harmony Side-Condition Necessity -/

/-- Indexed side conditions for the reconfiguration-Harmony theorem shape. -/
inductive HarmonySideCondition where
  | typedState
  | wellFormedReconfiguration
  | enabledPostReconfigStep
  deriving Repr, DecidableEq, Inhabited

/-- Generic reconfiguration-Harmony commutation contract. -/
def ReconfigurationHarmony {State : Type u} {Obs : Type v}
    (project : State → Obs)
    (globalStep : State → State → Prop)
    (localStep : Obs → Obs → Prop) : Prop :=
  ∀ C C', globalStep C C' → localStep (project C) (project C')

/-- Counterexample witness indexed by a dropped Harmony side condition. -/
structure HarmonyDroppedConditionCounterexample {State : Type u} {Obs : Type v}
    (project : State → Obs)
    (globalStep : State → State → Prop)
    (localStep : Obs → Obs → Prop)
    (conditions : HarmonySideCondition → Prop) where
  droppedCondition : HarmonySideCondition
  source : State
  target : State
  conditionDropped : ¬ conditions droppedCondition
  globalTransition : globalStep source target
  localTransitionFailure : ¬ localStep (project source) (project target)

/-- Oracle packaging: each dropped condition has a corresponding strict witness. -/
def HarmonySideConditionNecessityOracle {State : Type u} {Obs : Type v}
    (project : State → Obs)
    (globalStep : State → State → Prop)
    (localStep : Obs → Obs → Prop)
    (conditions : HarmonySideCondition → Prop) : Prop :=
  ∀ c : HarmonySideCondition, ¬ conditions c →
    Nonempty (HarmonyDroppedConditionCounterexample project globalStep localStep conditions)

/-! ## Harmony Necessity Theorems -/

/-- Any dropped-condition witness certifies Harmony failure. -/
theorem not_reconfigurationHarmony_of_dropped_condition_counterexample
    {State : Type u} {Obs : Type v}
    {project : State → Obs}
    {globalStep : State → State → Prop}
    {localStep : Obs → Obs → Prop}
    {conditions : HarmonySideCondition → Prop}
    (w : HarmonyDroppedConditionCounterexample project globalStep localStep conditions) :
    ¬ ReconfigurationHarmony project globalStep localStep := by
  intro hHarmony
  exact w.localTransitionFailure (hHarmony w.source w.target w.globalTransition)

/-- Side-condition necessity decomposition for Harmony:
    dropping any indexed condition yields a strict non-Harmony witness. -/
theorem reconfigurationHarmony_side_condition_necessity
    {State : Type u} {Obs : Type v}
    {project : State → Obs}
    {globalStep : State → State → Prop}
    {localStep : Obs → Obs → Prop}
    {conditions : HarmonySideCondition → Prop}
    (hOracle : HarmonySideConditionNecessityOracle project globalStep localStep conditions) :
    ∀ c : HarmonySideCondition, ¬ conditions c →
      ¬ ReconfigurationHarmony project globalStep localStep := by
  intro c hDropped
  rcases hOracle c hDropped with ⟨w⟩
  exact not_reconfigurationHarmony_of_dropped_condition_counterexample w

/-! ## E1 Envelope Bridge Interfaces -/

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

/-! ## E1 Bridge Premises Record -/

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

/-! ## E1 Bridge Premise Projections -/

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

/-! ## Protocol Semantics Interfaces (E2) -/

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

/-! ## Protocol Semantics Properties (E2.1-E2.6) -/

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

/-! ## Protocol Envelope Premises -/

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

/-! ## Protocol Bridge Theorem Projections -/

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

/-! ## Protocol Bridge Bundle -/

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

end Adequacy
end Runtime
