import Runtime.VM.Model.State
import Runtime.VM.Runtime.Failure

set_option autoImplicit false

/-! # Runtime.Adequacy.EnvelopeCore

Core abstract objects for envelope-based adequacy and recovery taxonomy.
-/

/-
The Problem. Envelope statements, VM adherence claims, and capability-admission
contracts need a shared core vocabulary so theorem packages can be expressed once
and instantiated consistently across local/sharded regimes.

Solution Structure. This module defines the abstract envelope relations first,
then layers exactness/bridge theorem forms, capability/admission abstractions,
and finally transport/failure taxonomy objects used by runtime-facing theorem packs.
-/

namespace Runtime
namespace Adequacy

universe u v

/-! ## Core Definitions -/

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

/-- Local/sharded collapse condition: both envelope views induce the same
    erased-observation equivalence on runs. -/
def LocalShardedCollapse {State : Type u} {Obs : Type v}
    (ELocal : LocalEnvelope State Obs)
    (EShard : ShardedEnvelope State Obs) : Prop :=
  ∀ ref impl, EqEnvLocal ELocal ref impl ↔ EqEnvShard EShard ref impl

/-- Transport local exactness into sharded exactness under collapse. -/
theorem shardedExact_of_localExact_and_collapse
    {State : Type u} {Obs : Type v}
    {ELocal : LocalEnvelope State Obs} {EShard : ShardedEnvelope State Obs}
    {RefRun ImplRun : Run State → Prop}
    (hLocal : LocalExactEnvelopeCharacterization ELocal RefRun ImplRun)
    (hCollapse : LocalShardedCollapse ELocal EShard) :
    ShardedExactEnvelopeCharacterization EShard RefRun ImplRun := by
  rcases hLocal with ⟨hSoundL, hRealL, hMaxL⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ref impl hRef hImpl
    exact (hCollapse ref impl).1 (hSoundL ref impl hRef hImpl)
  · intro ref impl hRef hEqShard
    exact hRealL ref impl hRef ((hCollapse ref impl).2 hEqShard)
  · intro R hR ref impl hRef hImpl hRel
    exact hR ref impl hRef hImpl hRel

/-- Transport sharded exactness into local exactness under collapse. -/
theorem localExact_of_shardedExact_and_collapse
    {State : Type u} {Obs : Type v}
    {ELocal : LocalEnvelope State Obs} {EShard : ShardedEnvelope State Obs}
    {RefRun ImplRun : Run State → Prop}
    (hShard : ShardedExactEnvelopeCharacterization EShard RefRun ImplRun)
    (hCollapse : LocalShardedCollapse ELocal EShard) :
    LocalExactEnvelopeCharacterization ELocal RefRun ImplRun := by
  rcases hShard with ⟨hSoundS, hRealS, hMaxS⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ref impl hRef hImpl
    exact (hCollapse ref impl).2 (hSoundS ref impl hRef hImpl)
  · intro ref impl hRef hEqLocal
    exact hRealS ref impl hRef ((hCollapse ref impl).1 hEqLocal)
  · intro R hR ref impl hRef hImpl hRel
    exact hR ref impl hRef hImpl hRel

/-- Exactness collapse equivalence between local and sharded views. -/
theorem localExact_iff_shardedExact_of_collapse
    {State : Type u} {Obs : Type v}
    {ELocal : LocalEnvelope State Obs} {EShard : ShardedEnvelope State Obs}
    {RefRun ImplRun : Run State → Prop}
    (hCollapse : LocalShardedCollapse ELocal EShard) :
    LocalExactEnvelopeCharacterization ELocal RefRun ImplRun ↔
      ShardedExactEnvelopeCharacterization EShard RefRun ImplRun := by
  constructor
  · intro hLocal
    exact shardedExact_of_localExact_and_collapse hLocal hCollapse
  · intro hShard
    exact localExact_of_shardedExact_and_collapse hShard hCollapse

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

end Adequacy
end Runtime
