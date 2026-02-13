import SessionCoTypes.CoinductiveRel

/-! # Runtime.Proofs.EffectBisim.Core

Coinductive behavioral equivalence for effectful runtime configurations.
-/

/-
The Problem. We need a reusable coinductive equivalence notion at the
Protocol/Runtime boundary to reason about unbounded interactive behavior
without rewriting finite-step preservation stacks.

Solution Structure. Define an observation interface `EffectObs`, a standard
strong-bisimulation endofunctor `EffectBisimF`, and interpret `EffectBisim` as
its greatest fixed point. Prove core laws (unfold, observational soundness,
reflexivity, symmetry, transitivity, equivalence).
-/

set_option autoImplicit false
set_option linter.dupNamespace false

open SessionCoTypes.CoinductiveRel

namespace Runtime.Proofs.EffectBisim

section

universe u v

/-! ## Relation Primitives -/

/-- Binary relation on states. -/
abbrev StateRel (σ : Type u) := σ → σ → Prop

/-- Observation interface used to compare effectful states. -/
structure EffectObs (σ : Type u) (α : Type v) where
  observe : σ → α

/-- Observation-level equivalence induced by `EffectObs`. -/
def ObservationalEq {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (s t : σ) : Prop :=
  obs.observe s = obs.observe t

/-- Relational converse. -/
def RelInv {σ : Type u} (R : StateRel σ) : StateRel σ :=
  fun s t => R t s

/-- Relational composition. -/
def RelComp {σ : Type u} (R S : StateRel σ) : StateRel σ :=
  fun s u => ∃ t, R s t ∧ S t u

/-! ## Coinductive Carrier -/

/-- Strong bisimulation body functor for a step relation and observer. -/
def EffectBisimF {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) (R : StateRel σ) : StateRel σ :=
  fun s t =>
    ObservationalEq obs s t ∧
    (∀ s', step s s' → ∃ t', step t t' ∧ R s' t') ∧
    (∀ t', step t t' → ∃ s', step s s' ∧ R s' t')

instance effectBisimF_coinductiveRel {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) :
    CoinductiveRel (StateRel σ) (EffectBisimF obs step) where
  mono := by
    intro R S hRS s t h
    rcases h with ⟨hObs, hFwd, hBwd⟩
    refine ⟨hObs, ?_, ?_⟩
    · intro s' hStep
      rcases hFwd s' hStep with ⟨t', hStep', hRel⟩
      exact ⟨t', hStep', hRS _ _ hRel⟩
    · intro t' hStep
      rcases hBwd t' hStep with ⟨s', hStep', hRel⟩
      exact ⟨s', hStep', hRS _ _ hRel⟩

/-- Coinductive effect bisimulation (greatest fixed point). -/
def EffectBisim {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) : StateRel σ :=
  gfp (F := EffectBisimF obs step)

/-! ## Unfold and Fold Laws -/

/-- Unfold law for `EffectBisim`. -/
theorem effectBisim_unfold {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    {s t : σ} (h : EffectBisim obs step s t) :
    EffectBisimF obs step (EffectBisim obs step) s t := by
  have hFixed :
      EffectBisimF obs step (gfp (F := EffectBisimF obs step)) =
        gfp (F := EffectBisimF obs step) :=
    gfp_fixed (F := EffectBisimF obs step)
  have h' : gfp (F := EffectBisimF obs step) s t := by
    simpa [EffectBisim] using h
  have : EffectBisimF obs step (gfp (F := EffectBisimF obs step)) s t := by
    simpa [hFixed] using h'
  simpa [EffectBisim] using this

/-- Fold law for `EffectBisim`. -/
theorem effectBisim_fold {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    {s t : σ} (h : EffectBisimF obs step (EffectBisim obs step) s t) :
    EffectBisim obs step s t := by
  have hFixed :
      EffectBisimF obs step (gfp (F := EffectBisimF obs step)) =
        gfp (F := EffectBisimF obs step) :=
    gfp_fixed (F := EffectBisimF obs step)
  have h' : EffectBisimF obs step (gfp (F := EffectBisimF obs step)) s t := by
    simpa [EffectBisim] using h
  have : gfp (F := EffectBisimF obs step) s t := by
    simpa [hFixed] using h'
  simpa [EffectBisim] using this

/-! ## Core Consequences -/

/-- Bisimilar states are observationally equivalent. -/
theorem effectBisim_observationalEq {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    {s t : σ} (h : EffectBisim obs step s t) :
    ObservationalEq obs s t := by
  exact (effectBisim_unfold obs step h).1

/-! ### Reflexivity -/

private theorem eq_postfixed {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) :
    (fun s t : σ => s = t) ≤ EffectBisimF obs step (fun s t : σ => s = t) := by
  intro s t hEq
  subst hEq
  refine ⟨rfl, ?_, ?_⟩
  · intro s' hStep
    exact ⟨s', hStep, rfl⟩
  · intro t' hStep
    exact ⟨t', hStep, rfl⟩

/-- `EffectBisim` is reflexive. -/
theorem effectBisim_refl {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) (s : σ) :
    EffectBisim obs step s s := by
  have hEqLe : (fun a b : σ => a = b) ≤ EffectBisim obs step :=
    coind (F := EffectBisimF obs step) (S := fun a b : σ => a = b) (eq_postfixed obs step)
  exact hEqLe _ _ rfl

/-! ### Symmetry -/

private theorem relInv_postfixed {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    {R : StateRel σ}
    (hPost : R ≤ EffectBisimF obs step R) :
    RelInv R ≤ EffectBisimF obs step (RelInv R) := by
  intro s t hInv
  have hBase : EffectBisimF obs step R t s := hPost _ _ hInv
  rcases hBase with ⟨hObs, hFwd, hBwd⟩
  refine ⟨hObs.symm, ?_, ?_⟩
  · intro s' hStep
    rcases hBwd s' hStep with ⟨t', hStep', hRel⟩
    exact ⟨t', hStep', hRel⟩
  · intro t' hStep
    rcases hFwd t' hStep with ⟨s', hStep', hRel⟩
    exact ⟨s', hStep', hRel⟩

/-- `EffectBisim` is symmetric. -/
theorem effectBisim_symm {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    {s t : σ} (h : EffectBisim obs step s t) :
    EffectBisim obs step t s := by
  have hPost : EffectBisim obs step ≤ EffectBisimF obs step (EffectBisim obs step) := by
    intro a b hab
    exact effectBisim_unfold obs step hab
  have hInvPost : RelInv (EffectBisim obs step) ≤
      EffectBisimF obs step (RelInv (EffectBisim obs step)) :=
    relInv_postfixed obs step hPost
  have hInvLe : RelInv (EffectBisim obs step) ≤ EffectBisim obs step :=
    coind (F := EffectBisimF obs step)
      (S := RelInv (EffectBisim obs step)) hInvPost
  exact hInvLe _ _ h

/-! ### Transitivity -/

private theorem relComp_postfixed {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    {R S : StateRel σ}
    (hRPost : R ≤ EffectBisimF obs step R)
    (hSPost : S ≤ EffectBisimF obs step S) :
    RelComp R S ≤ EffectBisimF obs step (RelComp R S) := by
  intro s u hComp
  rcases hComp with ⟨t, hR, hS⟩
  rcases hRPost _ _ hR with ⟨hObsR, hRFwd, hRBwd⟩
  rcases hSPost _ _ hS with ⟨hObsS, hSFwd, hSBwd⟩
  refine ⟨hObsR.trans hObsS, ?_, ?_⟩
  · intro s' hStep
    rcases hRFwd s' hStep with ⟨t', htStep, hRt'⟩
    rcases hSFwd t' htStep with ⟨u', huStep, hSu'⟩
    exact ⟨u', huStep, ⟨t', hRt', hSu'⟩⟩
  · intro u' hStep
    rcases hSBwd u' hStep with ⟨t', htStep, hSt'⟩
    rcases hRBwd t' htStep with ⟨s', hsStep, hRs'⟩
    exact ⟨s', hsStep, ⟨t', hRs', hSt'⟩⟩

/-- `EffectBisim` is transitive. -/
theorem effectBisim_trans {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    {s t u : σ}
    (h₁₂ : EffectBisim obs step s t)
    (h₂₃ : EffectBisim obs step t u) :
    EffectBisim obs step s u := by
  have hPost : EffectBisim obs step ≤ EffectBisimF obs step (EffectBisim obs step) := by
    intro a b hab
    exact effectBisim_unfold obs step hab
  have hCompPost :
      RelComp (EffectBisim obs step) (EffectBisim obs step) ≤
        EffectBisimF obs step (RelComp (EffectBisim obs step) (EffectBisim obs step)) :=
    relComp_postfixed obs step hPost hPost
  have hCompLe :
      RelComp (EffectBisim obs step) (EffectBisim obs step) ≤ EffectBisim obs step :=
    coind (F := EffectBisimF obs step)
      (S := RelComp (EffectBisim obs step) (EffectBisim obs step)) hCompPost
  exact hCompLe _ _ ⟨t, h₁₂, h₂₃⟩

/-- Equivalence packaging for `EffectBisim`. -/
theorem effectBisim_equivalence {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) :
    Equivalence (EffectBisim obs step) := by
  refine ⟨effectBisim_refl obs step, ?_, ?_⟩
  · intro s t h
    exact effectBisim_symm obs step h
  · intro s t u h₁₂ h₂₃
    exact effectBisim_trans obs step h₁₂ h₂₃

end

end Runtime.Proofs.EffectBisim
