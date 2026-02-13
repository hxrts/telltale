import Runtime.Proofs.EffectBisim.Core

/-! # Runtime.Proofs.EffectBisim.Congruence

Context-congruence rules for effect bisimulation.
-/

/-
The Problem. To leverage coinduction in the broader runtime/effect architecture,
we need reusable congruence rules showing bisimulation is preserved by standard
composition contexts (sequence, parallel, linking, handler substitution).

Solution Structure. Define a generic context-compatibility contract and prove a
single context-congruence theorem. Then export named corollaries for sequence,
parallel, linking, and handler-substitution contexts.
-/

set_option autoImplicit false

namespace Runtime.Proofs.EffectBisim

section

universe u v

/-! ## Context Compatibility -/

/-- A context is bisimulation-compatible when it preserves observations and
    commutes with steps in both directions. -/
structure EffectBisimContext {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) (ctx : σ → σ) : Prop where
  observe_ctx : ∀ s, obs.observe (ctx s) = obs.observe s
  step_ctx_fwd : ∀ {s s'}, step s s' → step (ctx s) (ctx s')
  step_ctx_bwd : ∀ {s s'}, step (ctx s) s' → ∃ t, step s t ∧ s' = ctx t

/-- Image relation induced by a context over a base relation. -/
def CtxImageRel {σ : Type u} (ctx : σ → σ) (R : StateRel σ) : StateRel σ :=
  fun s t => ∃ a b, s = ctx a ∧ t = ctx b ∧ R a b

private theorem ctxImage_postfixed {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) (ctx : σ → σ)
    (hCtx : EffectBisimContext obs step ctx)
    {R : StateRel σ}
    (hPost : R ≤ EffectBisimF obs step R) :
    CtxImageRel ctx R ≤ EffectBisimF obs step (CtxImageRel ctx R) := by
  intro s t hImg
  rcases hImg with ⟨a, b, hs, ht, hR⟩
  rcases hPost _ _ hR with ⟨hObs, hFwd, hBwd⟩
  subst hs
  subst ht
  refine ⟨?_, ?_, ?_⟩
  · calc
      obs.observe (ctx a) = obs.observe a := hCtx.observe_ctx a
      _ = obs.observe b := hObs
      _ = obs.observe (ctx b) := (hCtx.observe_ctx b).symm
  · intro s' hStep
    rcases hCtx.step_ctx_bwd hStep with ⟨a', haStep, hs'⟩
    rcases hFwd a' haStep with ⟨b', hbStep, hRb'⟩
    refine ⟨ctx b', hCtx.step_ctx_fwd hbStep, ?_⟩
    exact ⟨a', b', hs', rfl, hRb'⟩
  · intro t' hStep
    rcases hCtx.step_ctx_bwd hStep with ⟨b', hbStep, ht'⟩
    rcases hBwd b' hbStep with ⟨a', haStep, hRa'⟩
    refine ⟨ctx a', hCtx.step_ctx_fwd haStep, ?_⟩
    exact ⟨a', b', rfl, ht', hRa'⟩

/-! ## Generic Congruence -/

/-- Generic context congruence for effect bisimulation. -/
theorem effectBisim_congr_context {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) (ctx : σ → σ)
    (hCtx : EffectBisimContext obs step ctx)
    {s t : σ} (h : EffectBisim obs step s t) :
    EffectBisim obs step (ctx s) (ctx t) := by
  have hPost : EffectBisim obs step ≤ EffectBisimF obs step (EffectBisim obs step) := by
    intro a b hab
    exact effectBisim_unfold obs step hab
  have hImgPost : CtxImageRel ctx (EffectBisim obs step) ≤
      EffectBisimF obs step (CtxImageRel ctx (EffectBisim obs step)) :=
    ctxImage_postfixed obs step ctx hCtx hPost
  have hImgLe : CtxImageRel ctx (EffectBisim obs step) ≤ EffectBisim obs step :=
    SessionCoTypes.CoinductiveRel.coind
      (F := EffectBisimF obs step)
      (S := CtxImageRel ctx (EffectBisim obs step)) hImgPost
  exact hImgLe _ _ ⟨s, t, rfl, rfl, h⟩

/-! ## Named Congruence Corollaries -/

/-- Sequence-context congruence. -/
theorem effectBisim_congr_seq {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    (seqCtx : σ → σ)
    (hSeq : EffectBisimContext obs step seqCtx)
    {s t : σ} (h : EffectBisim obs step s t) :
    EffectBisim obs step (seqCtx s) (seqCtx t) :=
  effectBisim_congr_context obs step seqCtx hSeq h

/-- Parallel-context congruence. -/
theorem effectBisim_congr_par {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    (parCtx : σ → σ)
    (hPar : EffectBisimContext obs step parCtx)
    {s t : σ} (h : EffectBisim obs step s t) :
    EffectBisim obs step (parCtx s) (parCtx t) :=
  effectBisim_congr_context obs step parCtx hPar h

/-- Linking-context congruence. -/
theorem effectBisim_congr_link {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    (linkCtx : σ → σ)
    (hLink : EffectBisimContext obs step linkCtx)
    {s t : σ} (h : EffectBisim obs step s t) :
    EffectBisim obs step (linkCtx s) (linkCtx t) :=
  effectBisim_congr_context obs step linkCtx hLink h

/-- Handler-substitution congruence. -/
theorem effectBisim_congr_handler_subst {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    (handlerCtx : σ → σ)
    (hHandler : EffectBisimContext obs step handlerCtx)
    {s t : σ} (h : EffectBisim obs step s t) :
    EffectBisim obs step (handlerCtx s) (handlerCtx t) :=
  effectBisim_congr_context obs step handlerCtx hHandler h

end

end Runtime.Proofs.EffectBisim
