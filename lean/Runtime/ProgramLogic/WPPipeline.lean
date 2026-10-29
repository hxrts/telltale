import Runtime.ProgramLogic.WPPair
import IrisExtractionInstance

/-! # Runtime.ProgramLogic.WPPipeline

Sequentially composed weakest-precondition pipelines built from `InstrPair`s.
-/

/-
The Problem. Composed WP rules like send pipelines duplicate the open/interact/close
reasoning of each instruction rule, and a plain separating conjunction of stage
rules carries no sequencing: nothing forces stage `i`'s postcondition to feed
stage `i+1`'s precondition.

Solution Structure. `wp_seq p K` is continuation-style sequencing: own `p.pre`,
and once `p.post` holds the continuation `K` (the rest of the pipeline) runs.
Nesting `wp_seq` makes each stage's postcondition the resource from which the
next stage's precondition must be produced. `wp_seq_compose` is the bind rule:
when `p.post ⊢ q.pre`, running `p` then `q` reduces to `p.pre` plus a
continuation for `q.post`.
-/

set_option autoImplicit false
section

open Iris Iris.BI

universe u

variable [Telltale.TelltaleIris]
variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]

/-! ## Sequential Composition -/

/-- Continuation-style stage: own `p.pre`; from `p.post`, continue with `K`. -/
def wp_seq (p : InstrPair γ ε) (K : iProp) : iProp :=
  iProp.sep p.pre (iProp.wand p.post K)

/-- Hand-off condition: stage `p`'s postcondition establishes `q`'s precondition. -/
def StageChains (p q : InstrPair γ ε) : Prop :=
  iProp.entails p.post q.pre

/-- Helper: a continuation for `q.post` yields a continuation for `p.post` that
first runs stage `q`, provided `p.post ⊢ q.pre`. -/
theorem wand_chain (p q : InstrPair γ ε) (K : iProp) (h : StageChains p q) :
    iProp.entails (iProp.wand q.post K) (iProp.wand p.post (wp_seq q K)) := by
  apply _root_.wand_intro
  exact BI.entails_trans (_root_.sep_comm _ _) (_root_.sep_mono _ _ _ _ h BI.entails_refl)

/-- Bind rule: running `p` then `q` reduces to `p.pre` and a continuation for
`q.post`, when `p`'s postcondition establishes `q`'s precondition. -/
theorem wp_seq_compose (p q : InstrPair γ ε) (K : iProp) (h : StageChains p q) :
    iProp.entails (iProp.sep p.pre (iProp.wand q.post K)) (wp_seq p (wp_seq q K)) :=
  _root_.sep_mono _ _ _ _ BI.entails_refl (wand_chain p q K h)

/-- Running a stage: its precondition, the stage's effect `pre ⊢ post`, and the
continuation entail the continuation's goal. -/
theorem wp_seq_run (p : InstrPair γ ε) (K : iProp) (hStep : iProp.entails p.pre p.post) :
    iProp.entails (wp_seq p K) K :=
  BI.entails_trans (_root_.sep_comm _ _)
    (BI.entails_trans (_root_.sep_mono _ _ _ _ BI.entails_refl hStep) (_root_.wand_elim _ _))

/-! ## Send Pipeline -/

/-- Send pipeline: acquire, then invoke, then send, each stage's postcondition
feeding the next stage; `Φ` is the pipeline's postcondition. -/
def wp_send_pipeline (layer : γ) (action : EffectRuntime.EffectAction ε) (Φ : iProp) : iProp :=
  wp_seq (acquirePair (γ:=γ) (ε:=ε) layer)
    (wp_seq (invokePair (γ:=γ) (ε:=ε) action) (wp_seq (sendPair (γ:=γ) (ε:=ε)) Φ))

/-- Pipeline bind: if acquire's post establishes invoke's pre and invoke's post
establishes send's pre, then acquire's pre plus a continuation for send's post
suffices for the whole pipeline. -/
theorem wp_send_pipeline_intro (layer : γ) (action : EffectRuntime.EffectAction ε) (Φ : iProp)
    (h₁ : StageChains (acquirePair (γ:=γ) (ε:=ε) layer) (invokePair action))
    (h₂ : StageChains (invokePair (γ:=γ) (ε:=ε) action) sendPair) :
    iProp.entails
      (iProp.sep (acquirePair (γ:=γ) (ε:=ε) layer).pre (iProp.wand (sendPair (γ:=γ) (ε:=ε)).post Φ))
      (wp_send_pipeline layer action Φ) := by
  apply BI.entails_trans _ (wp_seq_compose _ _ _ h₁)
  exact _root_.sep_mono _ _ _ _ BI.entails_refl (wand_chain _ _ Φ h₂)

/-- The default concrete pairs chain (their pre/postconditions are `emp`). -/
theorem default_pairs_chain (layer : γ) (action : EffectRuntime.EffectAction ε) :
    StageChains (acquirePair (γ:=γ) (ε:=ε) layer) (invokePair action) ∧
      StageChains (invokePair (γ:=γ) (ε:=ε) action) sendPair :=
  ⟨BI.entails_refl, BI.entails_refl⟩

end
