import Runtime.Shim.ResourceAlgebra
import Runtime.Shim.Invariants

/-!
# WeakestPre: Language Interface and Weakest Preconditions

Axiom shims for the Iris Language typeclass and WP rules.
Retires when: iris.md Task 7, iris_2.md Tasks 9A–9C land.
Unblocks: Tasks 12, 17, 19, 21, 22.
-/

set_option autoImplicit false

universe u

namespace Iris

/-! ## Language Typeclass -/

class Language (Λ : Type u) where
  expr : Type
  val : Type
  state : Type
  of_val : val → expr
  to_val : expr → Option val
  prim_step : expr → state → List (expr × state × List expr)

class EctxLanguage (Λ : Type u) extends Language Λ where
  ectx : Type
  empty_ectx : ectx
  comp_ectx : ectx → ectx → ectx
  fill : ectx → expr → expr
  decomp : expr → ectx × expr

/-! ## Weakest Preconditions -/

axiom wp (Λ : Type u) [Language Λ] (E : Mask) (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp) : iProp

axiom state_interp (Λ : Type u) [Language Λ] (σ : Language.state Λ) : iProp

axiom wp_value (Λ : Type u) [Language Λ] (E : Mask)
    (v : Language.val Λ) (Φ : Language.val Λ → iProp) :
    iProp.entails (Φ v) (wp Λ E (Language.of_val v) Φ)

axiom wp_strong_mono (Λ : Type u) [Language Λ] (E₁ E₂ : Mask) (e : Language.expr Λ)
    (Φ Ψ : Language.val Λ → iProp) (hSub : Mask.subseteq E₁ E₂) :
    iProp.entails
      (iProp.sep (wp Λ E₁ e Φ)
        (iProp.forall fun v => iProp.wand (Φ v) (fupd E₂ E₂ (Ψ v))))
      (wp Λ E₂ e Ψ)

axiom wp_bind (Λ : Type u) [EctxLanguage Λ] (E : Mask)
    (K : EctxLanguage.ectx Λ) (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp) :
    iProp.entails
      (wp Λ E e (fun v => wp Λ E (EctxLanguage.fill K (Language.of_val v)) Φ))
      (wp Λ E (EctxLanguage.fill K e) Φ)

axiom wp_frame_l (Λ : Type u) [Language Λ] (E : Mask) (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp) (R : iProp) :
    iProp.entails (iProp.sep R (wp Λ E e Φ)) (wp Λ E e (fun v => iProp.sep R (Φ v)))

axiom wp_fupd (Λ : Type u) [Language Λ] (E : Mask) (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp) :
    iProp.entails (wp Λ E e (fun v => fupd E E (Φ v))) (wp Λ E e Φ)

axiom wp_lift_step (Λ : Type u) [Language Λ] (E : Mask) (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp)
    (hNotVal : Language.to_val e = none) :
    iProp.entails
      (iProp.forall fun σ =>
        iProp.wand (state_interp Λ σ)
          (fupd E Mask.empty
            (iProp.sep
              (iProp.pure (Language.prim_step e σ ≠ []))
              (iProp.forall fun eσefs =>
                iProp.wand
                  (iProp.pure (eσefs ∈ Language.prim_step e σ))
                  (fupd Mask.empty E
                    (iProp.sep (state_interp Λ eσefs.2.1)
                      (iProp.sep (wp Λ E eσefs.1 Φ)
                        (big_sepL (fun e' => wp Λ Mask.top e' (fun _ => iProp.emp))
                          eσefs.2.2))))))))
      (wp Λ E e Φ)

/-! ## Adequacy -/

axiom MultiStep {Λ : Type u} [Language Λ] :
    Language.expr Λ → Language.state Λ → Language.val Λ → Language.state Λ → Prop
axiom MultiStep' {Λ : Type u} [Language Λ] :
    Language.expr Λ → Language.state Λ → Language.expr Λ → Language.state Λ → Prop

axiom wp_adequacy (Λ : Type u) [Language Λ]
    (e : Language.expr Λ) (σ : Language.state Λ)
    (Φ : Language.val Λ → iProp) (φ : Language.val Λ → Prop)
    (hWP : iProp.entails iProp.emp (iProp.wand (state_interp Λ σ) (wp Λ Mask.top e Φ)))
    (hPost : ∀ v, iProp.entails (Φ v) (iProp.pure (φ v))) :
    ∀ v σ', MultiStep e σ v σ' → φ v

axiom wp_invariance (Λ : Type u) [Language Λ]
    (e : Language.expr Λ) (σ : Language.state Λ)
    (Φ : Language.val Λ → iProp)
    (hWP : iProp.entails iProp.emp (iProp.wand (state_interp Λ σ) (wp Λ Mask.top e Φ))) :
    ∀ e' σ', MultiStep' e σ e' σ' →
      iProp.entails iProp.emp (bupd (state_interp Λ σ'))

end Iris
