import Runtime.Adequacy.Adequacy
import Runtime.Proofs.EffectBisim.Bridge

/-! # Runtime.Adequacy.CompileRefinesEffectBisim

Compile/refinement-adjacent observational corollaries via effect bisimulation.
-/

/-
The Problem. Compile/refinement results are often consumed by extensional
(observational) corollaries. We want those corollaries to reuse the coinductive
bridge instead of re-proving observation equality ad hoc.

Solution Structure. A bridge-style corollary parameterized by an effect
observer and step relation. It does not (and previously only pretended to)
depend on `compile_refines`: the conclusion follows from bisimulation alone, so
no compilation hypothesis is taken.
-/

set_option autoImplicit false

section

open Runtime.Proofs.EffectBisim

/-- Observational equivalence of effect-bisimilar states, via the coinductive
    bridge. Intended for comparing a compiled program's run against its
    specification once a bisimulation has been established; no compiler
    refinement premise is needed for this step. -/
theorem compile_refines_observational_eq_of_effect_bisim
    {σ : Type} {α : Type}
    (obs : EffectObs σ α) (step : StateRel σ)
    {s t : σ}
    (hBisim : EffectBisim obs step s t) :
    ObservationalEq obs s t :=
  effect_bisim_implies_observational_equivalence obs step hBisim

end
