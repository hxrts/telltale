import Runtime.Adequacy.Adequacy
import Runtime.Proofs.EffectBisim.Bridge

/-! # Runtime.Adequacy.CompileRefinesEffectBisim

Compile/refinement-adjacent observational corollaries via effect bisimulation.
-/

/-
The Problem. Compile/refinement results are often consumed by extensional
(observational) corollaries. We want those corollaries to reuse the coinductive
bridge instead of re-proving observation equality ad hoc.

Solution Structure. Keep `compile_refines` unchanged and add a bridge-style
corollary parameterized by an effect observer and step relation.
-/

set_option autoImplicit false

section

open Runtime.Proofs.EffectBisim

/-- Compile/refinement-adjacent corollary: once a comparison context is
    established and states are effect-bisimilar, observational equivalence
    follows directly from the bisimulation bridge. -/
theorem compile_refines_observationalEq_of_effectBisim
    {γ ε ν : Type} [GuardLayer γ] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    (p : Process) (roles : RoleSet) (types : Role → LocalType) (chain : GuardChain γ)
    (_hCompile : compile_refines (γ:=γ) (ε:=ε) (ν:=ν) p roles types chain)
    {σ : Type} {α : Type}
    (obs : EffectObs σ α) (step : StateRel σ)
    {s t : σ}
    (hBisim : EffectBisim obs step s t) :
    ObservationalEq obs s t :=
  effectBisim_implies_observationalEquivalence obs step hBisim

end
