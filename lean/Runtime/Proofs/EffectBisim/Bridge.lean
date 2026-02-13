import Runtime.Proofs.EffectBisim.Core

/-! # Runtime.Proofs.EffectBisim.Bridge

Bridge lemmas from coinductive effect bisimulation to observation-level results.
-/

/-
The Problem. Downstream runtime/protocol results are often phrased in terms of
observable equality. We need direct bridge theorems so those proofs can consume
`EffectBisim` without unfolding its coinductive definition repeatedly.

Solution Structure. Re-export observational consequences with stable theorem
names intended for downstream composition and paper-facing theorem inventories.
-/

set_option autoImplicit false

namespace Runtime.Proofs.EffectBisim

section

universe u v

/-- Primary bridge theorem: effect bisimulation implies observational equality. -/
theorem effectBisim_implies_observationalEquivalence {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    {s t : σ} (h : EffectBisim obs step s t) :
    ObservationalEq obs s t :=
  effectBisim_observationalEq obs step h

/-- Bidirectional packaging for self-contained API use. -/
theorem observationalEquivalence_of_effectBisim {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    (s t : σ) :
    EffectBisim obs step s t → ObservationalEq obs s t :=
  effectBisim_implies_observationalEquivalence obs step

end

end Runtime.Proofs.EffectBisim
