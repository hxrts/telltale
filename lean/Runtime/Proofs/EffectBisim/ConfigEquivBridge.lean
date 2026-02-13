import Runtime.Proofs.EffectBisim.Core
import Protocol.Coherence.Conserved

/-! # Runtime.Proofs.EffectBisim.ConfigEquivBridge

Bridge between protocol-level `ConfigEquiv` quotienting and effect bisimulation.
-/

/-
The Problem. The coinductive effect layer must respect the existing protocol
quotient (`ConfigEquiv`) so we can transport equivalence claims cleanly between
protocol and runtime statements.

Solution Structure. Use `observationalErasure` as the observer and a silent
(step-free) transition relation. Prove a two-way correspondence:
`ConfigEquiv` iff silent `EffectBisim` at the erasure observer.
-/

set_option autoImplicit false

namespace Runtime.Proofs.EffectBisim

section

/-- Silent transition relation for quotient-level compatibility lemmas. -/
def configSilentStep : StateRel CoherenceConfig :=
  fun _ _ => False

/-- Observer that maps configurations to their `ConfigEquiv` quotient class. -/
def configErasureObs : EffectObs CoherenceConfig (Quotient ConfigEquivSetoid) where
  observe := observationalErasure

private theorem erasureEq_postfixed :
    (fun C₁ C₂ : CoherenceConfig => observationalErasure C₁ = observationalErasure C₂) ≤
      EffectBisimF configErasureObs configSilentStep
        (fun C₁ C₂ : CoherenceConfig => observationalErasure C₁ = observationalErasure C₂) := by
  intro C₁ C₂ hEq
  refine ⟨hEq, ?_, ?_⟩
  · intro C' hStep
    cases hStep
  · intro C' hStep
    cases hStep

/-- `ConfigEquiv` implies silent effect bisimulation at the erasure observer. -/
theorem configEquiv_effectBisim_silent {C₁ C₂ : CoherenceConfig}
    (hEq : ConfigEquiv C₁ C₂) :
    EffectBisim configErasureObs configSilentStep C₁ C₂ := by
  have hLift :
      (fun A B : CoherenceConfig => observationalErasure A = observationalErasure B) ≤
        EffectBisim configErasureObs configSilentStep :=
    SessionCoTypes.CoinductiveRel.coind
      (F := EffectBisimF configErasureObs configSilentStep)
      (S := fun A B : CoherenceConfig => observationalErasure A = observationalErasure B)
      erasureEq_postfixed
  have hQuot : observationalErasure C₁ = observationalErasure C₂ := by
    change ConfigEquivSetoid.r C₁ C₂ at hEq
    exact Quotient.sound hEq
  exact hLift _ _ hQuot

/-- Silent effect bisimulation at erasure observer implies `ConfigEquiv`. -/
theorem configEquiv_of_effectBisim_silent {C₁ C₂ : CoherenceConfig}
    (hBisim : EffectBisim configErasureObs configSilentStep C₁ C₂) :
    ConfigEquiv C₁ C₂ := by
  have hObs : observationalErasure C₁ = observationalErasure C₂ :=
    effectBisim_observationalEq configErasureObs configSilentStep hBisim
  exact Quotient.exact hObs

/-- Quotient compatibility package: protocol `ConfigEquiv` iff silent
    effect bisimulation at the erasure observer. -/
theorem configEquiv_iff_effectBisim_silent (C₁ C₂ : CoherenceConfig) :
    ConfigEquiv C₁ C₂ ↔ EffectBisim configErasureObs configSilentStep C₁ C₂ := by
  constructor
  · exact configEquiv_effectBisim_silent
  · exact configEquiv_of_effectBisim_silent

end

end Runtime.Proofs.EffectBisim
