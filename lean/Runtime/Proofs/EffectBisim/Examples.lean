import Runtime.Proofs.EffectBisim.Core

/-! # Runtime.Proofs.EffectBisim.Examples

Small canonical examples for the effect bisimulation API.
-/

/-
The Problem. New coinductive infrastructure is only useful if we have concrete,
readable examples showing how to build bisimulation witnesses.

Solution Structure. Provide two lightweight examples:
1. silent-step parity observer (observation equality suffices),
2. always-progressing increment system with unit observation (all states bisimilar).
-/

set_option autoImplicit false

namespace Runtime.Proofs.EffectBisim

section

/-! ## Example 1: Silent step + parity observation -/

private def silentStep : StateRel Nat :=
  fun _ _ => False

private def parityObs : EffectObs Nat Bool where
  observe := fun n => n % 2 = 0

private theorem parityEq_postfixed :
    (fun n m : Nat => parityObs.observe n = parityObs.observe m) ≤
      EffectBisimF parityObs silentStep
        (fun n m : Nat => parityObs.observe n = parityObs.observe m) := by
  intro n m hEq
  refine ⟨hEq, ?_, ?_⟩
  · intro n' hStep
    cases hStep
  · intro m' hStep
    cases hStep

/-- With no transitions, matching parity observations are bisimilar. -/
theorem parityEq_effectBisim_silent {n m : Nat}
    (hParity : parityObs.observe n = parityObs.observe m) :
    EffectBisim parityObs silentStep n m := by
  have hLift :
      (fun a b : Nat => parityObs.observe a = parityObs.observe b) ≤
        EffectBisim parityObs silentStep :=
    SessionCoTypes.CoinductiveRel.coind
      (F := EffectBisimF parityObs silentStep)
      (S := fun a b : Nat => parityObs.observe a = parityObs.observe b)
      parityEq_postfixed
  exact hLift _ _ hParity

/-! ## Example 2: Increment step + unit observation -/

private def incStep : StateRel Nat :=
  fun n n' => n' = n + 1

private def unitObs : EffectObs Nat Unit where
  observe := fun _ => ()

private theorem true_postfixed_inc :
    (fun _ _ : Nat => True) ≤ EffectBisimF unitObs incStep (fun _ _ : Nat => True) := by
  intro n m _
  refine ⟨rfl, ?_, ?_⟩
  · intro n' hStep
    refine ⟨m + 1, ?_, trivial⟩
    simp [incStep]
  · intro m' hStep
    refine ⟨n + 1, ?_, trivial⟩
    simp [incStep]

/-- Under unit observation and deterministic increment transitions,
    every pair of naturals is bisimilar. -/
theorem allNat_effectBisim_inc (n m : Nat) :
    EffectBisim unitObs incStep n m := by
  have hLift : (fun _ _ : Nat => True) ≤ EffectBisim unitObs incStep :=
    SessionCoTypes.CoinductiveRel.coind
      (F := EffectBisimF unitObs incStep)
      (S := fun _ _ : Nat => True)
      true_postfixed_inc
  exact hLift _ _ trivial

end

end Runtime.Proofs.EffectBisim
