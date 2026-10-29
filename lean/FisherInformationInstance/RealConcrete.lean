import FisherInformationAPI

/-! # Fisher Information Real Concrete Instance

Mathlib-backed concrete realizations for finite-discrete Fisher information.
-/

/-
The Problem. The abstract Fisher information API needs at least one checked
concrete realization over finite sample spaces.

Solution Structure.
1. Keep implementation details in this instance file.
2. Package concrete operations and law witnesses for downstream import.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators

namespace RealConcrete

/-! ## General Finite-Discrete Construction -/

/-- Uniform positive base weight for a finite sample space.

The normalized density divides by the partition function, so constant unit
weights represent the same uniform base measure without using real inverse. -/
def uniformBaseWeight (_n : Nat) : ℝ :=
  1

/-- Finite-discrete exponential-family presentation over `Fin n`. -/
def finiteDiscreteFamily
    (n d : Nat) [NeZero n]
    (T : Fin n → Fin d → ℝ) : Family where
  Ω := Fin n
  omegaFinite := inferInstance
  omegaDecEq := inferInstance
  d := d
  sufficientStatistic := T
  baseMeasureWeight := fun _ => uniformBaseWeight n
  baseMeasureWeight_nonneg := by
    -- Constant unit base weights are nonnegative.
    intro ω
    norm_num [uniformBaseWeight]
  baseMeasureWeight_exists_pos := by
    -- Nonempty `Fin n` gives one strictly positive uniform base weight.
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact ⟨⟨0, hn⟩, by norm_num [uniformBaseWeight]⟩

/-- Concrete model operations for a finite-discrete exponential family. -/
noncomputable def finiteDiscreteModel
    (n d : Nat) [NeZero n]
    (T : Fin n → Fin d → ℝ) : Model where
  family := finiteDiscreteFamily n d T
  fisherAt := fisherInformation (finiteDiscreteFamily n d T)
  expectationParam := fun θ => ⟨θ⟩
  naturalParam := fun μ => ⟨μ⟩

/-! ## Canonical Laws Instance

The checked nondegenerate laws instance is `RealConcrete.bernoulliLaws` in
`FisherInformationInstance.BernoulliLaws`. The former zero-dimensional
`unitLaws` instance was removed: every law held trivially on it. -/

end RealConcrete

end FisherInformationAPI
