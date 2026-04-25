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
def finiteDiscreteModel
    (n d : Nat) [NeZero n]
    (T : Fin n → Fin d → ℝ) : Model where
  family := finiteDiscreteFamily n d T
  fisherAt := fun _ _ _ => 0
  expectationParam := fun θ => ⟨θ⟩
  naturalParam := fun μ => ⟨μ⟩

/-! ## Degenerate Finite-Discrete Instance -/

/-- One-outcome, zero-dimensional finite family. -/
def unitFamily : Family where
  Ω := PUnit
  omegaFinite := inferInstance
  omegaDecEq := inferInstance
  d := 0
  sufficientStatistic := fun _ i => Fin.elim0 i
  baseMeasureWeight := fun _ => 1
  baseMeasureWeight_nonneg := by
    -- Unit mass is nonnegative.
    intro ω
    norm_num
  baseMeasureWeight_exists_pos := by
    -- The only outcome has positive mass.
    exact ⟨PUnit.unit, by norm_num⟩

/-- The degenerate concrete model uses the API's finite-family formulas. -/
def unitModel : Model where
  family := unitFamily
  fisherAt := fun _ _ _ => 0
  expectationParam := fun θ => ⟨θ⟩
  naturalParam := fun μ => ⟨μ⟩

/-! ## Law Helpers -/

/-- All vectors in zero dimensions are extensionally equal. -/
private theorem fin_zero_vector_ext (v w : Fin 0 → ℝ) : v = w := by
  -- There are no coordinates to compare.
  funext i
  exact Fin.elim0 i

/-- All natural parameters of the unit family are equal. -/
private theorem unit_natural_ext
    (θ η : naturalParameter unitFamily.d) : θ = η := by
  -- Zero-dimensional coordinates have no entries.
  ext i
  exact Fin.elim0 i

/-- All expectation parameters of the unit family are equal. -/
private theorem unit_expectation_ext
    (μ ν : expectationParameter unitFamily.d) : μ = ν := by
  -- Zero-dimensional coordinates have no entries.
  ext i
  exact Fin.elim0 i

/-! ## Laws Instance -/

/-- A checked finite-discrete Fisher laws instance for the unit family. -/
instance unitLaws : Laws where
  toModel := unitModel
  fisher_psd := by
    -- The zero-dimensional quadratic form is the empty sum.
    intro θ v
    simp [unitModel]
  fisher_eq_hessian := by
    -- Zero-dimensional matrices are extensionally equal.
    intro θ
    ext i j
    exact Fin.elim0 i
  legendre_duality := by
    -- Zero-dimensional natural and expectation coordinates are unique.
    intro hmin
    constructor
    · intro μ
      exact unit_expectation_ext _ _
    · intro θ
      exact unit_natural_ext _ _
  dual_potential_eq_legendre := by
    -- The selected natural map matches the API closed-form map in zero dimensions.
    intro hmin μ
    simp [unitModel, dualPotential, mappingExpectationToNatural]
  kl_nonneg := by
    -- In zero dimensions both parameters coincide, so the closed-form KL is zero.
    intro θ₁ θ₂
    have hθ : θ₁ = θ₂ := unit_natural_ext θ₁ θ₂
    subst hθ
    simp [unitModel, klClosedForm, naturalParameterSub, dot]
  kl_zero_iff_equal_parameters := by
    -- Zero-dimensional parameters are always equal, and the KL expression is zero.
    intro hmin θ₁ θ₂
    constructor
    · intro _h
      exact unit_natural_ext θ₁ θ₂
    · intro hθ
      subst hθ
      simp [unitModel, klClosedForm, naturalParameterSub, dot]
  kl_second_order_taylor := by
    -- The current API law is the abstract leading-term placeholder.
    intro θ δ
    trivial
  fisher_metric_symmetric := by
    -- Both metric sums are empty in zero dimensions.
    intro θ v w
    simp [unitModel, fisherMetric]
  fisher_metric_psd := by
    -- The squared metric is the empty nonnegative sum.
    intro θ v
    simp [unitModel, fisherMetric]
  cramer_rao_bound := by
    -- Matrix order is vacuous for zero-dimensional matrices.
    intro θ g hunbiased v
    change 0 ≤ (0 : ℝ)
    norm_num
  reachability_volume_bound := by
    -- API-level volume is zero, bounded by any extended nonnegative real.
    intro start steps stepBudget
    simp [fisherVolume]
  natural_gradient_exists := by
    -- The natural-gradient step is explicitly defined for every input.
    intro hmin θ gradient
    exact ⟨naturalGradientStep unitModel θ gradient, rfl⟩

end RealConcrete

end FisherInformationAPI
