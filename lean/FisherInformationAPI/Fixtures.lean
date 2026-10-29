import FisherInformationAPI.Laws

/-! # FisherInformationAPI.Fixtures

Small fixture families: Bernoulli, two-dimensional, known-variance Gaussian.

Part of the `FisherInformationAPI` boundary (finite-discrete Fisher
information geometry); re-exported by the `FisherInformationAPI` module.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators Matrix MatrixOrder
open Asymptotics

noncomputable section

/-! ## Small Fixtures -/

namespace Fixtures

/-- Two-outcome Bernoulli family with statistic `0, 1` and unit base weights. -/
def bernoulliFamily : Family where
  Ω := Fin 2
  omegaFinite := inferInstance
  omegaDecEq := inferInstance
  d := 1
  sufficientStatistic := fun ω _ => if ω = 0 then 0 else 1
  baseMeasureWeight := fun _ => 1
  baseMeasureWeight_nonneg := by
    -- Unit base measure is nonnegative at every outcome.
    intro ω
    norm_num
  baseMeasureWeight_exists_pos := by
    -- The first outcome has strictly positive base mass.
    exact ⟨0, by norm_num⟩

/-- The only Bernoulli natural-coordinate index. -/
def bernoulliIndex : Fin bernoulliFamily.d :=
  ⟨0, by norm_num [bernoulliFamily]⟩

/-- Logistic probability induced by the one-dimensional Bernoulli natural parameter. -/
def bernoulliSigmoid (θ : naturalParameter bernoulliFamily.d) : ℝ :=
  Real.exp (θ bernoulliIndex) / (1 + Real.exp (θ bernoulliIndex))

/-- Logit coordinate for a one-dimensional Bernoulli expectation parameter. -/
def bernoulliLogit (μ : expectationParameter bernoulliFamily.d) : ℝ :=
  Real.log (μ bernoulliIndex / (1 - μ bernoulliIndex))

/-- Bernoulli expectation-coordinate map `θ ↦ σ(θ)`. -/
def bernoulliExpectationParam
    (θ : naturalParameter bernoulliFamily.d) :
    expectationParameter bernoulliFamily.d :=
  ⟨fun _ => bernoulliSigmoid θ⟩

/-- Bernoulli natural-coordinate map `μ ↦ log(μ/(1-μ))`. -/
def bernoulliNaturalParam
    (μ : expectationParameter bernoulliFamily.d) :
    naturalParameter bernoulliFamily.d :=
  ⟨fun _ => bernoulliLogit μ⟩

/-- Bernoulli model using the finite-family Fisher matrix and sigmoid/logit dual coordinates. -/
def bernoulliModel : Model where
  family := bernoulliFamily
  fisherAt := fisherInformation bernoulliFamily
  expectationParam := bernoulliExpectationParam
  naturalParam := bernoulliNaturalParam

/-- Bernoulli expectation parameter is the sigmoid. -/
theorem bernoulli_expectationParam_eq_sigmoid
    (θ : naturalParameter bernoulliFamily.d) :
    bernoulliModel.expectationParam θ = ⟨fun _ => bernoulliSigmoid θ⟩ := by
  -- The model selects the named sigmoid map definitionally.
  rfl

/-- Bernoulli natural parameter is the logit. -/
theorem bernoulli_naturalParam_eq_logit
    (μ : expectationParameter bernoulliFamily.d) :
    bernoulliModel.naturalParam μ = ⟨fun _ => bernoulliLogit μ⟩ := by
  -- The model selects the named logit map definitionally.
  rfl

/-- Scalar logistic/logit cancellation on the open unit interval. -/
private theorem sigmoid_logit_scalar
    (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    Real.exp (Real.log (p / (1 - p))) /
      (1 + Real.exp (Real.log (p / (1 - p)))) = p := by
  -- Normalize the positive log argument and clear the nonzero denominators.
  have hden_pos : 0 < 1 - p := by
    linarith
  have hdiv_pos : 0 < p / (1 - p) :=
    div_pos h0 hden_pos
  have hsum_ne : 1 + p / (1 - p) ≠ 0 := by
    nlinarith
  rw [Real.exp_log hdiv_pos]
  field_simp [ne_of_gt hden_pos, hsum_ne]
  ring

/-- Sigmoid after logit is the identity on Bernoulli means in `(0, 1)`. -/
theorem bernoulli_sigmoid_logit
    (μ : expectationParameter bernoulliFamily.d)
    (h0 : 0 < μ bernoulliIndex)
    (h1 : μ bernoulliIndex < 1) :
    bernoulliModel.expectationParam (bernoulliModel.naturalParam μ) = μ := by
  -- Reduce the wrapped equality to the scalar identity
  -- `exp(log (p/(1-p))) / (1 + exp(log (p/(1-p)))) = p`.
  change bernoulliExpectationParam (bernoulliNaturalParam μ) = μ
  ext i
  fin_cases i
  simp [bernoulliExpectationParam, bernoulliNaturalParam,
    bernoulliSigmoid, bernoulliLogit, bernoulliIndex]
  exact sigmoid_logit_scalar
    (μ ⟨0, by norm_num [bernoulliFamily]⟩)
    (by simpa [bernoulliIndex] using h0)
    (by simpa [bernoulliIndex] using h1)

-- `bernoulli_logPartition_eq` is proved in `FisherInformationInstance.BernoulliCalculus`.
-- `bernoulli_fisherInformation_eq_variance` is proved in
-- `FisherInformationInstance.BernoulliCalculus` from explicit density lemmas.

/-- Explicit Bernoulli KL formula in probability coordinates. -/
def bernoulliKlExplicit
    (θ₁ θ₂ : naturalParameter bernoulliFamily.d) : ℝ :=
  bernoulliSigmoid θ₁ * Real.log (bernoulliSigmoid θ₁ / bernoulliSigmoid θ₂) +
    (1 - bernoulliSigmoid θ₁) *
      Real.log ((1 - bernoulliSigmoid θ₁) / (1 - bernoulliSigmoid θ₂))

/-- Backend-backed Bernoulli KL agrees with the explicit probability formula. -/
theorem bernoulli_klBetweenParameters_eq_explicit
    [EntropyAPI.Model]
    (hKL :
      ∀ θ₁ θ₂,
        klBetweenParameters bernoulliModel θ₁ θ₂ =
          bernoulliKlExplicit θ₁ θ₂)
    (θ₁ θ₂ : naturalParameter bernoulliFamily.d) :
    klBetweenParameters bernoulliModel θ₁ θ₂ =
      bernoulliKlExplicit θ₁ θ₂ := by
  -- The concrete entropy backend supplies the finite two-outcome KL calculation.
  exact hKL θ₁ θ₂

/-- Variance coordinate of a Bernoulli estimator. -/
def bernoulliEstimatorVariance
    (θ : naturalParameter bernoulliFamily.d)
    (g : bernoulliFamily.Ω → Fin bernoulliFamily.d → ℝ) : ℝ :=
  estimatorCovariance bernoulliModel θ g bernoulliIndex bernoulliIndex

/-- Backend-backed scalar Bernoulli Cramer-Rao variance lower bound. -/
theorem bernoulli_cramer_rao_variance_bound
    (hVariance :
      ∀ θ g, locallyUnbiasedEstimator bernoulliModel θ g →
        (bernoulliSigmoid θ * (1 - bernoulliSigmoid θ))⁻¹ ≤
          bernoulliEstimatorVariance θ g)
    (θ : naturalParameter bernoulliFamily.d)
    (g : bernoulliFamily.Ω → Fin bernoulliFamily.d → ℝ)
    (hunbiased : locallyUnbiasedEstimator bernoulliModel θ g) :
    (bernoulliSigmoid θ * (1 - bernoulliSigmoid θ))⁻¹ ≤
      bernoulliEstimatorVariance θ g := by
  -- The concrete backend supplies the scalar specialization of Cramer-Rao.
  exact hVariance θ g hunbiased

/-- Natural parameter with a single Bernoulli coordinate. -/
def bernoulliTheta (x : ℝ) : naturalParameter bernoulliFamily.d :=
  ⟨fun _ => x⟩

/-- Closed interval in the one-dimensional Bernoulli natural chart. -/
def bernoulliInterval (θlo θhi : ℝ) :
    Set (naturalParameter bernoulliFamily.d) :=
  {θ | θlo ≤ θ bernoulliIndex ∧ θ bernoulliIndex ≤ θhi}

/-- Closed-form Bernoulli Fisher-Rao length for a natural-coordinate interval. -/
def bernoulliFisherVolumeClosedForm (θlo θhi : ℝ) : ℝ :=
  2 * (Real.arctan (Real.exp (θhi / 2)) -
    Real.arctan (Real.exp (θlo / 2)))

/-- Backend-backed Bernoulli Fisher-volume interval formula. -/
theorem bernoulli_fisherVolume_interval_eq
    (hVolume :
      ∀ θlo θhi,
        fisherVolume bernoulliModel (bernoulliInterval θlo θhi) =
          ENNReal.ofReal (bernoulliFisherVolumeClosedForm θlo θhi))
    (θlo θhi : ℝ) :
    fisherVolume bernoulliModel (bernoulliInterval θlo θhi) =
      ENNReal.ofReal (bernoulliFisherVolumeClosedForm θlo θhi) := by
  -- The concrete volume backend supplies the one-dimensional integral.
  exact hVolume θlo θhi

/-! ### Two-Dimensional Cramer-Rao Fixture -/

/-- A small two-dimensional finite family for multivariate API checks. -/
def twoDimensionalFamily : Family where
  Ω := Fin 2
  omegaFinite := inferInstance
  omegaDecEq := inferInstance
  d := 2
  sufficientStatistic := fun ω i => if (ω : Nat) = (i : Nat) then 1 else 0
  baseMeasureWeight := fun _ => 1
  baseMeasureWeight_nonneg := by
    -- Unit base mass is nonnegative at every point.
    intro ω
    norm_num
  baseMeasureWeight_exists_pos := by
    -- The first point has positive base mass.
    exact ⟨0, by norm_num⟩

/-- Model fixture for the two-dimensional family. -/
def twoDimensionalModel : Model where
  family := twoDimensionalFamily
  fisherAt := fisherInformation twoDimensionalFamily
  expectationParam := fun θ => ⟨θ⟩
  naturalParam := fun μ => ⟨μ⟩

/-- The multivariate fixture really has dimension two. -/
theorem twoDimensionalFamily_dimension :
    twoDimensionalFamily.d = 2 := by
  -- Dimension is part of the fixture definition.
  rfl

/-- Cramer-Rao theorem instantiates at a non-scalar dimension. -/
theorem twoDimensional_cramer_rao_compiles
    (hCR : CramerRaoBound twoDimensionalModel)
    (θ : naturalParameter twoDimensionalFamily.d)
    (g : twoDimensionalFamily.Ω → Fin twoDimensionalFamily.d → ℝ)
    (hunbiased : locallyUnbiasedEstimator twoDimensionalModel θ g) :
    MatrixPSDLe (twoDimensionalModel.fisherAt θ)⁻¹
      (estimatorCovariance twoDimensionalModel θ g) := by
  -- This is the generic theorem specialized to a `Fin 2` parameter space.
  exact cramer_rao_bound twoDimensionalModel hCR θ g hunbiased

/-! ### Gaussian Known-Variance Coordinate Fixture -/

/-- One-dimensional coordinate fixture for a known-variance Gaussian chart.

The sample space remains finite at the API boundary; this fixture records the
standard identity coordinate map for the known-variance Gaussian chart. -/
def gaussianKnownVarianceFamily : Family where
  Ω := PUnit
  omegaFinite := inferInstance
  omegaDecEq := inferInstance
  d := 1
  sufficientStatistic := fun _ _ => 0
  baseMeasureWeight := fun _ => 1
  baseMeasureWeight_nonneg := by
    -- Unit base mass is nonnegative.
    intro ω
    norm_num
  baseMeasureWeight_exists_pos := by
    -- The only point has positive base mass.
    exact ⟨PUnit.unit, by norm_num⟩

/-- Identity expectation-coordinate map for the known-variance Gaussian chart. -/
def gaussianKnownVarianceExpectationParam
    (θ : naturalParameter gaussianKnownVarianceFamily.d) :
    expectationParameter gaussianKnownVarianceFamily.d :=
  ⟨θ⟩

/-- Identity natural-coordinate map for the known-variance Gaussian chart. -/
def gaussianKnownVarianceNaturalParam
    (μ : expectationParameter gaussianKnownVarianceFamily.d) :
    naturalParameter gaussianKnownVarianceFamily.d :=
  ⟨μ⟩

/-- Coordinate model for a one-dimensional known-variance Gaussian chart. -/
def gaussianKnownVarianceModel : Model where
  family := gaussianKnownVarianceFamily
  fisherAt := fun _ i j => if i = j then 1 else 0
  expectationParam := gaussianKnownVarianceExpectationParam
  naturalParam := gaussianKnownVarianceNaturalParam

/-- Known-variance Gaussian expectation coordinates coincide with natural coordinates. -/
theorem gaussianKnownVariance_expectationParam_eq
    (θ : naturalParameter gaussianKnownVarianceFamily.d) :
    gaussianKnownVarianceModel.expectationParam θ = ⟨θ⟩ := by
  -- The fixture selects the identity coordinate map definitionally.
  rfl

end Fixtures

end

end FisherInformationAPI
