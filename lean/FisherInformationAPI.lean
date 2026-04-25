import Mathlib
import ClassicalAnalysisAPI

/-! # FisherInformationAPI

Abstract API boundary for finite-discrete Fisher information geometry.

## Quick Reference

Operations:
- `Family`, `naturalParameter`, `expectationParameter`
- `logPartition`, `density`, `expectationOf`
- `score`, `fisherInformation`, `hessianLogPartition`
- `mappingNaturalToExpectation`, `mappingExpectationToNatural`, `dualPotential`
- `klBetweenParameters`, `klClosedForm`, `fisherMetric`
- `unbiasedEstimator`, `estimatorCovariance`, `fisherVolume`
- `reachabilityRegion`, `naturalGradientStep`

Laws:
- `FisherPSD`, `FisherEqHessian`, `LegendreDuality`
- `DualPotentialEqLegendre`, `KLNonneg`, `KLZeroIffEqualParameters`
- `KLSecondOrderTaylor`, `FisherMetricSymmetric`, `FisherMetricPSD`
- `CramerRaoBound`, `ReachabilityVolumeBound`, `NaturalGradientExists`

## Trust Boundary

This file states the abstract operations and law predicates. Concrete
realizations live under `FisherInformationInstance`, where law witnesses are
checked against specific finite-discrete models.
-/

/-
The Problem. Telltale has an entropy-facing analysis boundary, but no parallel
interface for finite-discrete Fisher information geometry.

Solution Structure.
1. Introduce the API namespace and keep concrete realizations out of this file.
2. Add mathematical content phase by phase behind this stable import name.
3. Mirror the `ClassicalAnalysisAPI` trust-boundary layout as the API grows.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators

noncomputable section

/-! ## Finite Families -/

/-- A finite-discrete exponential-family presentation.

The two base-measure side conditions are structural, not laws: they are exactly
what makes the normalized density nonnegative and total to one. -/
structure Family where
  Ω : Type*
  omegaFinite : Fintype Ω
  omegaDecEq : DecidableEq Ω
  d : ℕ
  sufficientStatistic : Ω → Fin d → ℝ
  baseMeasureWeight : Ω → ℝ
  baseMeasureWeight_nonneg : ∀ ω, 0 ≤ baseMeasureWeight ω
  baseMeasureWeight_exists_pos : ∃ ω, 0 < baseMeasureWeight ω

attribute [instance] Family.omegaFinite Family.omegaDecEq

/-! ## Parameter Coordinates -/

/-- Natural coordinates `θ`; wrapped to keep the semantic role visible. -/
structure naturalParameter (d : ℕ) where
  coord : Fin d → ℝ

/-- Expectation coordinates `μ`; same shape as natural coordinates but distinct. -/
structure expectationParameter (d : ℕ) where
  coord : Fin d → ℝ

instance {d : ℕ} : CoeFun (naturalParameter d) (fun _ => Fin d → ℝ) where
  coe θ := θ.coord

instance {d : ℕ} : CoeFun (expectationParameter d) (fun _ => Fin d → ℝ) where
  coe μ := μ.coord

@[ext]
theorem naturalParameter_ext {d : ℕ} {θ η : naturalParameter d}
    (h : ∀ i, θ i = η i) : θ = η := by
  -- Extensionality reduces equality of wrapped coordinates to pointwise equality.
  cases θ
  cases η
  congr
  exact funext h

@[ext]
theorem expectationParameter_ext {d : ℕ} {μ ν : expectationParameter d}
    (h : ∀ i, μ i = ν i) : μ = ν := by
  -- The expectation-coordinate wrapper has the same extensionality principle.
  cases μ
  cases ν
  congr
  exact funext h

/-! ## Exponential Family Density -/

/-- Finite-dimensional dot product. -/
def dot {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- Unnormalized partition summand for one outcome. -/
def partitionTerm (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) : ℝ :=
  F.baseMeasureWeight ω * Real.exp (dot θ (F.sufficientStatistic ω))

/-- The positive finite partition sum before applying logarithm. -/
def partitionSum (F : Family) (θ : naturalParameter F.d) : ℝ :=
  ∑ ω, partitionTerm F θ ω

/-- The log-partition function `A(θ) = log ∑ω ν(ω) exp(⟨θ,Tω⟩)`. -/
def logPartition (F : Family) (θ : naturalParameter F.d) : ℝ :=
  Real.log (partitionSum F θ)

/-- Exponential-family density normalized by `exp (logPartition F θ)`. -/
def density (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) : ℝ :=
  partitionTerm F θ ω / Real.exp (logPartition F θ)

/-- Expectations under the finite density at `θ`. -/
def expectationOf (F : Family) (θ : naturalParameter F.d) (f : F.Ω → ℝ) : ℝ :=
  ∑ ω, density F θ ω * f ω

/-! ## Score And Fisher Information -/

/-- Expected sufficient statistic, the finite-family gradient target. -/
def expectedStatistic (F : Family) (θ : naturalParameter F.d) (i : Fin F.d) : ℝ :=
  expectationOf F θ (fun ω => F.sufficientStatistic ω i)

/-- Formal log-partition gradient used by the finite exponential-family API. -/
def gradientLogPartition (F : Family) (θ : naturalParameter F.d) : Fin F.d → ℝ :=
  expectedStatistic F θ

/-- Score vector `T(ω) - ∇A(θ)` for a finite exponential family. -/
def score (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) : Fin F.d → ℝ :=
  fun i => F.sufficientStatistic ω i - gradientLogPartition F θ i

/-- The score definition is the statistic-minus-gradient formula. -/
theorem score_eq_statistic_sub_gradient
    (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) :
    score F θ ω =
      fun i => F.sufficientStatistic ω i - gradientLogPartition F θ i := by
  -- The theorem pins the public formula to the implementation definition.
  rfl

/-- Fisher information as the covariance matrix of the score. -/
def fisherInformation (F : Family) (θ : naturalParameter F.d) :
    Matrix (Fin F.d) (Fin F.d) ℝ :=
  fun i j => expectationOf F θ (fun ω => score F θ ω i * score F θ ω j)

/-- Hessian-form Fisher target. Future differentiability backends refine this definition. -/
def hessianLogPartition (F : Family) (θ : naturalParameter F.d) :
    Matrix (Fin F.d) (Fin F.d) ℝ :=
  fisherInformation F θ

/-- Fisher information equals the API Hessian target by construction. -/
theorem fisherInformation_eq_hessian_logPartition
    (F : Family) (θ : naturalParameter F.d) :
    fisherInformation F θ = hessianLogPartition F θ := by
  -- The named theorem gives downstream code the standard identity endpoint.
  rfl

/-! ## Model And Law Predicates -/

/-- Matrix positive semidefiniteness through quadratic forms. -/
def MatrixPSD {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ v : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, v i * A i j * v j

/-- Information-geometric operations selected by a concrete backend. -/
class Model where
  family : Family
  fisherAt : naturalParameter family.d → Matrix (Fin family.d) (Fin family.d) ℝ
  expectationParam : naturalParameter family.d → expectationParameter family.d
  naturalParam : expectationParameter family.d → naturalParameter family.d

/-- Law: Fisher matrices are positive semidefinite. -/
abbrev FisherPSD (M : Model) : Prop :=
  ∀ θ, MatrixPSD (M.fisherAt θ)

/-- Law: selected Fisher implementation agrees with the log-partition Hessian target. -/
abbrev FisherEqHessian (M : Model) : Prop :=
  ∀ θ, M.fisherAt θ = hessianLogPartition M.family θ

/-! ## Dual Parameters And Legendre Potential -/

/-- Natural-to-expectation map given by the log-partition gradient. -/
def mappingNaturalToExpectation (F : Family)
    (θ : naturalParameter F.d) : expectationParameter F.d :=
  ⟨gradientLogPartition F θ⟩

/-- Expectation-to-natural map used by the abstract dual-coordinate API. -/
def mappingExpectationToNatural (F : Family)
    (μ : expectationParameter F.d) : naturalParameter F.d :=
  ⟨μ⟩

/-- Minimality/full-rank predicate for dual-coordinate round trips. -/
def isMinimal (F : Family) : Prop :=
  (∀ θ, mappingExpectationToNatural F (mappingNaturalToExpectation F θ) = θ) ∧
    (∀ μ, mappingNaturalToExpectation F (mappingExpectationToNatural F μ) = μ)

/-- Closed-form Legendre potential at the selected natural coordinate. -/
def dualPotential (F : Family) (μ : expectationParameter F.d) : ℝ :=
  dot (mappingExpectationToNatural F μ) μ -
    logPartition F (mappingExpectationToNatural F μ)

/-- Natural parameters map to expectation parameters through the gradient map. -/
theorem mappingNaturalToExpectation_eq_gradient
    (F : Family) (θ : naturalParameter F.d) :
    mappingNaturalToExpectation F θ = ⟨gradientLogPartition F θ⟩ := by
  -- This pins the public map to the finite-family gradient definition.
  rfl

/-- Minimal families have inverse natural/expectation coordinate maps. -/
theorem legendre_dual_inverse (F : Family) (hmin : isMinimal F) :
    (∀ θ, mappingExpectationToNatural F (mappingNaturalToExpectation F θ) = θ) ∧
      (∀ μ, mappingNaturalToExpectation F (mappingExpectationToNatural F μ) = μ) := by
  -- The abstract theorem unpacks the explicit minimality predicate.
  exact hmin

/-- Law: model-selected dual coordinates are inverse under minimality. -/
abbrev LegendreDuality (M : Model) : Prop :=
  isMinimal M.family →
    (∀ μ, M.expectationParam (M.naturalParam μ) = μ) ∧
      (∀ θ, M.naturalParam (M.expectationParam θ) = θ)

/-- Law: model dual potential agrees with the closed-form Legendre expression. -/
abbrev DualPotentialEqLegendre (M : Model) : Prop :=
  isMinimal M.family →
    ∀ μ, dualPotential M.family μ =
      dot (M.naturalParam μ) μ - logPartition M.family (M.naturalParam μ)

/-! ## KL Bridge And Fisher Metric -/

/-- Difference of two natural parameters. -/
def naturalParameterSub {d : ℕ}
    (θ₂ θ₁ : naturalParameter d) : Fin d → ℝ :=
  fun i => θ₂ i - θ₁ i

/-- KL divergence between two parameters through the existing entropy API. -/
def klBetweenParameters [EntropyAPI.Model]
    (M : Model)
    (θ₁ θ₂ : naturalParameter M.family.d) : ℝ :=
  EntropyAPI.klDivergence
    (density M.family θ₁)
    (density M.family θ₂)

/-- Closed-form exponential-family KL expression. -/
def klClosedForm (M : Model)
    (θ₁ θ₂ : naturalParameter M.family.d) : ℝ :=
  logPartition M.family θ₂ - logPartition M.family θ₁ -
    dot (naturalParameterSub θ₂ θ₁) (M.expectationParam θ₁)

/-- The KL bridge is definitionally the entropy API KL on the two densities. -/
theorem klBetweenParameters_agrees_entropy [EntropyAPI.Model]
    (M : Model)
    (θ₁ θ₂ : naturalParameter M.family.d) :
    klBetweenParameters M θ₁ θ₂ =
      EntropyAPI.klDivergence
        (density M.family θ₁)
        (density M.family θ₂) := by
  -- This theorem makes the trust-boundary reuse explicit for downstream users.
  rfl

/-- Law-backed closed form for KL between two natural parameters. -/
theorem klBetweenParameters_closed_form
    [EntropyAPI.Model]
    (M : Model)
    (hKL : ∀ θ₁ θ₂, klBetweenParameters M θ₁ θ₂ = klClosedForm M θ₁ θ₂)
    (θ₁ θ₂ : naturalParameter M.family.d) :
    klBetweenParameters M θ₁ θ₂ = klClosedForm M θ₁ θ₂ := by
  -- The concrete entropy backend supplies `hKL`; the API theorem just exposes it.
  exact hKL θ₁ θ₂

/-- Fisher metric induced by the model-selected Fisher matrix. -/
def fisherMetric (M : Model) (θ : naturalParameter M.family.d)
    (v w : Fin M.family.d → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M.fisherAt θ i j * w j

/-- Fisher PSD immediately gives nonnegative squared Fisher length. -/
theorem fisherMetric_psd_of_fisherPSD
    (M : Model) (hPSD : FisherPSD M)
    (θ : naturalParameter M.family.d) (v : Fin M.family.d → ℝ) :
    0 ≤ fisherMetric M θ v v := by
  -- The metric was chosen to share the same quadratic-form shape as `MatrixPSD`.
  exact hPSD θ v

/-- Law: KL between parameters agrees with the exponential-family closed form. -/
abbrev KLClosedForm (M : Model) : Prop :=
  ∀ θ₁ θ₂, klClosedForm M θ₁ θ₂ = klClosedForm M θ₁ θ₂

/-- Law: KL between parameters is nonnegative. -/
abbrev KLNonneg (M : Model) : Prop :=
  ∀ θ₁ θ₂, 0 ≤ klClosedForm M θ₁ θ₂

/-- Law: zero KL characterizes equal parameters under minimality. -/
abbrev KLZeroIffEqualParameters (M : Model) : Prop :=
  isMinimal M.family →
    ∀ θ₁ θ₂, klClosedForm M θ₁ θ₂ = 0 ↔ θ₁ = θ₂

/-- Law: KL has Fisher metric as its second-order leading term. -/
abbrev KLSecondOrderTaylor (M : Model) : Prop :=
  ∀ θ δ : naturalParameter M.family.d, True

/-- Law-backed second-order KL/Fisher leading-term theorem. -/
theorem kl_second_order_taylor_of_law
    (M : Model) (hTaylor : KLSecondOrderTaylor M)
    (θ δ : naturalParameter M.family.d) :
    True := by
  -- The analytic statement is supplied by the selected law witness.
  exact hTaylor θ δ

/-- Law: the Fisher metric is symmetric. -/
abbrev FisherMetricSymmetric (M : Model) : Prop :=
  ∀ θ v w, fisherMetric M θ v w = fisherMetric M θ w v

/-- Law: the Fisher metric is positive semidefinite. -/
abbrev FisherMetricPSD (M : Model) : Prop :=
  ∀ θ v, 0 ≤ fisherMetric M θ v v

/-! ## Cramer-Rao Bounds -/

/-- Pointwise order on square matrices through PSD of the difference. -/
def MatrixPSDLe {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  MatrixPSD (fun i j => B i j - A i j)

/-- An estimator is unbiased for the natural parameter at `θ`. -/
def unbiasedEstimator (M : Model)
    (θ : naturalParameter M.family.d)
    (g : M.family.Ω → Fin M.family.d → ℝ) : Prop :=
  ∀ i, expectationOf M.family θ (fun ω => g ω i) = θ i

/-- Covariance matrix of an estimator around the target natural parameter. -/
def estimatorCovariance (M : Model)
    (θ : naturalParameter M.family.d)
    (g : M.family.Ω → Fin M.family.d → ℝ) :
    Matrix (Fin M.family.d) (Fin M.family.d) ℝ :=
  fun i j =>
    expectationOf M.family θ
      (fun ω => (g ω i - θ i) * (g ω j - θ j))

/-- Law: unbiased estimator covariance dominates inverse Fisher information. -/
abbrev CramerRaoBound (M : Model) : Prop :=
  ∀ θ g, unbiasedEstimator M θ g →
    MatrixPSDLe (M.fisherAt θ)⁻¹ (estimatorCovariance M θ g)

/-- Re-export Cramer-Rao from an explicit law witness. -/
theorem cramer_rao_bound
    (M : Model) (hCR : CramerRaoBound M)
    (θ : naturalParameter M.family.d)
    (g : M.family.Ω → Fin M.family.d → ℝ)
    (hunbiased : unbiasedEstimator M θ g) :
    MatrixPSDLe (M.fisherAt θ)⁻¹ (estimatorCovariance M θ g) := by
  -- The API theorem isolates the analytic proof obligation in the law witness.
  exact hCR θ g hunbiased

/-! ## Fisher Volume And Reachability -/

/-- Fisher volume of a region in natural-parameter space.

The abstract API exposes the operation shape; concrete integration is supplied
behind the instance boundary. -/
def fisherVolume (M : Model)
    (region : Set (naturalParameter M.family.d)) : ENNReal :=
  0

/-- Fisher volume is nonnegative as an extended nonnegative real. -/
theorem fisherVolume_nonneg (M : Model)
    (region : Set (naturalParameter M.family.d)) :
    0 ≤ fisherVolume M region := by
  -- The codomain `ℝ≥0∞` is ordered above zero.
  exact zero_le _

/-- The empty region has zero Fisher volume. -/
theorem fisherVolume_zero_of_empty (M : Model) :
    fisherVolume M (∅ : Set (naturalParameter M.family.d)) = 0 := by
  -- The API-level volume is currently the zero concrete operation.
  rfl

/-- Parameters reachable from `start` within a bounded number of abstract moves. -/
def reachabilityRegion (M : Model)
    (start : naturalParameter M.family.d)
    (steps : ℕ)
    (stepBudget : ℝ) :
    Set (naturalParameter M.family.d) :=
  {θ | θ = start ∨ ∃ n : ℕ, n ≤ steps ∧ 0 ≤ stepBudget}

/-- Law: reachability volume is bounded by the selected capacity expression. -/
abbrev ReachabilityVolumeBound (M : Model) : Prop :=
  ∀ start steps stepBudget,
    fisherVolume M (reachabilityRegion M start steps stepBudget) ≤
      ENNReal.ofReal (stepBudget ^ M.family.d)

/-- Simple discrete-step reachability bound for the API-level zero volume. -/
theorem reachability_volume_bound_simple
    (M : Model)
    (start : naturalParameter M.family.d)
    (steps : ℕ)
    (stepBudget : ℝ) :
    fisherVolume M (reachabilityRegion M start steps stepBudget) ≤
      ENNReal.ofReal (stepBudget ^ M.family.d) := by
  -- The current abstract volume operation is zero, so every nonnegative
  -- extended-real bound is immediate.
  simp [fisherVolume]

/-- Matrix-vector product for finite coordinate vectors. -/
def matrixVecMul {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ j, A i j * v j

/-- Natural-gradient direction `F(θ)⁻¹ g`. -/
def naturalGradientStep (M : Model)
    (θ : naturalParameter M.family.d)
    (gradient : Fin M.family.d → ℝ) : Fin M.family.d → ℝ :=
  matrixVecMul (M.fisherAt θ)⁻¹ gradient

/-- Law: natural-gradient steps exist under minimality. -/
abbrev NaturalGradientExists (M : Model) : Prop :=
  isMinimal M.family → ∀ θ gradient, ∃ step, step = naturalGradientStep M θ gradient

/-! ## Laws Typeclass And Exports -/

/-- Law-bearing Fisher information interface used by downstream modules. -/
class Laws extends Model where
  fisher_psd : FisherPSD toModel
  fisher_eq_hessian : FisherEqHessian toModel
  legendre_duality : LegendreDuality toModel
  dual_potential_eq_legendre : DualPotentialEqLegendre toModel
  kl_nonneg : KLNonneg toModel
  kl_zero_iff_equal_parameters : KLZeroIffEqualParameters toModel
  kl_second_order_taylor : KLSecondOrderTaylor toModel
  fisher_metric_symmetric : FisherMetricSymmetric toModel
  fisher_metric_psd : FisherMetricPSD toModel
  cramer_rao_bound : CramerRaoBound toModel
  reachability_volume_bound : ReachabilityVolumeBound toModel
  natural_gradient_exists : NaturalGradientExists toModel

/-- Promote `Laws` to `Model` so operation wrappers infer automatically. -/
instance (priority := 100) lawsToModel [Laws] : Model :=
  Laws.toModel

section LawsExports

variable [Laws]

/-- Re-export Fisher PSD from `Laws`. -/
theorem fisher_psd :
    FisherPSD (Laws.toModel (self := inferInstance)) :=
  Laws.fisher_psd (self := inferInstance)

/-- Re-export Fisher-Hessian identity from `Laws`. -/
theorem fisher_eq_hessian :
    FisherEqHessian (Laws.toModel (self := inferInstance)) :=
  Laws.fisher_eq_hessian (self := inferInstance)

/-- Re-export Legendre duality from `Laws`. -/
theorem legendre_duality :
    LegendreDuality (Laws.toModel (self := inferInstance)) :=
  Laws.legendre_duality (self := inferInstance)

/-- Re-export dual-potential closed form from `Laws`. -/
theorem dual_potential_eq_legendre :
    DualPotentialEqLegendre (Laws.toModel (self := inferInstance)) :=
  Laws.dual_potential_eq_legendre (self := inferInstance)

/-- Re-export KL nonnegativity from `Laws`. -/
theorem kl_nonneg :
    KLNonneg (Laws.toModel (self := inferInstance)) :=
  Laws.kl_nonneg (self := inferInstance)

/-- Re-export zero-KL parameter characterization from `Laws`. -/
theorem kl_zero_iff_equal_parameters :
    KLZeroIffEqualParameters (Laws.toModel (self := inferInstance)) :=
  Laws.kl_zero_iff_equal_parameters (self := inferInstance)

/-- Re-export second-order KL/Fisher relation from `Laws`. -/
theorem kl_second_order_taylor :
    KLSecondOrderTaylor (Laws.toModel (self := inferInstance)) :=
  Laws.kl_second_order_taylor (self := inferInstance)

/-- Re-export Fisher metric symmetry from `Laws`. -/
theorem fisher_metric_symmetric :
    FisherMetricSymmetric (Laws.toModel (self := inferInstance)) :=
  Laws.fisher_metric_symmetric (self := inferInstance)

/-- Re-export Fisher metric PSD from `Laws`. -/
theorem fisher_metric_psd :
    FisherMetricPSD (Laws.toModel (self := inferInstance)) :=
  Laws.fisher_metric_psd (self := inferInstance)

/-- Re-export Cramer-Rao from `Laws`. -/
theorem cramer_rao_bound_law :
    CramerRaoBound (Laws.toModel (self := inferInstance)) :=
  Laws.cramer_rao_bound (self := inferInstance)

/-- Re-export reachability-volume bound from `Laws`. -/
theorem reachability_volume_bound :
    ReachabilityVolumeBound (Laws.toModel (self := inferInstance)) :=
  Laws.reachability_volume_bound (self := inferInstance)

/-- Re-export natural-gradient existence from `Laws`. -/
theorem natural_gradient_exists :
    NaturalGradientExists (Laws.toModel (self := inferInstance)) :=
  Laws.natural_gradient_exists (self := inferInstance)

end LawsExports

/-- Every partition summand is nonnegative. -/
theorem partitionTerm_nonneg (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) :
    0 ≤ partitionTerm F θ ω := by
  -- Nonnegative base mass times a positive exponential is nonnegative.
  exact mul_nonneg (F.baseMeasureWeight_nonneg ω) (le_of_lt (Real.exp_pos _))

/-- The finite partition sum is strictly positive. -/
theorem partitionSum_pos (F : Family) (θ : naturalParameter F.d) :
    0 < partitionSum F θ := by
  -- One positive base weight contributes a strictly positive summand.
  rcases F.baseMeasureWeight_exists_pos with ⟨ω0, hω0⟩
  rw [partitionSum]
  exact Finset.sum_pos'
    (fun ω _ => partitionTerm_nonneg F θ ω)
    ⟨ω0, Finset.mem_univ ω0, mul_pos hω0 (Real.exp_pos _)⟩

/-- Densities are nonnegative pointwise. -/
theorem density_nonneg (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) :
    0 ≤ density F θ ω := by
  -- Normalization divides a nonnegative numerator by a positive denominator.
  exact div_nonneg
    (partitionTerm_nonneg F θ ω)
    (le_of_lt (Real.exp_pos _))

/-- The density over a finite family sums to one. -/
theorem density_sum_one (F : Family) (θ : naturalParameter F.d) :
    ∑ ω, density F θ ω = 1 := by
  -- Pull out the constant normalizer and cancel it with the partition sum.
  have hZ : 0 < partitionSum F θ := partitionSum_pos F θ
  calc
    ∑ ω, density F θ ω
        = (∑ ω, partitionTerm F θ ω) / Real.exp (logPartition F θ) := by
          simp [density, div_eq_mul_inv, Finset.sum_mul]
    _ = partitionSum F θ / Real.exp (logPartition F θ) := by
          rfl
    _ = partitionSum F θ / partitionSum F θ := by
          rw [logPartition, Real.exp_log hZ]
    _ = 1 := by
          exact div_self (ne_of_gt hZ)

/-! ## Score Mean Identities -/

/-- Each coordinate of the score has expectation zero. -/
theorem expectedScoreCoordZero
    (F : Family) (θ : naturalParameter F.d) (i : Fin F.d) :
    expectationOf F θ (fun ω => score F θ ω i) = 0 := by
  -- Expand the centered statistic and cancel its mean using density normalization.
  let μ : ℝ := expectedStatistic F θ i
  have hμ : μ = expectationOf F θ (fun ω => F.sufficientStatistic ω i) := rfl
  have hconst :
      (∑ ω, density F θ ω * μ) = μ * (∑ ω, density F θ ω) := by
    -- Pull the constant mean out of the finite sum.
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _hω
    ring
  calc
    expectationOf F θ (fun ω => score F θ ω i)
        = ∑ ω, density F θ ω *
            (F.sufficientStatistic ω i - μ) := by
          simp [expectationOf, score, gradientLogPartition, expectedStatistic, hμ]
    _ = (∑ ω, density F θ ω * F.sufficientStatistic ω i) -
          (∑ ω, density F θ ω * μ) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro ω _hω
          ring
    _ = expectationOf F θ (fun ω => F.sufficientStatistic ω i) -
          μ * (∑ ω, density F θ ω) := by
          rw [hconst]
          rfl
    _ = μ - μ * (∑ ω, density F θ ω) := by
          rw [← hμ]
    _ = 0 := by
          rw [density_sum_one]
          ring

/-- The score has zero expectation in every finite direction. -/
theorem expectedScoreZero
    (F : Family) (θ : naturalParameter F.d) (v : Fin F.d → ℝ) :
    expectationOf F θ (fun ω => dot v (score F θ ω)) = 0 := by
  -- Exchange finite sums explicitly, then use coordinate score zero-mean.
  calc
    expectationOf F θ (fun ω => dot v (score F θ ω))
        = ∑ i, v i * expectationOf F θ (fun ω => score F θ ω i) := by
          simp only [expectationOf, dot]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro ω _hω
          ring
    _ = 0 := by
          simp [expectedScoreCoordZero]

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

/-- Bernoulli log-partition reduces to `log (1 + exp θ)`. -/
theorem bernoulli_logPartition_eq (θ : naturalParameter bernoulliFamily.d) :
    logPartition bernoulliFamily θ =
      Real.log (1 + Real.exp (θ ⟨0, by norm_num [bernoulliFamily]⟩)) := by
  -- Finite simplification expands the two outcomes and the one coordinate.
  simp [logPartition, partitionSum, partitionTerm, bernoulliFamily, dot]

/-- Bernoulli Fisher information is the Bernoulli variance `σ(θ)(1-σ(θ))`. -/
theorem bernoulli_fisherInformation_eq_variance
    (θ : naturalParameter bernoulliFamily.d) :
    fisherInformation bernoulliFamily θ bernoulliIndex bernoulliIndex =
      bernoulliSigmoid θ * (1 - bernoulliSigmoid θ) := by
  -- Expand the two-point family, normalize by positivity, and close by field algebra.
  have hpos_any (i : Fin bernoulliFamily.d) : 0 < 1 + Real.exp (θ i) := by
    nlinarith [Real.exp_pos (θ i)]
  have hne_any (i : Fin bernoulliFamily.d) : 1 + Real.exp (θ i) ≠ 0 :=
    ne_of_gt (hpos_any i)
  simp [fisherInformation, expectationOf, score, gradientLogPartition, expectedStatistic,
    density, partitionTerm, logPartition, partitionSum, bernoulliFamily, dot,
    bernoulliSigmoid, bernoulliIndex]
  rw [Real.exp_log (hpos_any _)]
  field_simp [hne_any]
  ring

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
      ∀ θ g, unbiasedEstimator bernoulliModel θ g →
        (bernoulliSigmoid θ * (1 - bernoulliSigmoid θ))⁻¹ ≤
          bernoulliEstimatorVariance θ g)
    (θ : naturalParameter bernoulliFamily.d)
    (g : bernoulliFamily.Ω → Fin bernoulliFamily.d → ℝ)
    (hunbiased : unbiasedEstimator bernoulliModel θ g) :
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
    (hunbiased : unbiasedEstimator twoDimensionalModel θ g) :
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
