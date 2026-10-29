import FisherInformationInstance.BernoulliDuality

/-! # Bernoulli Fisher Laws Instance

A nondegenerate (`d = 1`) checked `Laws` instance for the Bernoulli family
`Fixtures.bernoulliModel`, whose Fisher matrix is the real Fisher information
`σ(θ)(1 - σ(θ)) > 0`.

## Scope

Every law is proved with full content. Minimality (affine independence of the
statistic `0, 1`), Legendre duality, dual potential = negative entropy, the KL
Bregman closed form, KL-zero-iff-equal, natural-gradient existence, and the
Fisher/Hessian identity are proved in `BernoulliDuality`.
-/

/-
The Problem. The canonical finite-discrete instance used a zero-dimensional
family on which every law is trivial.

Solution Structure.
1. Reduce each model-level quantity to scalar softplus/logistic forms.
2. Prove each law from the scalar calculus in `BernoulliCalculus`.
3. Package the laws instance.
-/

set_option autoImplicit false

namespace FisherInformationAPI

namespace Fixtures

open scoped BigOperators
open Asymptotics

noncomputable section

/-! ## Model-Level Reductions -/

/-- The Bernoulli Fisher metric is `v · σ(1-σ) · w`. -/
theorem fisherMetric_eq (θ : naturalParameter bernoulliFamily.d)
    (v w : Fin bernoulliFamily.d → ℝ) :
    fisherMetric bernoulliModel θ v w =
      v bernoulliIndex * logisticVar (θ bernoulliIndex) * w bernoulliIndex := by
  -- Collapse both one-term sums.
  show ∑ i : Fin bernoulliFamily.d, ∑ j : Fin bernoulliFamily.d,
    v i * fisherInformation bernoulliFamily θ i j * w j = _
  rw [sum_index]
  rw [sum_index, fisherInformation_eq]

/-- The Bernoulli Fisher determinant is the scalar Fisher information. -/
theorem fisherAt_det (θ : naturalParameter bernoulliFamily.d) :
    (bernoulliModel.fisherAt θ).det = logisticVar (θ bernoulliIndex) := by
  -- `1 × 1` determinants are the single entry.
  have h : ∀ A : Matrix (Fin 1) (Fin 1) ℝ, A.det = A 0 0 := fun A => Matrix.det_fin_one A
  exact (h (bernoulliModel.fisherAt θ)).trans (fisherInformation_eq θ _ _)

/-! ## Law Proofs -/

/-- Bernoulli Fisher matrices are positive semidefinite. -/
theorem bernoulli_fisherPSD : FisherPSD bernoulliModel := by
  -- `v² σ(1-σ) ≥ 0`.
  intro (θ : naturalParameter bernoulliFamily.d) (v : Fin bernoulliFamily.d → ℝ)
  show 0 ≤ fisherMetric bernoulliModel θ v v
  rw [fisherMetric_eq θ v v, mul_right_comm]
  exact mul_nonneg (mul_self_nonneg _) (logisticVar_pos _).le

/-- Bernoulli closed-form KL is nonnegative. -/
theorem bernoulli_klNonneg : KLNonneg bernoulliModel := by
  -- Convexity gap of softplus.
  intro (θ₁ : naturalParameter bernoulliFamily.d) (θ₂ : naturalParameter bernoulliFamily.d)
  rw [klClosedForm_eq θ₁ θ₂]
  have h := softplus_bregman_nonneg (θ₁ bernoulliIndex)
    (θ₂ bernoulliIndex - θ₁ bernoulliIndex)
  rw [add_sub_cancel] at h
  linarith

/-- Bernoulli KL has the Fisher metric as second-order term. -/
theorem bernoulli_klSecondOrderTaylor : KLSecondOrderTaylor bernoulliModel := by
  -- The KL defect is exactly the softplus Taylor remainder.
  intro (θ : naturalParameter bernoulliFamily.d) (δ : Fin bernoulliFamily.d → ℝ)
  refine (softplusRemainder_isLittleO (θ bernoulliIndex) (δ bernoulliIndex)).congr_left
    (fun t => ?_)
  refine Eq.trans ?_ (congrArg₂ (fun x y : ℝ => x - t ^ 2 / 2 * y)
    (klClosedForm_eq θ (perturbParameter θ t δ)) (fisherMetric_eq θ δ δ)).symm
  show _ = softplus (θ bernoulliIndex + t * δ bernoulliIndex) - _ -
    (θ bernoulliIndex + t * δ bernoulliIndex - θ bernoulliIndex) * _ - _
  unfold softplusRemainder
  ring

/-- Bernoulli Fisher metric is symmetric. -/
theorem bernoulli_fisherMetricSymmetric : FisherMetricSymmetric bernoulliModel := by
  -- Scalar commutativity.
  intro (θ : naturalParameter bernoulliFamily.d) (v : Fin bernoulliFamily.d → ℝ)
    (w : Fin bernoulliFamily.d → ℝ)
  rw [fisherMetric_eq θ v w, fisherMetric_eq θ w v]
  ring

/-- Bernoulli Fisher metric is positive semidefinite. -/
theorem bernoulli_fisherMetricPSD : FisherMetricPSD bernoulliModel := by
  -- Same quadratic form as `FisherPSD`.
  intro θ v
  exact bernoulli_fisherPSD θ v

/-- Bernoulli reachable Fisher volume is bounded with constant `1/2`. -/
theorem bernoulli_reachabilityVolumeBound : ReachabilityVolumeBound bernoulliModel := by
  -- `√(σ(1-σ)) ≤ √(1/4) = 1/2`.
  refine reachabilityVolumeBound_of_sqrt_det_le bernoulliModel (1 / 2) (by norm_num)
    (fun (θ : naturalParameter bernoulliFamily.d) => ?_)
  rw [fisherAt_det θ, show (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) from
    (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by linarith [logisticVar_le_quarter (θ bernoulliIndex)])

/-! ## Cramer-Rao -/

/-- For a locally unbiased Bernoulli estimator the variance equals `1 / I(θ)`
(the Bernoulli family attains the Cramer-Rao bound). -/
theorem bernoulli_cr_gap_zero (θ : naturalParameter bernoulliFamily.d)
    (g : bernoulliFamily.Ω → Fin bernoulliFamily.d → ℝ)
    (hunb : locallyUnbiasedEstimator bernoulliModel θ g) :
    estimatorCovariance bernoulliModel θ g bernoulliIndex bernoulliIndex -
      (bernoulliModel.fisherAt θ)⁻¹ bernoulliIndex bernoulliIndex = 0 := by
  -- With `q = σ(1-σ)` and `D = g₁ - g₀`: `qD = 1` and variance `qD² = D = q⁻¹`.
  have hmean : expectationOf bernoulliFamily θ (fun ω => g ω bernoulliIndex) =
      θ bernoulliIndex := hunb.1 bernoulliIndex
  have hscore : expectationOf bernoulliFamily θ
      (fun ω => g ω bernoulliIndex * score bernoulliFamily θ ω bernoulliIndex) = 1 := by
    have h : expectationOf bernoulliFamily θ
        (fun ω => g ω bernoulliIndex * score bernoulliFamily θ ω bernoulliIndex) =
          if bernoulliIndex = bernoulliIndex then (1 : ℝ) else 0 :=
      hunb.2 bernoulliIndex bernoulliIndex
    rw [if_pos rfl] at h
    exact h
  rw [expectation_eq θ] at hmean
  rw [expectation_eq θ, score_ω0 θ, score_ω1 θ] at hscore
  have hD : logisticVar (θ bernoulliIndex) * (g ω1 bernoulliIndex - g ω0 bernoulliIndex) = 1 := by
    unfold logisticVar; linear_combination hscore
  have hInv := eq_inv_of_mul_eq_one_right hD
  rw [fisherAt_inv_apply θ, ← hInv]
  show expectationOf bernoulliFamily θ
    (fun ω => (g ω bernoulliIndex - θ bernoulliIndex) *
      (g ω bernoulliIndex - θ bernoulliIndex)) - _ = 0
  rw [expectation_eq θ]
  unfold logisticVar at hD
  linear_combination
    ((1 - logistic (θ bernoulliIndex)) * g ω0 bernoulliIndex +
      logistic (θ bernoulliIndex) * g ω1 bernoulliIndex - θ bernoulliIndex) * hmean +
    (g ω1 bernoulliIndex - g ω0 bernoulliIndex) * hD

/-- Bernoulli Cramer-Rao bound for locally unbiased estimators. -/
theorem bernoulli_cramerRaoBound : CramerRaoBound bernoulliModel := by
  -- The PSD gap is the zero `1 × 1` matrix.
  intro θ g hunb v
  show 0 ≤ ∑ i : Fin bernoulliFamily.d, ∑ j : Fin bernoulliFamily.d,
    v i * (estimatorCovariance bernoulliModel θ g i j -
      (bernoulliModel.fisherAt θ)⁻¹ i j) * v j
  rw [sum_index]
  rw [sum_index, bernoulli_cr_gap_zero θ g hunb]
  simp

end

end Fixtures

/-! ## Laws Instance -/

namespace RealConcrete

open Fixtures

/-- Nondegenerate checked Fisher laws for the Bernoulli family (`d = 1`). -/
noncomputable instance bernoulliLaws : Laws where
  toModel := bernoulliModel
  fisher_psd := bernoulli_fisherPSD
  fisher_eq_hessian := bernoulli_fisherEqHessian
  legendre_duality := bernoulli_legendreDuality
  dual_potential_eq_legendre := bernoulli_dualPotentialEqLegendre
  kl_closed_form := bernoulli_klClosedForm
  kl_nonneg := bernoulli_klNonneg
  kl_zero_iff_equal_parameters := bernoulli_klZeroIffEqualParameters
  kl_second_order_taylor := bernoulli_klSecondOrderTaylor
  fisher_metric_symmetric := bernoulli_fisherMetricSymmetric
  fisher_metric_psd := bernoulli_fisherMetricPSD
  cramer_rao_bound := bernoulli_cramerRaoBound
  reachability_volume_bound := bernoulli_reachabilityVolumeBound
  natural_gradient_exists := bernoulli_naturalGradientExists

end RealConcrete

end FisherInformationAPI
