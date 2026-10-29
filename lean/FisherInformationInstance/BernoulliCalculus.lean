import FisherInformationAPI

/-! # Bernoulli Fisher Calculus

Explicit computations for the one-dimensional Bernoulli exponential family
`Fixtures.bernoulliFamily` (outcomes `Fin 2`, statistic `0, 1`, unit base
weights): softplus log-partition, logistic mean, density, score, and Fisher
information, together with the scalar calculus (derivatives, convexity gap,
second-order Taylor remainder) used by the Bernoulli laws instance.
-/

/-
The Problem. The Fisher API laws need a nondegenerate checked instance, which
requires concrete closed forms for the Bernoulli family and real analysis on
`log (1 + exp x)`.

Solution Structure.
1. Scalar softplus/logistic calculus.
2. Reduce finite sums over the Bernoulli outcome and index types.
3. Close-form density, expectation, score, Fisher information, and KL.
-/

set_option autoImplicit false

namespace FisherInformationAPI

namespace Fixtures

open scoped BigOperators
open Asymptotics

noncomputable section

/-! ## Scalar Softplus And Logistic -/

/-- Scalar softplus `A(x) = log (1 + exp x)`, the Bernoulli log-partition. -/
def softplus (x : ℝ) : ℝ :=
  Real.log (1 + Real.exp x)

/-- Scalar logistic `σ(x) = exp x / (1 + exp x)`, the Bernoulli mean. -/
def logistic (x : ℝ) : ℝ :=
  Real.exp x / (1 + Real.exp x)

/-- Bernoulli variance `σ(x)(1 - σ(x))`, the scalar Fisher information. -/
def logisticVar (x : ℝ) : ℝ :=
  logistic x * (1 - logistic x)

/-- The softplus argument is strictly positive. -/
theorem one_add_exp_pos (x : ℝ) : 0 < 1 + Real.exp x := by
  -- `exp` is positive.
  positivity

/-- The logistic is strictly positive. -/
theorem logistic_pos (x : ℝ) : 0 < logistic x := by
  -- Quotient of positive reals.
  exact div_pos (Real.exp_pos x) (one_add_exp_pos x)

/-- The logistic is strictly below one. -/
theorem logistic_lt_one (x : ℝ) : logistic x < 1 := by
  -- `exp x < 1 + exp x`.
  rw [logistic, div_lt_one (one_add_exp_pos x)]
  linarith

/-- The Bernoulli variance is strictly positive. -/
theorem logisticVar_pos (x : ℝ) : 0 < logisticVar x := by
  -- Both factors lie in `(0, 1)`.
  exact mul_pos (logistic_pos x) (by linarith [logistic_lt_one x])

/-- The Bernoulli variance is at most `1/4`. -/
theorem logisticVar_le_quarter (x : ℝ) : logisticVar x ≤ 1 / 4 := by
  -- `p(1-p) ≤ 1/4` is `(p - 1/2)^2 ≥ 0`.
  unfold logisticVar
  nlinarith [sq_nonneg (logistic x - 1 / 2)]

/-- Softplus has derivative logistic. -/
theorem hasDerivAt_softplus (x : ℝ) : HasDerivAt softplus (logistic x) x := by
  -- Chain rule for `log ∘ (1 + exp)`.
  exact ((Real.hasDerivAt_exp x).const_add 1).log (one_add_exp_pos x).ne'

/-- Logistic has derivative `σ(1 - σ)`. -/
theorem hasDerivAt_logistic (x : ℝ) :
    HasDerivAt logistic (logisticVar x) x := by
  -- Quotient rule, then clear the positive denominator.
  have hne : 1 + Real.exp x ≠ 0 := (one_add_exp_pos x).ne'
  have h := (Real.hasDerivAt_exp x).div ((Real.hasDerivAt_exp x).const_add 1) hne
  refine h.congr_deriv ?_
  unfold logisticVar logistic
  field_simp

/-- Affine reparametrization `s ↦ a + s * b` has derivative `b`. -/
theorem hasDerivAt_affine (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => a + s * b) b t := by
  -- Linear map plus a constant.
  exact (hasDerivAt_mul_const b).const_add a

/-! ## Softplus Convexity Gap -/

/-- The softplus ratio `(1 + e^{x+u}) / (1 + e^x)` is a logistic mixture. -/
theorem softplus_ratio (x u : ℝ) :
    (1 - logistic x) * 1 + logistic x * Real.exp u =
      (1 + Real.exp (x + u)) / (1 + Real.exp x) := by
  -- Clear the common denominator.
  have hne : 1 + Real.exp x ≠ 0 := (one_add_exp_pos x).ne'
  unfold logistic
  rw [Real.exp_add]
  field_simp
  ring

/-- Bregman gap of softplus is nonnegative (convexity of the log-partition). -/
theorem softplus_bregman_nonneg (x u : ℝ) :
    u * logistic x ≤ softplus (x + u) - softplus x := by
  -- Concavity of `log` on the mixture `(1-p)·1 + p·e^u`.
  have hp0 : 0 ≤ logistic x := (logistic_pos x).le
  have hp1 : 0 ≤ 1 - logistic x := by linarith [logistic_lt_one x]
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 one_pos)
    (Set.mem_Ioi.2 (Real.exp_pos u)) hp1 hp0 (by ring)
  simp only [smul_eq_mul] at hc
  rw [softplus_ratio, Real.log_one, Real.log_exp,
    Real.log_div (one_add_exp_pos _).ne' (one_add_exp_pos x).ne'] at hc
  unfold softplus
  linarith

/-! ## Second-Order Softplus Remainder -/

/-- Remainder of the second-order Taylor expansion of softplus along `a + t b`. -/
def softplusRemainder (a b t : ℝ) : ℝ :=
  softplus (a + t * b) - softplus a - t * (b * logistic a) -
    t ^ 2 / 2 * (b ^ 2 * logisticVar a)

/-- Derivative in `t` of `softplusRemainder a b`. -/
def softplusRemainderDeriv (a b t : ℝ) : ℝ :=
  b * logistic (a + t * b) - b * logistic a - t * (b ^ 2 * logisticVar a)

/-- The quadratic Taylor term has the expected derivative. -/
theorem hasDerivAt_half_sq_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 2 / 2 * c) (t * c) t := by
  -- Power rule, then normalize constants.
  have h := ((hasDerivAt_pow 2 t).div_const 2).mul_const c
  convert h using 1
  push_cast
  ring

/-- `softplusRemainder a b` has derivative `softplusRemainderDeriv a b`. -/
theorem hasDerivAt_softplusRemainder (a b t : ℝ) :
    HasDerivAt (softplusRemainder a b) (softplusRemainderDeriv a b t) t := by
  -- Combine the chain rule with the linear and quadratic correction terms.
  have h1 := (hasDerivAt_softplus (a + t * b)).comp t (hasDerivAt_affine a b t)
  have h := ((h1.sub_const (softplus a)).sub
    (hasDerivAt_mul_const (b * logistic a))).sub
      (hasDerivAt_half_sq_mul (b ^ 2 * logisticVar a) t)
  refine h.congr_deriv ?_
  unfold softplusRemainderDeriv
  ring

/-- The remainder derivative is `o(t)` at zero (logistic is differentiable). -/
theorem softplusRemainderDeriv_isLittleO (a b : ℝ) :
    softplusRemainderDeriv a b =o[nhds 0] (fun t : ℝ => (t - 0) ^ 1) := by
  -- First-order expansion of `s ↦ σ(a + s b)` at zero, scaled by `b`.
  have hk := (hasDerivAt_logistic (a + 0 * b)).comp 0 (hasDerivAt_affine a b 0)
  have ho := (hasDerivAt_iff_isLittleO.1 hk).const_mul_left b
  refine ho.congr (fun t => ?_) (fun t => by ring)
  simp only [softplusRemainderDeriv, Function.comp_apply, smul_eq_mul, zero_mul,
    add_zero, sub_zero]
  ring

/-- The remainder vanishes at `t = 0`. -/
theorem softplusRemainder_zero (a b : ℝ) : softplusRemainder a b 0 = 0 := by
  -- Every term is evaluated at the base point.
  simp [softplusRemainder]

/-- Second-order Taylor theorem for softplus: the remainder is `o(t²)`. -/
theorem softplusRemainder_isLittleO (a b : ℝ) :
    softplusRemainder a b =o[nhds 0] (fun t : ℝ => t ^ 2) := by
  -- Integrate the `o(t)` derivative bound via the mean-value little-o lemma.
  have h := Convex.isLittleO_pow_succ_real (f := softplusRemainder a b)
    (f' := softplusRemainderDeriv a b) (n := 1) convex_univ (Set.mem_univ 0)
    (fun x _ => (hasDerivAt_softplusRemainder a b x).hasDerivWithinAt)
    (by simpa only [nhdsWithin_univ] using softplusRemainderDeriv_isLittleO a b)
  simp only [nhdsWithin_univ, softplusRemainder_zero, sub_zero] at h
  simpa using h

/-! ## Bernoulli Sum Reductions -/

/-- The Bernoulli failure outcome. -/
def ω0 : bernoulliFamily.Ω :=
  (0 : Fin 2)

/-- The Bernoulli success outcome. -/
def ω1 : bernoulliFamily.Ω :=
  (1 : Fin 2)

/-- Sums over Bernoulli outcomes have two terms. -/
theorem sum_omega (f : bernoulliFamily.Ω → ℝ) : ∑ ω, f ω = f ω0 + f ω1 :=
  Fin.sum_univ_two f

/-- Sums over the single Bernoulli coordinate have one term. -/
theorem sum_index (f : Fin bernoulliFamily.d → ℝ) : ∑ i, f i = f bernoulliIndex :=
  Fin.sum_univ_one f

/-- Bernoulli dot products reduce to one product. -/
theorem dot_eq (x y : Fin bernoulliFamily.d → ℝ) :
    dot x y = x bernoulliIndex * y bernoulliIndex :=
  sum_index _

/-- The failure statistic is zero. -/
theorem stat_ω0 (i : Fin bernoulliFamily.d) :
    bernoulliFamily.sufficientStatistic ω0 i = 0 := by
  -- Evaluate the `if` on `Fin 2`.
  show (if (0 : Fin 2) = 0 then (0 : ℝ) else 1) = 0
  simp

/-- The success statistic is one. -/
theorem stat_ω1 (i : Fin bernoulliFamily.d) :
    bernoulliFamily.sufficientStatistic ω1 i = 1 := by
  -- Evaluate the `if` on `Fin 2`.
  show (if (1 : Fin 2) = 0 then (0 : ℝ) else 1) = 1
  simp

/-- Bernoulli base weights are one. -/
theorem weight_eq (ω : bernoulliFamily.Ω) : bernoulliFamily.baseMeasureWeight ω = 1 :=
  rfl

/-! ## Bernoulli Closed Forms -/

/-- The Bernoulli partition sum is `1 + exp θ`. -/
theorem partitionSum_eq (θ : naturalParameter bernoulliFamily.d) :
    partitionSum bernoulliFamily θ = 1 + Real.exp (θ bernoulliIndex) := by
  -- Two outcomes with statistics `0` and `1`.
  unfold partitionSum
  rw [sum_omega]
  simp only [partitionTerm, dot_eq, stat_ω0, stat_ω1, weight_eq, mul_zero, mul_one,
    Real.exp_zero, one_mul]

/-- The Bernoulli log-partition is softplus. -/
theorem logPartition_eq (θ : naturalParameter bernoulliFamily.d) :
    logPartition bernoulliFamily θ = softplus (θ bernoulliIndex) := by
  -- Logarithm of the partition sum.
  unfold logPartition
  rw [partitionSum_eq]
  rfl

/-- Bernoulli log-partition reduces to `log (1 + exp θ)`. -/
theorem bernoulli_logPartition_eq (θ : naturalParameter bernoulliFamily.d) :
    logPartition bernoulliFamily θ =
      Real.log (1 + Real.exp (θ ⟨0, by norm_num [bernoulliFamily]⟩)) := by
  -- Softplus of the single coordinate.
  exact logPartition_eq θ

/-- Normalized partition terms divide by `1 + exp θ`. -/
theorem density_eq_div (θ : naturalParameter bernoulliFamily.d) (ω : bernoulliFamily.Ω) :
    density bernoulliFamily θ ω =
      partitionTerm bernoulliFamily θ ω / (1 + Real.exp (θ bernoulliIndex)) := by
  -- `exp (log Z) = Z` for the positive partition sum.
  unfold density logPartition
  rw [Real.exp_log (partitionSum_pos _ _), partitionSum_eq]

/-- Failure probability is `1 - σ(θ)`. -/
theorem density_ω0 (θ : naturalParameter bernoulliFamily.d) :
    density bernoulliFamily θ ω0 = 1 - logistic (θ bernoulliIndex) := by
  -- The failure term is `1`.
  have hne := (one_add_exp_pos (θ bernoulliIndex)).ne'
  rw [density_eq_div]
  simp only [partitionTerm, dot_eq, stat_ω0, weight_eq, mul_zero, Real.exp_zero, one_mul]
  unfold logistic
  field_simp
  ring

/-- Success probability is `σ(θ)`. -/
theorem density_ω1 (θ : naturalParameter bernoulliFamily.d) :
    density bernoulliFamily θ ω1 = logistic (θ bernoulliIndex) := by
  -- The success term is `exp θ`.
  rw [density_eq_div]
  simp only [partitionTerm, dot_eq, stat_ω1, weight_eq, mul_one, one_mul]
  rfl

/-- Bernoulli expectations are logistic mixtures of the two outcome values. -/
theorem expectation_eq (θ : naturalParameter bernoulliFamily.d) (f : bernoulliFamily.Ω → ℝ) :
    expectationOf bernoulliFamily θ f =
      (1 - logistic (θ bernoulliIndex)) * f ω0 + logistic (θ bernoulliIndex) * f ω1 := by
  -- Expand the two-term sum.
  unfold expectationOf
  rw [sum_omega, density_ω0, density_ω1]

/-- The log-partition gradient is the logistic mean. -/
theorem gradient_eq (θ : naturalParameter bernoulliFamily.d) (i : Fin bernoulliFamily.d) :
    gradientLogPartition bernoulliFamily θ i = logistic (θ bernoulliIndex) := by
  -- Expected statistic `(1-p)·0 + p·1`.
  unfold gradientLogPartition expectedStatistic
  rw [expectation_eq, stat_ω0, stat_ω1]
  ring

/-- Failure score is `-σ(θ)`. -/
theorem score_ω0 (θ : naturalParameter bernoulliFamily.d) (i : Fin bernoulliFamily.d) :
    score bernoulliFamily θ ω0 i = -logistic (θ bernoulliIndex) := by
  -- Statistic `0` minus the mean.
  simp only [score, stat_ω0, gradient_eq, zero_sub]

/-- Success score is `1 - σ(θ)`. -/
theorem score_ω1 (θ : naturalParameter bernoulliFamily.d) (i : Fin bernoulliFamily.d) :
    score bernoulliFamily θ ω1 i = 1 - logistic (θ bernoulliIndex) := by
  -- Statistic `1` minus the mean.
  simp only [score, stat_ω1, gradient_eq]

/-- Every Bernoulli Fisher entry is the Bernoulli variance. -/
theorem fisherInformation_eq (θ : naturalParameter bernoulliFamily.d)
    (i j : Fin bernoulliFamily.d) :
    fisherInformation bernoulliFamily θ i j = logisticVar (θ bernoulliIndex) := by
  -- `(1-p)p² + p(1-p)² = p(1-p)`.
  show expectationOf bernoulliFamily θ _ = _
  rw [expectation_eq, score_ω0, score_ω0, score_ω1, score_ω1]
  unfold logisticVar
  ring

/-- Bernoulli Fisher information is the Bernoulli variance `σ(θ)(1-σ(θ))`. -/
theorem bernoulli_fisherInformation_eq_variance
    (θ : naturalParameter bernoulliFamily.d) :
    fisherInformation bernoulliFamily θ bernoulliIndex bernoulliIndex =
      bernoulliSigmoid θ * (1 - bernoulliSigmoid θ) := by
  -- `bernoulliSigmoid` is the logistic of the single coordinate.
  exact fisherInformation_eq θ _ _

end

end Fixtures

end FisherInformationAPI
