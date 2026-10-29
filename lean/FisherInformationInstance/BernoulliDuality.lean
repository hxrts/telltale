import FisherInformationInstance.BernoulliCalculus

/-! # Bernoulli Duality, Hessian, And KL

Genuine (non-vacuous) duality laws for the Bernoulli family in natural
parameter `η`: log-partition `A(η) = log (1 + e^η)`, mean `σ(η)`, dual
potential equal to the negative entropy, KL equal to the Bregman divergence of
`A`, minimality of the representation, and the Fisher/Hessian identity proved
from the actual second derivative of `A`.
-/

/-
The Problem. The Bernoulli laws instance needs real proofs of minimality,
Legendre duality, the dual potential, the KL closed form, KL zero iff equal,
natural-gradient existence, and Fisher = Hessian.

Solution Structure.
1. Scalar logit/log-logistic identities and strict softplus convexity.
2. Coordinate reductions for the single Bernoulli index.
3. One theorem per law.
-/

set_option autoImplicit false

namespace FisherInformationAPI

namespace Fixtures

open scoped BigOperators

noncomputable section

/-! ## Scalar Identities -/

/-- `1 - σ(x) = (1 + exp x)⁻¹`. -/
theorem one_sub_logistic (x : ℝ) : 1 - logistic x = (1 + Real.exp x)⁻¹ := by
  -- Clear the positive denominator.
  have hne := (one_add_exp_pos x).ne'
  unfold logistic
  field_simp
  ring

/-- `log σ(x) = x - A(x)`. -/
theorem log_logistic (x : ℝ) : Real.log (logistic x) = x - softplus x := by
  -- Logarithm of a quotient of positive reals.
  rw [logistic, Real.log_div (Real.exp_pos x).ne' (one_add_exp_pos x).ne', Real.log_exp]
  rfl

/-- `log (1 - σ(x)) = -A(x)`. -/
theorem log_one_sub_logistic (x : ℝ) : Real.log (1 - logistic x) = -softplus x := by
  -- Logarithm of an inverse.
  rw [one_sub_logistic, Real.log_inv]
  rfl

/-- The logit inverts the logistic: `log (σ / (1 - σ)) = x`. -/
theorem logit_logistic (x : ℝ) : Real.log (logistic x / (1 - logistic x)) = x := by
  -- Split the quotient and use the two log identities.
  rw [Real.log_div (logistic_pos x).ne' (by linarith [logistic_lt_one x]),
    log_logistic, log_one_sub_logistic]
  ring

/-- Strict Bregman gap of softplus (strict convexity of the log-partition). -/
theorem softplus_bregman_pos (x u : ℝ) (hu : u ≠ 0) :
    u * logistic x < softplus (x + u) - softplus x := by
  -- Strict concavity of `log` on the mixture `(1-p)·1 + p·e^u` with `e^u ≠ 1`.
  have hp1 : 0 < 1 - logistic x := by linarith [logistic_lt_one x]
  have hne : (1 : ℝ) ≠ Real.exp u := fun h => hu (Real.exp_eq_one_iff u |>.1 h.symm)
  have hc := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 one_pos)
    (Set.mem_Ioi.2 (Real.exp_pos u)) hne hp1 (logistic_pos x) (by ring)
  simp only [smul_eq_mul] at hc
  rw [softplus_ratio, Real.log_one, Real.log_exp,
    Real.log_div (one_add_exp_pos _).ne' (one_add_exp_pos x).ne'] at hc
  unfold softplus
  linarith

/-! ## Coordinate Reductions -/

/-- Every Bernoulli coordinate index is the single index. -/
theorem index_eq (i : Fin bernoulliFamily.d) : i = bernoulliIndex := by
  -- `Fin 1` has one element.
  have h := i.isLt
  change i.val < 1 at h
  exact Fin.ext (show i.val = 0 by omega)

/-- Bernoulli matrix-vector products reduce to one product. -/
theorem matrixVecMul_eq (A : Matrix (Fin bernoulliFamily.d) (Fin bernoulliFamily.d) ℝ)
    (v : Fin bernoulliFamily.d → ℝ) (i : Fin bernoulliFamily.d) :
    matrixVecMul A v i = A bernoulliIndex bernoulliIndex * v bernoulliIndex := by
  -- One-term sum at the single index.
  unfold matrixVecMul
  rw [sum_index, index_eq i]

/-- Bernoulli closed-form KL is the softplus Bregman gap. -/
theorem klClosedForm_eq (θ₁ θ₂ : naturalParameter bernoulliFamily.d) :
    klClosedForm bernoulliModel θ₁ θ₂ =
      softplus (θ₂ bernoulliIndex) - softplus (θ₁ bernoulliIndex) -
        (θ₂ bernoulliIndex - θ₁ bernoulliIndex) * logistic (θ₁ bernoulliIndex) := by
  -- Expand the log-partitions, the gradient, and the one-coordinate dot product.
  show logPartition bernoulliFamily θ₂ - logPartition bernoulliFamily θ₁ -
    dot (naturalParameterSub θ₂ θ₁) (gradientLogPartition bernoulliFamily θ₁) = _
  rw [logPartition_eq, logPartition_eq, dot_eq, gradient_eq]
  rfl

/-- The model logit inverts the model mean map. -/
theorem naturalParam_expectationParam (θ : naturalParameter bernoulliFamily.d) :
    bernoulliModel.naturalParam (bernoulliModel.expectationParam θ) = θ := by
  -- Coordinatewise `logit (σ η) = η`.
  ext i
  rw [index_eq i]
  exact logit_logistic (θ bernoulliIndex)

/-! ## Minimality And Legendre Duality -/

/-- The Bernoulli representation is minimal: `T = 0, 1` is affinely independent. -/
theorem bernoulli_minimal : isMinimal bernoulliFamily := by
  -- `v·0 = c` and `v·1 = c` force `v = 0`.
  rintro v ⟨c, hc⟩
  have h0 := hc ω0 (by rw [weight_eq]; exact one_ne_zero)
  have h1 := hc ω1 (by rw [weight_eq]; exact one_ne_zero)
  rw [dot_eq, stat_ω0] at h0
  rw [dot_eq, stat_ω1] at h1
  funext i
  rw [index_eq i]
  show v bernoulliIndex = 0
  linarith

/-- Bernoulli Legendre duality: `σ = ∇A` and `logit` inverts it on `(0, 1)`. -/
theorem bernoulli_legendreDuality : LegendreDuality bernoulliModel := by
  -- The mean map is the gradient; the logit is its inverse on the image.
  intro _
  refine ⟨fun θ => ?_, naturalParam_expectationParam, ?_⟩
  · ext i
    exact (gradient_eq θ i).symm
  · rintro μ ⟨θ, rfl⟩
    exact congrArg bernoulliModel.expectationParam (naturalParam_expectationParam θ)

/-- Bernoulli dual potential is `η σ(η) - A(η)`. -/
theorem dualPotential_eq (θ : naturalParameter bernoulliFamily.d) :
    dualPotential bernoulliModel (bernoulliModel.expectationParam θ) =
      θ bernoulliIndex * logistic (θ bernoulliIndex) - softplus (θ bernoulliIndex) := by
  -- Substitute the round trip `logit ∘ σ = id`.
  unfold dualPotential
  erw [naturalParam_expectationParam, logPartition_eq, dot_eq]
  rfl

/-- Bernoulli negative entropy is `η σ(η) - A(η)`. -/
theorem negEntropy_eq (θ : naturalParameter bernoulliFamily.d) :
    negEntropy bernoulliFamily θ =
      θ bernoulliIndex * logistic (θ bernoulliIndex) - softplus (θ bernoulliIndex) := by
  -- `(1-σ) log (1-σ) + σ log σ` with the log-logistic identities.
  unfold negEntropy
  rw [sum_omega, density_ω0, density_ω1, weight_eq, weight_eq, div_one, div_one,
    log_one_sub_logistic, log_logistic]
  ring

/-- Bernoulli dual potential is the negative entropy and the Legendre conjugate. -/
theorem bernoulli_dualPotentialEqLegendre : DualPotentialEqLegendre bernoulliModel := by
  -- Fenchel-Young is the softplus Bregman gap at `u = θ' - θ`.
  intro _ θ
  refine ⟨(dualPotential_eq θ).trans (negEntropy_eq θ).symm, fun θ' => ?_⟩
  erw [dualPotential_eq, dot_eq, logPartition_eq]
  have h := softplus_bregman_nonneg (θ bernoulliIndex)
    (θ' bernoulliIndex - θ bernoulliIndex)
  rw [add_sub_cancel] at h
  change θ' bernoulliIndex * logistic (θ bernoulliIndex) - _ ≤ _
  linarith

/-! ## KL Laws -/

/-- Bernoulli KL between densities equals the Bregman divergence of `A`. -/
theorem bernoulli_klClosedForm : KLClosedForm bernoulliModel := by
  -- Expand both outcomes and apply the log-logistic identities.
  intro θ₁ θ₂
  erw [klClosedForm_eq]
  show ∑ ω, density bernoulliFamily θ₁ ω *
    Real.log (density bernoulliFamily θ₁ ω / density bernoulliFamily θ₂ ω) = _
  have h1 := (logistic_pos (θ₁ bernoulliIndex)).ne'
  have h2 := (logistic_pos (θ₂ bernoulliIndex)).ne'
  have h3 : 1 - logistic (θ₁ bernoulliIndex) ≠ 0 := by linarith [logistic_lt_one (θ₁ bernoulliIndex)]
  have h4 : 1 - logistic (θ₂ bernoulliIndex) ≠ 0 := by linarith [logistic_lt_one (θ₂ bernoulliIndex)]
  erw [sum_omega, density_ω0, density_ω1, density_ω0, density_ω1,
    Real.log_div h3 h4, Real.log_div h1 h2, log_one_sub_logistic, log_one_sub_logistic,
    log_logistic, log_logistic]
  ring

/-- Bernoulli KL vanishes exactly at equal parameters. -/
theorem bernoulli_klZeroIffEqualParameters : KLZeroIffEqualParameters bernoulliModel := by
  -- Strict convexity of softplus.
  intro _ θ₁ θ₂
  erw [klClosedForm_eq]
  constructor
  · intro h
    by_contra hne
    have hu : θ₂ bernoulliIndex - θ₁ bernoulliIndex ≠ 0 := fun h' =>
      hne (by ext i; rw [index_eq i]; linarith)
    have hp := softplus_bregman_pos (θ₁ bernoulliIndex) _ hu
    rw [add_sub_cancel] at hp
    linarith
  · rintro rfl
    ring

/-! ## Natural Gradient And Hessian -/

/-- Entry of a `1 × 1` real matrix inverse. -/
theorem fin_one_inv_apply (A : Matrix (Fin 1) (Fin 1) ℝ) : A⁻¹ 0 0 = (A 0 0)⁻¹ := by
  -- `A⁻¹ = det⁻¹ • adj` and `adj = 1` in dimension one.
  rw [Matrix.inv_def, Matrix.adjugate_fin_one, Matrix.det_fin_one, Ring.inverse_eq_inv']
  simp

/-- The inverse Bernoulli Fisher matrix is the reciprocal variance. -/
theorem fisherAt_inv_apply (θ : naturalParameter bernoulliFamily.d) :
    (bernoulliModel.fisherAt θ)⁻¹ bernoulliIndex bernoulliIndex =
      (logisticVar (θ bernoulliIndex))⁻¹ := by
  -- Specialize the `1 × 1` inverse formula.
  exact (fin_one_inv_apply (bernoulliModel.fisherAt θ)).trans
    (congrArg Inv.inv (fisherInformation_eq θ _ _))

/-- Bernoulli natural-gradient step is `g / (σ(1-σ))`. -/
theorem naturalGradientStep_eq (θ : naturalParameter bernoulliFamily.d)
    (g : Fin bernoulliFamily.d → ℝ) (i : Fin bernoulliFamily.d) :
    naturalGradientStep bernoulliModel θ g i =
      (logisticVar (θ bernoulliIndex))⁻¹ * g bernoulliIndex := by
  -- `1 × 1` inverse entry times the single gradient coordinate.
  unfold naturalGradientStep
  erw [matrixVecMul_eq, fisherAt_inv_apply]

/-- Bernoulli natural gradients exist and are unique. -/
theorem bernoulli_naturalGradientExists : NaturalGradientExists bernoulliModel := by
  -- The scalar Fisher information `σ(1-σ)` is nonzero.
  intro _ θ g
  have hq := (logisticVar_pos (θ bernoulliIndex)).ne'
  have hF : bernoulliModel.fisherAt θ bernoulliIndex bernoulliIndex =
      logisticVar (θ bernoulliIndex) := fisherInformation_eq θ _ _
  refine ⟨funext fun i => ?_, fun step hstep => funext fun i => ?_⟩
  · erw [matrixVecMul_eq, naturalGradientStep_eq, hF, index_eq i]
    field_simp
  · have h := congrFun hstep bernoulliIndex
    erw [matrixVecMul_eq, hF] at h
    erw [naturalGradientStep_eq, index_eq i, ← h]
    field_simp

/-- Doubly perturbed Bernoulli log-partition is a shifted softplus. -/
theorem logPartition_perturb (θ : naturalParameter bernoulliFamily.d) (s t : ℝ)
    (i j : Fin bernoulliFamily.d) :
    logPartition bernoulliFamily
        (perturbParameter (perturbParameter θ s (basisVector j)) t (basisVector i)) =
      softplus (θ bernoulliIndex + s + t) := by
  -- Every basis vector is `1` at the single index.
  rw [logPartition_eq, index_eq i, index_eq j]
  simp [perturbParameter, basisVector]

/-- The Bernoulli log-partition Hessian is `σ(1-σ)`. -/
theorem hessian_eq (θ : naturalParameter bernoulliFamily.d) (i j : Fin bernoulliFamily.d) :
    hessianLogPartition bernoulliFamily θ i j = logisticVar (θ bernoulliIndex) := by
  -- Differentiate softplus twice: `A' = σ`, `σ' = σ(1-σ)`.
  have hin : ∀ s, deriv (fun t => softplus (θ bernoulliIndex + s + t)) 0 =
      logistic (θ bernoulliIndex + s) := fun s => by
    have h := HasDerivAt.comp_const_add (θ bernoulliIndex + s) 0
      (by rw [add_zero]; exact hasDerivAt_softplus (θ bernoulliIndex + s))
    exact h.deriv
  have hout := HasDerivAt.comp_const_add (θ bernoulliIndex) 0
    (by rw [add_zero]; exact hasDerivAt_logistic (θ bernoulliIndex))
  unfold hessianLogPartition
  simp only [logPartition_perturb, hin]
  exact hout.deriv

/-- Bernoulli Fisher information equals the log-partition Hessian. -/
theorem bernoulli_fisherEqHessian : FisherEqHessian bernoulliModel := by
  -- Both entries are `σ(1-σ)`.
  intro θ
  funext i j
  exact (fisherInformation_eq θ i j).trans (hessian_eq θ i j).symm

end

end Fixtures

end FisherInformationAPI
