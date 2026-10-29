import FisherInformationAPI.Geometry

/-! # FisherInformationAPI.Estimation

Cramer-Rao bounds, Fisher volume, reachability, and natural gradients.

Part of the `FisherInformationAPI` boundary (finite-discrete Fisher
information geometry); re-exported by the `FisherInformationAPI` module.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators Matrix MatrixOrder
open Asymptotics

noncomputable section

/-! ## Cramer-Rao Bounds -/

/-- Pointwise order on square matrices through PSD of the difference. -/
def MatrixPSDLe {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  MatrixPSD (fun i j => B i j - A i j)

/-- An estimator is locally unbiased for the natural parameter at `θ`.

Its mean is `θ`, and to first order it tracks parameter changes:
`∂_j E_θ[g_i] = E_θ[g_i · s_j] = δ_ij` (score identity for exponential
families). Mean-unbiasedness at the single point `θ` alone would admit the
constant estimator `g ≡ θ` of zero variance, for which Cramer-Rao is false. -/
def locallyUnbiasedEstimator (M : Model)
    (θ : naturalParameter M.family.d)
    (g : M.family.Ω → Fin M.family.d → ℝ) : Prop :=
  (∀ i, expectationOf M.family θ (fun ω => g ω i) = θ i) ∧
    ∀ i j, expectationOf M.family θ (fun ω => g ω i * score M.family θ ω j) =
      if i = j then 1 else 0

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
  ∀ θ g, locallyUnbiasedEstimator M θ g →
    MatrixPSDLe (M.fisherAt θ)⁻¹ (estimatorCovariance M θ g)

/-- Re-export Cramer-Rao from an explicit law witness. -/
theorem cramer_rao_bound
    (M : Model) (hCR : CramerRaoBound M)
    (θ : naturalParameter M.family.d)
    (g : M.family.Ω → Fin M.family.d → ℝ)
    (hunbiased : locallyUnbiasedEstimator M θ g) :
    MatrixPSDLe (M.fisherAt θ)⁻¹ (estimatorCovariance M θ g) := by
  -- The API theorem isolates the analytic proof obligation in the law witness.
  exact hCR θ g hunbiased

/-! ## Fisher Volume And Reachability -/

/-- Fisher (Jeffreys) volume of a region in natural-parameter space:
`∫_{region} √(det I(θ)) dθ` against Lebesgue measure on the coordinates. -/
def fisherVolume (M : Model)
    (region : Set (naturalParameter M.family.d)) : ENNReal :=
  ∫⁻ x in {x : Fin M.family.d → ℝ | (⟨x⟩ : naturalParameter M.family.d) ∈ region},
    ENNReal.ofReal (Real.sqrt (M.fisherAt ⟨x⟩).det)

/-- Fisher volume is nonnegative as an extended nonnegative real. -/
theorem fisherVolume_nonneg (M : Model)
    (region : Set (naturalParameter M.family.d)) :
    0 ≤ fisherVolume M region := by
  -- The codomain `ℝ≥0∞` is ordered above zero.
  exact bot_le

/-- The empty region has zero Fisher volume. -/
theorem fisherVolume_zero_of_empty (M : Model) :
    fisherVolume M (∅ : Set (naturalParameter M.family.d)) = 0 := by
  -- The coordinate preimage of the empty region is empty.
  simp [fisherVolume]

/-- Parameters reachable from `start` in at most `steps` moves, each changing
every natural coordinate by at most `stepBudget`: the sup-norm box of radius
`steps * stepBudget` around `start` (empty when the radius is negative). -/
def reachabilityRegion (M : Model)
    (start : naturalParameter M.family.d)
    (steps : ℕ)
    (stepBudget : ℝ) :
    Set (naturalParameter M.family.d) :=
  {θ | ∀ i, |θ i - start i| ≤ steps * stepBudget}

/-- Law: reachable Fisher volume grows at most like the reachable coordinate
volume `(2 · steps · stepBudget)^d`, up to a model constant `C` bounding
`√(det I)` (bounded statistics give bounded Fisher information). -/
abbrev ReachabilityVolumeBound (M : Model) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ start steps stepBudget,
    fisherVolume M (reachabilityRegion M start steps stepBudget) ≤
      ENNReal.ofReal C *
        ENNReal.ofReal (2 * (steps * stepBudget)) ^ M.family.d

/-- Coordinate preimage of a reachability region is a closed coordinate box. -/
theorem reachabilityRegion_preimage (M : Model)
    (start : naturalParameter M.family.d) (steps : ℕ) (stepBudget : ℝ) :
    {x : Fin M.family.d → ℝ |
        (⟨x⟩ : naturalParameter M.family.d) ∈ reachabilityRegion M start steps stepBudget} =
      Set.Icc (fun i => start i - steps * stepBudget)
        (fun i => start i + steps * stepBudget) := by
  -- Pointwise `|x i - s i| ≤ r` is `s i - r ≤ x i ≤ s i + r`.
  ext x
  simp only [reachabilityRegion, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def, abs_le]
  change (∀ i, _ ∧ _) ↔ _
  constructor
  · intro h
    exact ⟨fun i => by linarith [(h i).1], fun i => by linarith [(h i).2]⟩
  · intro h i
    exact ⟨by linarith [h.1 i], by linarith [h.2 i]⟩

/-- A uniform bound `√(det I) ≤ C` yields the reachability volume law. -/
theorem reachabilityVolumeBound_of_sqrt_det_le (M : Model) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ θ, Real.sqrt (M.fisherAt θ).det ≤ C) :
    ReachabilityVolumeBound M := by
  -- Bound the integrand by `C`, then compute the Lebesgue volume of the box.
  refine ⟨C, hC, fun start steps stepBudget => ?_⟩
  unfold fisherVolume
  rw [reachabilityRegion_preimage]
  calc _ ≤ ∫⁻ _ in Set.Icc (fun i => start i - steps * stepBudget)
          (fun i => start i + steps * stepBudget), ENNReal.ofReal C :=
        MeasureTheory.setLIntegral_mono measurable_const
          (fun x _ => ENNReal.ofReal_le_ofReal (hbound _))
    _ = _ := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Icc_pi]
        congr 1
        rw [Finset.prod_congr rfl (fun i _ => congrArg ENNReal.ofReal
          (show start i + steps * stepBudget - (start i - steps * stepBudget) =
            2 * (steps * stepBudget) by ring)),
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]

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

/-- Law: for minimal families the Fisher matrix is invertible, so the natural
gradient `F(θ)⁻¹ g` is the unique solution of `F(θ) · step = g`. -/
abbrev NaturalGradientExists (M : Model) : Prop :=
  isMinimal M.family → ∀ θ gradient,
    matrixVecMul (M.fisherAt θ) (naturalGradientStep M θ gradient) = gradient ∧
      ∀ step, matrixVecMul (M.fisherAt θ) step = gradient →
        step = naturalGradientStep M θ gradient

end

end FisherInformationAPI
