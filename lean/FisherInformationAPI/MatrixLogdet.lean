import FisherInformationAPI.Core

/-! # FisherInformationAPI.MatrixLogdet

Matrix log-determinant monotonicity and submodularity surface.

Part of the `FisherInformationAPI` boundary (finite-discrete Fisher
information geometry); re-exported by the `FisherInformationAPI` module.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators Matrix MatrixOrder
open Asymptotics

noncomputable section

/-! ## Matrix Log-Det Transport Surface -/

/-- A positive-semidefinite matrix has determinant at least one after adding the identity. -/
theorem matrix_det_one_add_posSemidef_ge_one
    {d : Nat}
    (B : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.PosSemidef) :
    (1 : ℝ) ≤ (1 + B).det := by
  classical
  let U := hB.1.eigenvectorUnitary
  let Um : Matrix (Fin d) (Fin d) ℝ := U
  let D : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (fun i => hB.1.eigenvalues i)
  have hs :
      B = ((Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ)) U) D := by
    simpa [D] using hB.1.spectral_theorem
  have hunit : Um * star Um = 1 := by
    simp [Um]
  have hdet_unit : Um.det * (star Um).det = 1 := by
    rw [← Matrix.det_mul, hunit, Matrix.det_one]
  have hdet_diag : (1 : ℝ) ≤ (1 + D).det := by
    have hdiag :
        1 + D = Matrix.diagonal (fun i => 1 + hB.1.eigenvalues i) := by
      simp [D, ← Matrix.diagonal_one]
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.one_le_prod₀ (fun i _hi => by linarith [hB.eigenvalues_nonneg i])
  calc
    (1 : ℝ) ≤ (1 + D).det := hdet_diag
    _ = (1 + B).det := by
      rw [hs, Unitary.conjStarAlgAut_apply]
      change (1 + D).det = (1 + Um * D * star Um).det
      have hfactor :
          1 + Um * D * star Um = Um * (1 + D) * star Um := by
        calc
          1 + Um * D * star Um =
              Um * star Um + Um * D * star Um := by
                rw [hunit]
          _ = Um * (1 + D) * star Um := by
                rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
      rw [hfactor]
      rw [Matrix.det_mul, Matrix.det_mul]
      calc
        (1 + D).det =
            (Um.det * (star Um).det) * (1 + D).det := by
              rw [hdet_unit, one_mul]
        _ = Um.det * (1 + D).det * (star Um).det := by
              ring

/-- Loewner monotonicity of determinant under positive-semidefinite addition. -/
theorem matrix_det_monotone_under_psd_addition
    {d : Nat}
    (A Δ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef)
    (hΔ : Δ.PosSemidef) :
    A.det ≤ (A + Δ).det := by
  classical
  let S : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt A⁻¹
  let B : Matrix (Fin d) (Fin d) ℝ := S * Δ * S
  have hAunitdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAinv_nonneg : 0 ≤ A⁻¹ := by
    exact hA.inv.posSemidef.nonneg
  have hsqrt : S * S = A⁻¹ := by
    simpa [S] using CFC.sqrt_mul_sqrt_self A⁻¹ hAinv_nonneg
  have hS_self : S.conjTranspose = S := by
    simpa [Matrix.star_eq_conjTranspose] using
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A⁻¹)).star_eq
  have hS_transpose : S.transpose = S :=
    (Matrix.conjTranspose_eq_transpose_of_trivial S).symm.trans hS_self
  have hBpsd : B.PosSemidef := by
    have hconj := hΔ.mul_mul_conjTranspose_same S
    simpa [B, hS_transpose] using hconj
  have hdetB : (1 : ℝ) ≤ (1 + B).det :=
    matrix_det_one_add_posSemidef_ge_one B hBpsd
  have hdet_factor :
      (A + Δ).det = A.det * (1 + A⁻¹ * Δ).det := by
    simpa [Matrix.mul_one, Matrix.one_mul] using
      (Matrix.det_add_mul (A := A)
        (U := Δ) (V := (1 : Matrix (Fin d) (Fin d) ℝ)) hAunitdet)
  have hdet_conj :
      (1 + B).det = (1 + A⁻¹ * Δ).det := by
    calc
      (1 + B).det = (1 + (S * Δ) * S).det := by
        simp [B, Matrix.mul_assoc]
      _ = (1 + S * (S * Δ)).det := by
        exact Matrix.det_one_add_mul_comm (S * Δ) S
      _ = (1 + A⁻¹ * Δ).det := by
        rw [← Matrix.mul_assoc, hsqrt]
  rw [hdet_factor, ← hdet_conj]
  nlinarith [hA.det_pos, hdetB]

/-- Loewner monotonicity of matrix log-det under positive-semidefinite addition. -/
theorem matrix_logdet_monotone_under_psd_addition
    {d : Nat}
    (A Δ : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef)
    (hΔ : Δ.PosSemidef) :
    Real.log A.det ≤ Real.log (A + Δ).det := by
  exact Real.log_le_log hA.det_pos
    (matrix_det_monotone_under_psd_addition A Δ hA hΔ)

/-- Finite sums of PSD increments preserve matrix log-det monotonicity. -/
theorem matrix_logdet_monotone_under_psd_finset_sum
    {d α : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (increment : Fin α → Matrix (Fin d) (Fin d) ℝ)
    (selected : Finset (Fin α))
    (hA : A.PosDef)
    (hincrement : ∀ i ∈ selected, (increment i).PosSemidef) :
    Real.log A.det ≤
      Real.log (A + ∑ i ∈ selected, increment i).det := by
  exact matrix_logdet_monotone_under_psd_addition A
    (∑ i ∈ selected, increment i) hA
    (Matrix.posSemidef_sum selected hincrement)

/-- Weighted rank-one PSD increment `w • x xᵀ`. -/
def weightedRankOnePSDIncrement
    {d : Nat}
    (weight : ℝ)
    (feature : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  weight • Matrix.vecMulVec feature feature

/-- Weighted rank-one increments are PSD when the weight is nonnegative. -/
theorem weightedRankOnePSDIncrement_posSemidef
    {d : Nat}
    (weight : ℝ)
    (feature : Fin d → ℝ)
    (hweight : 0 ≤ weight) :
    (weightedRankOnePSDIncrement weight feature).PosSemidef := by
  simpa [weightedRankOnePSDIncrement] using
    (Matrix.posSemidef_vecMulVec_self_star feature).smul hweight

/-- Weighted rank-one increments in the one-column form used by the determinant lemma. -/
theorem weighted_rank_one_eq_replicate
    {d : Nat}
    (weight : ℝ)
    (feature : Fin d → ℝ) :
    weightedRankOnePSDIncrement weight feature =
      Matrix.replicateCol Unit (weight • feature) *
        Matrix.replicateRow Unit feature := by
  -- Expand both rank-one products entrywise.
  ext i j
  simp [weightedRankOnePSDIncrement, Matrix.vecMulVec_apply,
    Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow]
  ring

/-- Schur-complement block positivity from a Loewner comparison `A ≤ B`. -/
theorem matrix_schur_block_posSemidef_of_posDef_le
    {d : Nat}
    (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef)
    (hAB : A ≤ B) :
    (Matrix.fromBlocks B (1 : Matrix (Fin d) (Fin d) ℝ)
      ((1 : Matrix (Fin d) (Fin d) ℝ).conjTranspose) A⁻¹).PosSemidef := by
  -- The lower-right Schur complement is exactly `B - A`.
  letI := hA.inv.isUnit.invertible
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hschur := Matrix.PosDef.fromBlocks₂₂
    (A := B) (B := (1 : Matrix (Fin d) (Fin d) ℝ))
    (D := A⁻¹) hA.inv
  apply hschur.mpr
  have hAunitdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hinv : A⁻¹⁻¹ = A := Matrix.nonsing_inv_nonsing_inv A hAunitdet
  simpa [hinv, Matrix.mul_assoc] using hdiff

/-- Loewner order reverses under inverses for positive definite matrices. -/
theorem matrix_inv_antitone_of_posDef_le
    {d : Nat}
    (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  -- Read the same PSD block through the top-left Schur complement.
  rw [Matrix.le_iff]
  have hblock := matrix_schur_block_posSemidef_of_posDef_le A B hA hAB
  letI := hB.isUnit.invertible
  have hschur := Matrix.PosDef.fromBlocks₁₁
    (A := B) (B := (1 : Matrix (Fin d) (Fin d) ℝ))
    (D := A⁻¹) hB
  simpa [Matrix.mul_assoc] using hschur.mp hblock

/-- Inverse antitonicity lowers every quadratic form. -/
theorem matrix_quadratic_form_inv_antitone
    {d : Nat}
    (A B : Matrix (Fin d) (Fin d) ℝ)
    (feature : Fin d → ℝ)
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hAB : A ≤ B) :
    (feature ᵥ* B⁻¹) ⬝ᵥ feature ≤
      (feature ᵥ* A⁻¹) ⬝ᵥ feature := by
  -- Apply PSD nonnegativity to the inverse difference.
  have hinv : B⁻¹ ≤ A⁻¹ :=
    matrix_inv_antitone_of_posDef_le A B hA hB hAB
  have hpsd : (A⁻¹ - B⁻¹).PosSemidef := Matrix.le_iff.mp hinv
  have hnonneg := hpsd.dotProduct_mulVec_nonneg feature
  rw [star_trivial, Matrix.dotProduct_mulVec, Matrix.vecMul_sub,
    sub_dotProduct] at hnonneg
  linarith

/-- Weighted rank-one determinant factors shrink under Loewner growth. -/
theorem weighted_rank_one_factor_antitone
    {d : Nat}
    (A B : Matrix (Fin d) (Fin d) ℝ)
    (weight : ℝ)
    (feature : Fin d → ℝ)
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hAB : A ≤ B)
    (hweight : 0 ≤ weight) :
    1 + (feature ᵥ* B⁻¹) ⬝ᵥ (weight • feature) ≤
      1 + (feature ᵥ* A⁻¹) ⬝ᵥ (weight • feature) := by
  -- Pull out the nonnegative scalar and use quadratic-form antitonicity.
  have hquad := matrix_quadratic_form_inv_antitone A B feature hA hB hAB
  have hweighted :
      (feature ᵥ* B⁻¹) ⬝ᵥ (weight • feature) ≤
        (feature ᵥ* A⁻¹) ⬝ᵥ (weight • feature) := by
    simpa using mul_le_mul_of_nonneg_left hquad hweight
  linarith

/-- Matrix determinant lemma for a weighted rank-one update. -/
theorem det_add_weighted_rank_one
    {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (weight : ℝ)
    (feature : Fin d → ℝ)
    (hA : A.PosDef) :
    (A + weightedRankOnePSDIncrement weight feature).det =
      A.det * (1 + (feature ᵥ* A⁻¹) ⬝ᵥ (weight • feature)) := by
  -- Convert to the determinant lemma and simplify the 1x1 factor.
  classical
  have hAunitdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [weighted_rank_one_eq_replicate]
  rw [Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit) hAunitdet]
  apply congrArg (fun z => A.det * z)
  rw [Matrix.det_unique]
  simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow,
    dotProduct, Matrix.vecMul]

/-- The determinant-lemma factor is positive for PSD rank-one updates. -/
theorem weighted_rank_one_factor_pos
    {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (weight : ℝ)
    (feature : Fin d → ℝ)
    (hA : A.PosDef)
    (hweight : 0 ≤ weight) :
    0 < 1 + (feature ᵥ* A⁻¹) ⬝ᵥ (weight • feature) := by
  -- Compare positive determinants through the rank-one determinant lemma.
  have hincrement :
      (weightedRankOnePSDIncrement weight feature).PosSemidef :=
    weightedRankOnePSDIncrement_posSemidef weight feature hweight
  have hdet_update :
      0 < (A + weightedRankOnePSDIncrement weight feature).det :=
    (hA.add_posSemidef hincrement).det_pos
  rw [det_add_weighted_rank_one A weight feature hA] at hdet_update
  nlinarith [hA.det_pos]

/-- A weighted rank-one log-det marginal is the log of its determinant factor. -/
theorem logdet_rank_one_marginal_eq_log_factor
    {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (weight : ℝ)
    (feature : Fin d → ℝ)
    (hA : A.PosDef)
    (hweight : 0 ≤ weight) :
    Real.log (A + weightedRankOnePSDIncrement weight feature).det -
        Real.log A.det =
      Real.log (1 + (feature ᵥ* A⁻¹) ⬝ᵥ (weight • feature)) := by
  -- Use `log_mul` after identifying the determinant factor.
  have hfactor := weighted_rank_one_factor_pos A weight feature hA hweight
  rw [det_add_weighted_rank_one A weight feature hA]
  rw [Real.log_mul hA.det_pos.ne' hfactor.ne']
  ring

/-- Rank-one log-det marginals decrease as the base matrix grows. -/
theorem matrix_logdet_rank_one_marginal_antitone
    {d : Nat}
    (A B : Matrix (Fin d) (Fin d) ℝ)
    (weight : ℝ)
    (feature : Fin d → ℝ)
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hAB : A ≤ B)
    (hweight : 0 ≤ weight) :
    Real.log (B + weightedRankOnePSDIncrement weight feature).det -
        Real.log B.det ≤
      Real.log (A + weightedRankOnePSDIncrement weight feature).det -
        Real.log A.det := by
  -- Reduce both sides to determinant factors and use monotonicity of `log`.
  rw [logdet_rank_one_marginal_eq_log_factor B weight feature hB hweight]
  rw [logdet_rank_one_marginal_eq_log_factor A weight feature hA hweight]
  exact Real.log_le_log
    (weighted_rank_one_factor_pos B weight feature hB hweight)
    (weighted_rank_one_factor_antitone A B weight feature
      hA hB hAB hweight)

/-- Log-det monotonicity for finite sums of weighted rank-one PSD increments. -/
theorem matrix_logdet_monotone_under_weighted_rank_one_sum
    {d α : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (weight : Fin α → ℝ)
    (feature : Fin α → Fin d → ℝ)
    (selected : Finset (Fin α))
    (hA : A.PosDef)
    (hweight : ∀ i ∈ selected, 0 ≤ weight i) :
    Real.log A.det ≤
      Real.log
        (A + ∑ i ∈ selected,
          weightedRankOnePSDIncrement (weight i) (feature i)).det := by
  exact matrix_logdet_monotone_under_psd_finset_sum A
    (fun i => weightedRankOnePSDIncrement (weight i) (feature i))
    selected hA
    (fun i hi => weightedRankOnePSDIncrement_posSemidef
      (weight i) (feature i) (hweight i hi))

/-- Selected weighted rank-one information matrices stay positive definite. -/
theorem weighted_rank_one_information_posDef
    {d α : Nat}
    (prior : Matrix (Fin d) (Fin d) ℝ)
    (weight : Fin α → ℝ)
    (feature : Fin α → Fin d → ℝ)
    (selected : Finset (Fin α))
    (hprior : prior.PosDef)
    (hweight : ∀ i ∈ selected, 0 ≤ weight i) :
    (prior + ∑ i ∈ selected,
      weightedRankOnePSDIncrement (weight i) (feature i)).PosDef := by
  -- Add a finite PSD sum of weighted rank-one increments to the prior.
  exact hprior.add_posSemidef
    (Matrix.posSemidef_sum selected
      (fun i hi => weightedRankOnePSDIncrement_posSemidef
        (weight i) (feature i) (hweight i hi)))

/-- Subset inclusion gives Loewner growth of selected information matrices. -/
theorem weighted_rank_one_information_le
    {d α : Nat}
    (prior : Matrix (Fin d) (Fin d) ℝ)
    (weight : Fin α → ℝ)
    (feature : Fin α → Fin d → ℝ)
    {S T : Finset (Fin α)}
    (hST : S ⊆ T)
    (hweight : ∀ i ∈ T \ S, 0 ≤ weight i) :
    prior + ∑ i ∈ S, weightedRankOnePSDIncrement (weight i) (feature i) ≤
      prior + ∑ i ∈ T, weightedRankOnePSDIncrement (weight i) (feature i) := by
  -- The larger selection is the smaller one plus a PSD residual.
  rw [Matrix.le_iff]
  let residual : Matrix (Fin d) (Fin d) ℝ :=
    ∑ i ∈ T \ S, weightedRankOnePSDIncrement (weight i) (feature i)
  have hresidual : residual.PosSemidef :=
    Matrix.posSemidef_sum (T \ S)
      (fun i hi => weightedRankOnePSDIncrement_posSemidef
        (weight i) (feature i) (hweight i hi))
  have hsplit :
      prior + ∑ i ∈ T, weightedRankOnePSDIncrement (weight i) (feature i) =
        (prior + ∑ i ∈ S,
          weightedRankOnePSDIncrement (weight i) (feature i)) + residual := by
    have hsum :
        (∑ i ∈ T \ S, weightedRankOnePSDIncrement (weight i) (feature i)) +
            ∑ i ∈ S, weightedRankOnePSDIncrement (weight i) (feature i) =
          ∑ i ∈ T, weightedRankOnePSDIncrement (weight i) (feature i) :=
      Finset.sum_sdiff hST
    dsimp [residual]
    rw [← hsum]
    abel
  rw [hsplit]
  simpa [residual, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hresidual

/-- Inserting a fresh weighted rank-one item adds exactly that increment. -/
theorem weighted_rank_one_insert_eq_add
    {d α : Nat}
    (prior : Matrix (Fin d) (Fin d) ℝ)
    (weight : Fin α → ℝ)
    (feature : Fin α → Fin d → ℝ)
    (selected : Finset (Fin α))
    (candidate : Fin α)
    (hcandidate : candidate ∉ selected) :
    prior + ∑ i ∈ insert candidate selected,
        weightedRankOnePSDIncrement (weight i) (feature i) =
      (prior + ∑ i ∈ selected,
        weightedRankOnePSDIncrement (weight i) (feature i)) +
        weightedRankOnePSDIncrement (weight candidate) (feature candidate) := by
  -- Finset insertion contributes the candidate increment once.
  rw [Finset.sum_insert hcandidate]
  abel

/-- Finite-set matrix log-det submodularity for weighted rank-one increments. -/
theorem matrix_logdet_submodular_under_psd_increment
    {d α : Nat}
    (prior : Matrix (Fin d) (Fin d) ℝ)
    (weight : Fin α → ℝ)
    (feature : Fin α → Fin d → ℝ)
    {S T : Finset (Fin α)}
    (candidate : Fin α)
    (hprior : prior.PosDef)
    (hweight : ∀ i, 0 ≤ weight i)
    (hST : S ⊆ T)
    (hcandidate : candidate ∉ T) :
    Real.log
        (prior + ∑ i ∈ insert candidate T,
          weightedRankOnePSDIncrement (weight i) (feature i)).det -
        Real.log
          (prior + ∑ i ∈ T,
            weightedRankOnePSDIncrement (weight i) (feature i)).det ≤
      Real.log
        (prior + ∑ i ∈ insert candidate S,
          weightedRankOnePSDIncrement (weight i) (feature i)).det -
        Real.log
          (prior + ∑ i ∈ S,
            weightedRankOnePSDIncrement (weight i) (feature i)).det := by
  -- Reduce selected-set marginals to the base-matrix rank-one marginal theorem.
  have hcandidateS : candidate ∉ S := fun hS => hcandidate (hST hS)
  rw [weighted_rank_one_insert_eq_add prior weight feature T candidate hcandidate]
  rw [weighted_rank_one_insert_eq_add prior weight feature S candidate hcandidateS]
  exact matrix_logdet_rank_one_marginal_antitone
    (prior + ∑ i ∈ S, weightedRankOnePSDIncrement (weight i) (feature i))
    (prior + ∑ i ∈ T, weightedRankOnePSDIncrement (weight i) (feature i))
    (weight candidate) (feature candidate)
    (weighted_rank_one_information_posDef prior weight feature S
      hprior (fun i _hi => hweight i))
    (weighted_rank_one_information_posDef prior weight feature T
      hprior (fun i _hi => hweight i))
    (weighted_rank_one_information_le prior weight feature hST
      (fun i _hi => hweight i))
    (hweight candidate)

end

end FisherInformationAPI
