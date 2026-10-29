import FisherInformationAPI.MatrixLogdet

/-! # FisherInformationAPI.Certificate

Certificate-side PSD increments and log-det objectives.

Part of the `FisherInformationAPI` boundary (finite-discrete Fisher
information geometry); re-exported by the `FisherInformationAPI` module.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators Matrix MatrixOrder
open Asymptotics

noncomputable section

/-- Certificate-side PSD increment with a checked nonnegative log-det gain. -/
structure CertificatePSDIncrement (d : Nat) where
  matrix : Matrix (Fin d) (Fin d) ℝ
  psd : matrix.PosSemidef
  logdetGain : ℝ
  logdetGain_nonneg : 0 ≤ logdetGain

/-- Additive certificate log-det objective over a selected finite set. -/
def certificateLogdetObjective {d α : Nat}
    (priorLogDet : ℝ)
    (increment : Fin α → CertificatePSDIncrement d)
    (selected : Finset (Fin α)) : ℝ :=
  priorLogDet + ∑ i ∈ selected, (increment i).logdetGain

/-- Additive certificate log-det objective over an ordered certificate list. -/
def certificateLogdetObjectiveList {d : Nat}
    (priorLogDet : ℝ)
    (increments : List (CertificatePSDIncrement d)) : ℝ :=
  priorLogDet + (increments.map (fun increment => increment.logdetGain)).sum

/-- Matrix-backed certificate information matrix for selected increments. -/
def certificateInformationMatrix {d α : Nat}
    (prior : Matrix (Fin d) (Fin d) ℝ)
    (increment : Fin α → CertificatePSDIncrement d)
    (selected : Finset (Fin α)) : Matrix (Fin d) (Fin d) ℝ :=
  prior + ∑ i ∈ selected, (increment i).matrix

/-- Matrix-backed certificate log-det objective. -/
def certificateMatrixLogdetObjective {d α : Nat}
    (prior : Matrix (Fin d) (Fin d) ℝ)
    (increment : Fin α → CertificatePSDIncrement d)
    (selected : Finset (Fin α)) : ℝ :=
  Real.log (certificateInformationMatrix prior increment selected).det

/-- Marginal log-det gain for inserting one certificate increment. -/
def certificateLogdetMarginal {d α : Nat}
    (increment : Fin α → CertificatePSDIncrement d)
    (selected : Finset (Fin α))
    (candidate : Fin α) : ℝ :=
  if candidate ∈ selected then 0 else (increment candidate).logdetGain

/-- Sum of checked nonnegative certificate log-det gains is nonnegative. -/
theorem certificate_logdet_gain_list_nonneg
    {d : Nat}
    (increments : List (CertificatePSDIncrement d)) :
    0 ≤ (increments.map (fun increment => increment.logdetGain)).sum := by
  exact List.sum_nonneg
    (fun gain hgain => by
      rcases List.mem_map.mp hgain with ⟨increment, _hincrement, rfl⟩
      exact increment.logdetGain_nonneg)

/-- Selected certificate log-det objective is monotone under set inclusion. -/
theorem certificate_logdet_objective_monotone
    {d α : Nat}
    (priorLogDet : ℝ)
    (increment : Fin α → CertificatePSDIncrement d)
    {S T : Finset (Fin α)}
    (hST : S ⊆ T) :
    certificateLogdetObjective priorLogDet increment S ≤
      certificateLogdetObjective priorLogDet increment T := by
  -- The objective is a prior plus a finite sum of nonnegative log-det gains.
  unfold certificateLogdetObjective
  have hsum :
      ∑ i ∈ S, (increment i).logdetGain ≤
        ∑ i ∈ T, (increment i).logdetGain :=
    (Finset.sum_le_sum_of_subset_of_nonneg hST
      (fun i _hi _hnot => (increment i).logdetGain_nonneg))
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hsum priorLogDet

/-- Appending certificate increments can only increase the list objective. -/
theorem certificate_logdet_objective_list_monotone
    {d : Nat}
    (priorLogDet : ℝ)
    (selected extra : List (CertificatePSDIncrement d)) :
    certificateLogdetObjectiveList priorLogDet selected ≤
      certificateLogdetObjectiveList priorLogDet (selected ++ extra) := by
  unfold certificateLogdetObjectiveList
  rw [List.map_append, List.sum_append]
  linarith [certificate_logdet_gain_list_nonneg extra]

/-- Matrix-backed certificate information matrices stay positive definite. -/
theorem certificate_information_matrix_posDef
    {d α : Nat}
    (prior : Matrix (Fin d) (Fin d) ℝ)
    (increment : Fin α → CertificatePSDIncrement d)
    (selected : Finset (Fin α))
    (hprior : prior.PosDef) :
    (certificateInformationMatrix prior increment selected).PosDef := by
  unfold certificateInformationMatrix
  exact hprior.add_posSemidef
    (Matrix.posSemidef_sum selected
      (fun i _hi => (increment i).psd))

/-- Matrix-backed certificate log-det objective is monotone under set inclusion. -/
theorem certificate_matrix_logdet_objective_monotone
    {d α : Nat}
    (prior : Matrix (Fin d) (Fin d) ℝ)
    (increment : Fin α → CertificatePSDIncrement d)
    {S T : Finset (Fin α)}
    (hprior : prior.PosDef)
    (hST : S ⊆ T) :
    certificateMatrixLogdetObjective prior increment S ≤
      certificateMatrixLogdetObjective prior increment T := by
  classical
  unfold certificateMatrixLogdetObjective certificateInformationMatrix
  let residual : Matrix (Fin d) (Fin d) ℝ :=
    ∑ i ∈ T \ S, (increment i).matrix
  have hbase :
      (prior + ∑ i ∈ S, (increment i).matrix).PosDef :=
    hprior.add_posSemidef
      (Matrix.posSemidef_sum S
        (fun i _hi => (increment i).psd))
  have hresidual : residual.PosSemidef := by
    exact Matrix.posSemidef_sum (T \ S)
      (fun i _hi => (increment i).psd)
  have hsplit :
      prior + ∑ i ∈ T, (increment i).matrix =
        (prior + ∑ i ∈ S, (increment i).matrix) + residual := by
    have hsum :
        (∑ i ∈ T \ S, (increment i).matrix) +
            ∑ i ∈ S, (increment i).matrix =
          ∑ i ∈ T, (increment i).matrix :=
      Finset.sum_sdiff hST
    dsimp [residual]
    rw [← hsum]
    abel
  rw [hsplit]
  exact matrix_logdet_monotone_under_psd_addition
    (prior + ∑ i ∈ S, (increment i).matrix)
    residual hbase hresidual

/-- Additive certificate log-det increments satisfy diminishing returns. -/
theorem certificate_logdet_objective_submodular
    {d α : Nat}
    (increment : Fin α → CertificatePSDIncrement d)
    {S T : Finset (Fin α)}
    (hST : S ⊆ T)
    (candidate : Fin α) :
    certificateLogdetMarginal increment T candidate ≤
      certificateLogdetMarginal increment S candidate := by
  -- Membership in the smaller set implies membership in the larger set.
  unfold certificateLogdetMarginal
  by_cases hS : candidate ∈ S
  · have hT : candidate ∈ T := hST hS
    simp [hS, hT]
  · by_cases hT : candidate ∈ T
    · simp [hS, hT, (increment candidate).logdetGain_nonneg]
    · simp [hS, hT]

/-- List-level additive certificate log-det increments satisfy diminishing returns. -/
theorem certificate_logdet_objective_list_submodular
    {d : Nat}
    (priorLogDet : ℝ)
    (small large : List (CertificatePSDIncrement d))
    (increment : CertificatePSDIncrement d)
    (_hSublist : small.Sublist large) :
    certificateLogdetObjectiveList priorLogDet (large ++ [increment]) -
        certificateLogdetObjectiveList priorLogDet large ≤
      certificateLogdetObjectiveList priorLogDet (small ++ [increment]) -
        certificateLogdetObjectiveList priorLogDet small := by
  unfold certificateLogdetObjectiveList
  simp [List.map_append, List.sum_append, add_comm]

end

end FisherInformationAPI
