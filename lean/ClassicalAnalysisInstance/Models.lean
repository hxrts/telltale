import ClassicalAnalysisInstance.RealConcrete

/-! # Entropy API: Concrete Models

Concrete real-valued implementations of the abstract entropy model API,
providing Shannon entropy, KL divergence, and mutual information over
finite distributions. -/

/-
The Problem. The abstract entropy API (`Model`) requires concrete
implementations with law proofs (nonnegativity, bounds, Gibbs' inequality).
These laws are proven for raw real-valued functions in `RealConcrete` but
need wrapping to match the `Distribution`-based API.

Solution Structure. Define `realModel : Model` forwarding to `RealConcrete`.
Provide private helper theorems that unpack `Distribution` fields and
forward to the underlying `RealConcrete` law proofs. Export the model
with its law witnesses.
-/

namespace EntropyAPI

open scoped BigOperators Classical

noncomputable section

/-! ## Real-Valued Model -/

/-- Concrete entropy operations used by the abstract API wrappers. -/
noncomputable def realModel : Model where
  shannonEntropy := RealConcrete.shannonEntropy
  klDivergence := RealConcrete.klDivergence
  mutualInfo := RealConcrete.mutualInfo

/-! ## Law Helpers -/

/-- Shannon entropy nonnegativity for the concrete model. -/
private theorem shannonEntropy_nonneg_real {α : Type*} [Fintype α]
    (d : Distribution α) :
    0 ≤ RealConcrete.shannonEntropy d.pmf := by
  -- Forward to the concrete theorem with unpacked distribution obligations.
  simpa using
    RealConcrete.shannonEntropy_nonneg d.pmf d.nonneg d.sum_one

/-- Shannon entropy `log |α|` upper bound for the concrete model. -/
private theorem shannonEntropy_le_log_card_real {α : Type*} [Fintype α] [Nonempty α]
    (d : Distribution α) :
    RealConcrete.shannonEntropy d.pmf ≤ Real.log (Fintype.card α) := by
  -- Forward to the concrete theorem with unpacked distribution obligations.
  simpa using
    RealConcrete.shannonEntropy_le_log_card d.pmf d.nonneg d.sum_one

/-- KL nonnegativity for the concrete model. -/
private theorem klDivergence_nonneg_real {α : Type*} [Fintype α]
    (p q : Distribution α)
    (habs : ∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) :
    0 ≤ RealConcrete.klDivergence p.pmf q.pmf := by
  -- Forward to the concrete theorem with unpacked distribution obligations.
  exact RealConcrete.klDivergence_nonneg
    p.pmf q.pmf p.nonneg p.sum_one q.nonneg q.sum_one habs

/-- KL zero characterization for the concrete model. -/
private theorem klDivergence_eq_zero_iff_real {α : Type*} [Fintype α]
    (p q : Distribution α)
    (habs : ∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) :
    RealConcrete.klDivergence p.pmf q.pmf = 0 ↔ p.pmf = q.pmf := by
  -- Forward to the concrete theorem with unpacked distribution obligations.
  exact RealConcrete.klDivergence_eq_zero_iff
    p.pmf q.pmf p.nonneg p.sum_one q.nonneg q.sum_one habs

/-- Erasure law for concrete mutual information. -/
private theorem mutualInfo_zero_of_erasure_real
    {L O : Type} [Fintype L] [Fintype O] [DecidableEq O]
    (labelDist : L → ℝ)
    (h_nn : ∀ l, 0 ≤ labelDist l)
    (h_sum : ∑ l, labelDist l = 1)
    (joint : L × O → ℝ)
    (hErase : IsErasureKernel labelDist joint) :
    RealConcrete.mutualInfo joint = 0 := by
  -- Forward directly to the concrete erasure theorem.
  exact RealConcrete.mutualInfo_zero_of_erasure
    labelDist h_nn h_sum joint hErase

/-! ## Real-Valued Laws Instance -/

/-- Noncomputable concrete laws witnessing `EntropyAPI.Laws`. -/
noncomputable instance realLaws : Laws where
  toModel := realModel
  shannonEntropy_nonneg := by
    -- Discharge this field using the specialized helper theorem.
    intro α _ d
    simpa [realModel] using shannonEntropy_nonneg_real d
  shannonEntropy_le_log_card := by
    -- Discharge this field using the specialized helper theorem.
    intro α _ _ d
    simpa [realModel] using shannonEntropy_le_log_card_real d
  klDivergence_nonneg := by
    -- Discharge this field using the specialized helper theorem.
    intro α _ p q habs
    simpa [realModel] using klDivergence_nonneg_real p q habs
  klDivergence_eq_zero_iff := by
    -- Discharge this field using the specialized helper theorem.
    intro α _ p q habs
    simpa [realModel] using klDivergence_eq_zero_iff_real p q habs
  mutualInfo_zero_of_erasure := by
    -- Discharge this field using the specialized helper theorem.
    intro L O _ _ _ labelDist h_nn h_sum joint hErase
    simpa [realModel] using
      mutualInfo_zero_of_erasure_real labelDist h_nn h_sum joint hErase

/-! ## Extended Real-Analysis Model -/

/-- Concrete realizations for the extended analysis interface. -/
noncomputable def realAnalysisModel : AnalysisModel where
  exponentialTail := fun σ t => 2 * Real.exp (-(t ^ 2) / (2 * σ ^ 2))
  fluctuationScale := fun n => Real.sqrt n
  finiteAverage := fun {n} x => if _ : n = 0 then 0 else (∑ i, x i) / (n : ℝ)
  normalizedCumulative := fun x μ N t =>
    (Finset.sum (Finset.range t) (fun i => x i - μ)) / Real.sqrt N
  transitionMatrixComplex := fun kernel =>
    (Matrix.of kernel).map (algebraMap ℝ ℂ)
  nontrivialSpectrumModuli := fun kernel =>
    { r | ∃ z ∈ spectrum ℂ ((Matrix.of kernel).map (algebraMap ℝ ℂ)),
      z ≠ (1 : ℂ) ∧ r = ‖z‖ }
  secondSpectrumValue := fun kernel =>
    sSup ({ r | ∃ z ∈ spectrum ℂ ((Matrix.of kernel).map (algebraMap ℝ ℂ)),
      z ≠ (1 : ℂ) ∧ r = ‖z‖ } : Set ℝ)
  spectralGapValue := fun kernel =>
    1 - sSup ({ r | ∃ z ∈ spectrum ℂ ((Matrix.of kernel).map (algebraMap ℝ ℂ)),
      z ≠ (1 : ℂ) ∧ r = ‖z‖ } : Set ℝ)

/-- Noncomputable laws for the extended analysis interface. -/
-- Extended Real-Analysis Laws

noncomputable instance realAnalysisLaws : AnalysisLaws where
  toAnalysisModel := realAnalysisModel
  exponentialTail_nonneg := by
    -- Exponential tails are nonnegative because `exp` is positive.
    intro σ t
    simp [realAnalysisModel]
    positivity
  exponentialTail_zero := by
    -- At zero threshold, the tail form evaluates to `2`.
    intro σ
    simp [realAnalysisModel]
  fluctuationScale_pos := by
    -- Square roots of positive reals are positive.
    intro n hn
    change 0 < Real.sqrt n
    exact Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  fluctuationScale_sq := by
    -- `(sqrt n)^2 = n` for `n : Nat` cast to `ℝ`.
    intro n
    change (Real.sqrt n) ^ 2 = n
    have hnonneg : (0 : ℝ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    exact Real.sq_sqrt hnonneg

  -- Extended Laws: Finite Averages and Cumulative Sums

  finiteAverage_perm := by
    -- Finite sums are invariant under permutation of finite indices.
    intro n σ x
    change
      (if h : n = 0 then 0 else (∑ i, x (σ i)) / (n : ℝ)) =
      (if h : n = 0 then 0 else (∑ i, x i) / (n : ℝ))
    by_cases h : n = 0
    · simp [h]
    · have hsum :
        (∑ i, x (σ i)) = ∑ i, x i := by
          simpa using
            (Fintype.sum_equiv σ (fun i => x (σ i)) x (by intro i; rfl))
      simp [h, hsum]
  finiteAverage_const := by
    -- The average of a constant family is that constant.
    intro n c hn
/- ## Structured Block 1 -/
    change (if h : n = 0 then 0 else (∑ _ : Fin n, c) / (n : ℝ)) = c
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp [hn, hnR]
  normalizedCumulative_const_zero := by
    -- Centering a constant sequence gives zero increments.
    intro c N t hN
    change
      (Finset.sum (Finset.range t) (fun i => ((fun _ => c) i - c)) / Real.sqrt N) = 0
    have hsum : Finset.sum (Finset.range t) (fun i => ((fun _ => c) i - c)) = 0 := by
      simp
    have hsqrt : (Real.sqrt N) ≠ 0 := by
      exact Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hN))
    simp

  -- Extended Laws: Spectral Gap Identity

  spectral_gap_eq := by
    -- The gap field is defined as `1 - secondSpectrumValue`.
    intro State _ _ kernel
    simp [realAnalysisModel]

end
end EntropyAPI
