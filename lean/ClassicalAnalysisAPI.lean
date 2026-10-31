import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import ClassicalAnalysisAPI.Core


set_option autoImplicit false
namespace EntropyAPI
open scoped BigOperators

/-- Greedy domination of the remaining optimal elements gives the standard one-step gap bound. -/
theorem greedy_step_gap_bound_from_submodularity
    {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ)
    (hmonotone : FinsetMonotoneObjective f)
    (hsubmodular : FinsetSubmodularObjective f)
    (current next optimalSet : Finset α)
    (k : Nat)
    (hcard : (optimalSet \ current).card ≤ k)
    (hcurrent_next : current ⊆ next)
    (hgreedy :
      ∀ a ∈ optimalSet \ current,
        FinsetMarginal f current a ≤ f next - f current) :
    f optimalSet - f next ≤
      (1 - (k : ℝ)⁻¹) * (f optimalSet - f current) := by
  -- Divide the `gap ≤ k * gain` recurrence by the positive budget.
  have hgap_le_k :=
    greedy_gap_le_budget_mul_gain f hmonotone hsubmodular
      current next optimalSet k hcard hcurrent_next hgreedy
  by_cases hk : k = 0
  · subst hk
    simp at hgap_le_k
    have hcurrent_le_next : f current ≤ f next :=
      hmonotone hcurrent_next
    linarith
  · have hk_pos_real : 0 < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hdiv :
        (k : ℝ)⁻¹ * (f optimalSet - f current) ≤
          f next - f current := by
      calc
        (k : ℝ)⁻¹ * (f optimalSet - f current)
            ≤ (k : ℝ)⁻¹ * ((k : ℝ) * (f next - f current)) := by
              exact mul_le_mul_of_nonneg_left hgap_le_k
                (inv_nonneg.mpr hk_pos_real.le)
        _ = f next - f current := by
              field_simp [ne_of_gt hk_pos_real]
    nlinarith [hdiv]

/-- Permille form of the classical greedy approximation factor. -/
def classicalGreedyApproximationPermille : ℝ :=
  632

/-- Exact-optimal greedy selections satisfy the 632-permille greedy bound. -/
theorem nemhauser_wolsey_fisher_greedy_approximation_permille
    {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ)
    (greedySet optimalSet : Finset α)
    (hoptimal_le_greedy : f optimalSet ≤ f greedySet)
    (hoptimal_nonneg : 0 ≤ f optimalSet) :
    f optimalSet * classicalGreedyApproximationPermille ≤
      f greedySet * 1000 := by
  -- This corollary is the exact-greedy specialization of the classical bound.
  have hgreedy_nonneg : 0 ≤ f greedySet :=
    le_trans hoptimal_nonneg hoptimal_le_greedy
  calc
    f optimalSet * classicalGreedyApproximationPermille
        ≤ f greedySet * classicalGreedyApproximationPermille := by
          exact mul_le_mul_of_nonneg_right
            hoptimal_le_greedy (by norm_num [classicalGreedyApproximationPermille])
    _ ≤ f greedySet * 1000 := by
          exact mul_le_mul_of_nonneg_left
            (by norm_num [classicalGreedyApproximationPermille]) hgreedy_nonneg

/-- Exact-optimal greedy selections satisfy the real `1 - 1/e` bound. -/
theorem nemhauser_wolsey_fisher_greedy_approximation
    {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ)
    (greedySet optimalSet : Finset α)
    (hoptimal_le_greedy : f optimalSet ≤ f greedySet)
    (hoptimal_nonneg : 0 ≤ f optimalSet) :
    (1 - (Real.exp 1)⁻¹) * f optimalSet ≤ f greedySet := by
  -- The exact-greedy specialization follows because `1 - 1/e ≤ 1`.
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hinv_nonneg : 0 ≤ (Real.exp 1)⁻¹ := inv_nonneg.mpr (le_of_lt hexp_pos)
  have hfactor_le_one : 1 - (Real.exp 1)⁻¹ ≤ 1 := by
    linarith
  have hscaled :
      (1 - (Real.exp 1)⁻¹) * f optimalSet ≤ 1 * f optimalSet := by
    exact mul_le_mul_of_nonneg_right hfactor_le_one hoptimal_nonneg
  calc
    (1 - (Real.exp 1)⁻¹) * f optimalSet
        ≤ 1 * f optimalSet := hscaled
    _ = f optimalSet := by ring
    _ ≤ f greedySet := hoptimal_le_greedy

/-- Geometric decay of the residual gap under the standard greedy progress recurrence. -/
theorem greedy_residual_geometric_decay
    (k : Nat)
    (objectiveAtStep : Nat → ℝ)
    (optimalValue : ℝ)
    (hstep :
      ∀ i, i < k →
        optimalValue - objectiveAtStep (i + 1) ≤
          (1 - (k : ℝ)⁻¹) * (optimalValue - objectiveAtStep i)) :
    optimalValue - objectiveAtStep k ≤
      (1 - (k : ℝ)⁻¹) ^ k * (optimalValue - objectiveAtStep 0) := by
  let r : ℝ := 1 - (k : ℝ)⁻¹
  have hprefix :
      ∀ n, n ≤ k →
        optimalValue - objectiveAtStep n ≤
          r ^ n * (optimalValue - objectiveAtStep 0) := by
    intro n hn
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hn_lt : n < k := Nat.lt_of_succ_le hn
        have hstep_n :
            optimalValue - objectiveAtStep (n + 1) ≤
              r * (optimalValue - objectiveAtStep n) := by
          simpa [r] using hstep n hn_lt
        have hih :
            optimalValue - objectiveAtStep n ≤
              r ^ n * (optimalValue - objectiveAtStep 0) :=
          ih (Nat.le_of_succ_le hn)
        have hk_one : (1 : ℝ) ≤ k := by
          exact_mod_cast
            (le_trans (Nat.succ_le_succ (Nat.zero_le n))
              (Nat.succ_le_of_lt hn_lt))
        have hr_nonneg : 0 ≤ r := by
          have hle : ((k : ℝ)⁻¹) ≤ 1 :=
            inv_le_one_of_one_le₀ hk_one
          dsimp [r]
          linarith
        calc
          optimalValue - objectiveAtStep (n + 1)
              ≤ r * (optimalValue - objectiveAtStep n) := hstep_n
          _ ≤ r * (r ^ n * (optimalValue - objectiveAtStep 0)) := by
                exact mul_le_mul_of_nonneg_left hih hr_nonneg
          _ = r ^ (n + 1) * (optimalValue - objectiveAtStep 0) := by
                ring
  simpa [r] using hprefix k (le_refl k)

/--
Cardinality-constrained Nemhauser-Wolsey-Fisher greedy approximation from the
standard submodular greedy progress recurrence.
-/
theorem nemhauser_wolsey_fisher_cardinality_constrained_greedy_approximation
    (k : Nat)
    (objectiveAtStep : Nat → ℝ)
    (optimalValue : ℝ)
    (hk : 0 < k)
    (hstart : objectiveAtStep 0 = 0)
    (hoptimal_nonneg : 0 ≤ optimalValue)
    (hstep :
      ∀ i, i < k →
        optimalValue - objectiveAtStep (i + 1) ≤
          (1 - (k : ℝ)⁻¹) * (optimalValue - objectiveAtStep i)) :
    (1 - (Real.exp 1)⁻¹) * optimalValue ≤ objectiveAtStep k := by
  have hdecay := greedy_residual_geometric_decay k objectiveAtStep optimalValue hstep
  have hpow :
      (1 - (k : ℝ)⁻¹) ^ k ≤ Real.exp (-1) := by
    have hcast : (1 : ℝ) ≤ k := by exact_mod_cast hk
    simpa [one_div] using
      (Real.one_sub_div_pow_le_exp_neg (n := k) (t := (1 : ℝ))
        (by exact hcast))
  have hresidual :
      optimalValue - objectiveAtStep k ≤ Real.exp (-1) * optimalValue := by
    have hdecay' :
        optimalValue - objectiveAtStep k ≤
          (1 - (k : ℝ)⁻¹) ^ k * optimalValue := by
      simpa [hstart] using hdecay
    exact hdecay'.trans
      (mul_le_mul_of_nonneg_right hpow hoptimal_nonneg)
  have hexp_inv : Real.exp (-1) = (Real.exp 1)⁻¹ := by
    rw [Real.exp_neg]
  rw [hexp_inv] at hresidual
  linarith

/--
Set-function form of the cardinality-constrained greedy approximation theorem.

The `hstep` premise is the standard progress lemma supplied by the greedy
choice plus monotone submodularity: each step closes at least a `1/k` fraction
of the remaining optimality gap.
-/
theorem nemhauser_wolsey_fisher_cardinality_constrained_set_greedy_approximation
    {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ)
    (greedyAtStep : Nat → Finset α)
    (optimalSet : Finset α)
    (k : Nat)
    (_hmonotone : FinsetMonotoneObjective f)
    (_hsubmodular : FinsetSubmodularObjective f)
    (_hoptimal_card : optimalSet.card ≤ k)
    (hk : 0 < k)
    (hstart : f (greedyAtStep 0) = 0)
    (hoptimal_nonneg : 0 ≤ f optimalSet)
    (hstep :
      ∀ i, i < k →
        f optimalSet - f (greedyAtStep (i + 1)) ≤
          (1 - (k : ℝ)⁻¹) * (f optimalSet - f (greedyAtStep i))) :
    (1 - (Real.exp 1)⁻¹) * f optimalSet ≤ f (greedyAtStep k) :=
  nemhauser_wolsey_fisher_cardinality_constrained_greedy_approximation
    k (fun i => f (greedyAtStep i)) (f optimalSet)
    hk hstart hoptimal_nonneg hstep

/--
Full finite-set NWF form from monotonicity, submodularity, and greedy domination
of every remaining optimal element at each step.
-/
theorem nemhauser_wolsey_fisher_cardinality_constrained_set_greedy_approximation_full
    {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ)
    (greedyAtStep : Nat → Finset α)
    (optimalSet : Finset α)
    (k : Nat)
    (hmonotone : FinsetMonotoneObjective f)
    (hsubmodular : FinsetSubmodularObjective f)
    (hoptimal_card : optimalSet.card ≤ k)
    (hk : 0 < k)
    (hstart : f (greedyAtStep 0) = 0)
    (hoptimal_nonneg : 0 ≤ f optimalSet)
    (hcurrent_next :
      ∀ i, i < k → greedyAtStep i ⊆ greedyAtStep (i + 1))
    (hgreedy :
      ∀ i, i < k → ∀ a ∈ optimalSet \ greedyAtStep i,
        FinsetMarginal f (greedyAtStep i) a ≤
          f (greedyAtStep (i + 1)) - f (greedyAtStep i)) :
    (1 - (Real.exp 1)⁻¹) * f optimalSet ≤ f (greedyAtStep k) := by
  apply nemhauser_wolsey_fisher_cardinality_constrained_set_greedy_approximation
    f greedyAtStep optimalSet k hmonotone hsubmodular hoptimal_card
    hk hstart hoptimal_nonneg
  intro i hi
  have hcard :
      (optimalSet \ greedyAtStep i).card ≤ k := by
    exact (Finset.card_le_card
      (by
        intro a ha
        exact (Finset.mem_sdiff.mp ha).1)).trans hoptimal_card
  exact greedy_step_gap_bound_from_submodularity
    f hmonotone hsubmodular
    (greedyAtStep i) (greedyAtStep (i + 1)) optimalSet k
    hcard (hcurrent_next i hi) (hgreedy i hi)

/-! ## Extended Analysis Operations

These operations support concentration inequalities and spectral analysis of
Markov chains, used for quantitative protocol guarantees (mixing times,
convergence rates).
-/

/-- Extended operations for real/complex-analysis touchpoints.

These support:
- **Concentration bounds**: `exponentialTail` for sub-Gaussian tails
- **CLT scaling**: `fluctuationScale` = √n for normalized sums
- **Ergodic averages**: `finiteAverage`, `normalizedCumulative`
- **Spectral analysis**: transition matrix spectrum for mixing time bounds -/
class AnalysisModel where
  /-- Exponential tail bound 2·exp(-t²/2σ²) for sub-Gaussian concentration. -/
  exponentialTail : ℝ → ℝ → ℝ
  /-- Fluctuation scale √n for CLT normalization. -/
  fluctuationScale : Nat → ℝ
  /-- Arithmetic mean of a finite family. -/
  finiteAverage : {n : Nat} → (Fin n → ℝ) → ℝ
  /-- Normalized cumulative sum (∑ᵢ₌₀ᵗ (xᵢ - μ)) / √N. -/
  normalizedCumulative : (Nat → ℝ) → ℝ → Nat → Nat → ℝ
  /-- Lift real transition kernel to complex matrix for spectral analysis. -/
  transitionMatrixComplex :
    {State : Type*} → [Fintype State] → [DecidableEq State] →
      (State → State → ℝ) → Matrix State State ℂ
  /-- Moduli of non-trivial eigenvalues (excluding the Perron eigenvalue 1). -/
  nontrivialSpectrumModuli :
    {State : Type*} → [Fintype State] → [DecidableEq State] →
      (State → State → ℝ) → Set ℝ
  /-- Second-largest eigenvalue modulus (determines mixing rate). -/
  secondSpectrumValue :
    {State : Type*} → [Fintype State] → [DecidableEq State] →
      (State → State → ℝ) → ℝ
  /-- Spectral gap 1 - λ₂ (larger gap = faster mixing). -/
  spectralGapValue :
    {State : Type*} → [Fintype State] → [DecidableEq State] →
      (State → State → ℝ) → ℝ

section AnalysisOperations

variable [AnalysisModel]

/-- Wrapper for the exponential-tail form. -/
def exponentialTail (σ t : ℝ) : ℝ :=
  AnalysisModel.exponentialTail σ t

/-- Wrapper for the fluctuation scale. -/
def fluctuationScale (n : Nat) : ℝ :=
  AnalysisModel.fluctuationScale n

/-- Wrapper for finite averaging. -/
def finiteAverage {n : Nat} (x : Fin n → ℝ) : ℝ :=
  AnalysisModel.finiteAverage x

/-- Wrapper for normalized cumulative process. -/
def normalizedCumulative (x : Nat → ℝ) (μ : ℝ) (N t : Nat) : ℝ :=
  AnalysisModel.normalizedCumulative x μ N t

/-- Wrapper for the complex transition-matrix realization. -/
def transitionMatrixComplex {State : Type*} [Fintype State] [DecidableEq State]
    (kernel : State → State → ℝ) : Matrix State State ℂ :=
  AnalysisModel.transitionMatrixComplex kernel

/-- Wrapper for nontrivial spectrum moduli. -/
def nontrivialSpectrumModuli {State : Type*} [Fintype State] [DecidableEq State]
    (kernel : State → State → ℝ) : Set ℝ :=
  AnalysisModel.nontrivialSpectrumModuli kernel

/-- Wrapper for the second spectral value. -/
def secondSpectrumValue {State : Type*} [Fintype State] [DecidableEq State]
    (kernel : State → State → ℝ) : ℝ :=
  AnalysisModel.secondSpectrumValue kernel

/-- Wrapper for the spectral-gap value. -/
def spectralGapValue {State : Type*} [Fintype State] [DecidableEq State]
    (kernel : State → State → ℝ) : ℝ :=
  AnalysisModel.spectralGapValue kernel

end AnalysisOperations

/-! ## Extended Analysis Laws

Laws for the extended analysis interface. These ensure the concrete
implementations behave as expected for concentration and spectral arguments.
-/

/-- Laws for `AnalysisModel` ensuring semantic correctness.

These laws capture:
- Basic properties of exponential/Gaussian tails
- √n scaling for CLT normalization
- Permutation invariance of averages (exchangeability)
- Spectral gap definition consistency -/
class AnalysisLaws extends AnalysisModel where
  /-- Exponential tails are nonnegative (probability bound). -/
  exponential_tail_nonneg :
    ∀ (σ t : ℝ), 0 ≤ toAnalysisModel.exponentialTail σ t
  /-- At zero threshold, tail probability is 2 (two-sided bound covers all). -/
  exponential_tail_zero :
    ∀ (σ : ℝ), toAnalysisModel.exponentialTail σ 0 = 2
  /-- Fluctuation scale is positive for positive sample size. -/
  fluctuation_scale_pos :
    ∀ {n : Nat}, 0 < n → 0 < toAnalysisModel.fluctuationScale n
  /-- Fluctuation scale squared equals sample size (√n property). -/
  fluctuation_scale_sq :
    ∀ (n : Nat), (toAnalysisModel.fluctuationScale n) ^ 2 = n
  /-- Finite averages are permutation-invariant (exchangeability). -/
  finite_average_perm :
    ∀ {n : Nat}, (σ : Equiv.Perm (Fin n)) → (x : Fin n → ℝ) →
      toAnalysisModel.finiteAverage (fun i => x (σ i)) =
      toAnalysisModel.finiteAverage x
  /-- Average of a constant family is that constant. -/
  finite_average_const :
    ∀ {n : Nat}, (c : ℝ) → n ≠ 0 →
      toAnalysisModel.finiteAverage (fun _ : Fin n => c) = c
  /-- Centered constant sequence has zero cumulative fluctuation. -/
  normalized_cumulative_const_zero :
    ∀ (c : ℝ) (N t : Nat), N ≠ 0 →
      toAnalysisModel.normalizedCumulative (fun _ => c) c N t = 0
  /-- Spectral gap is 1 minus the second eigenvalue modulus. This is a
  *definitional* bookkeeping law (the concrete model defines the gap this way);
  it carries no spectral-theoretic content. -/
  spectral_gap_eq :
    ∀ {State : Type*} [Fintype State] [DecidableEq State]
      (kernel : State → State → ℝ),
      toAnalysisModel.spectralGapValue kernel =
      1 - toAnalysisModel.secondSpectrumValue kernel

/-! ## Extended Analysis Laws: Exported Theorems -/

section AnalysisLaws

variable [AnalysisLaws]

/-- Re-export nonnegativity of the exponential-tail form. -/
theorem exponential_tail_nonneg (σ t : ℝ) : 0 ≤ exponentialTail σ t :=
  AnalysisLaws.exponential_tail_nonneg (self := inferInstance) σ t

/-- Re-export normalization at zero threshold for the exponential-tail form. -/
theorem exponential_tail_zero (σ : ℝ) : exponentialTail σ 0 = 2 :=
  AnalysisLaws.exponential_tail_zero (self := inferInstance) σ

/-- Re-export positivity of fluctuation scale for positive index. -/
theorem fluctuation_scale_pos {n : Nat} (hn : 0 < n) :
    0 < fluctuationScale n :=
  AnalysisLaws.fluctuation_scale_pos (self := inferInstance) hn

/-- Re-export squared-scale identity. -/
theorem fluctuation_scale_sq (n : Nat) :
    (fluctuationScale n) ^ 2 = n :=
  AnalysisLaws.fluctuation_scale_sq (self := inferInstance) n

/-- Re-export permutation invariance of finite averages. -/
theorem finite_average_perm {n : Nat} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    finiteAverage (fun i => x (σ i)) = finiteAverage x :=
  AnalysisLaws.finite_average_perm (self := inferInstance) σ x

/-- Re-export constant-family identity for finite averages. -/
theorem finite_average_const {n : Nat} (c : ℝ) (hn : n ≠ 0) :
    finiteAverage (fun _ : Fin n => c) = c :=
  AnalysisLaws.finite_average_const (self := inferInstance) c hn

/-- Re-export zero fluctuation for centered constant cumulative process. -/
theorem normalized_cumulative_const_zero (c : ℝ) (N t : Nat) (hN : N ≠ 0) :
    normalizedCumulative (fun _ => c) c N t = 0 :=
  AnalysisLaws.normalized_cumulative_const_zero (self := inferInstance) c N t hN

/-- Re-export of the definitional identity `gap = 1 - second spectral value`
(true by definition in the concrete model; no spectral theorem is involved). -/
theorem spectral_gap_eq {State : Type*} [Fintype State] [DecidableEq State]
    (kernel : State → State → ℝ) :
    spectralGapValue kernel = 1 - secondSpectrumValue kernel :=
  AnalysisLaws.spectral_gap_eq (self := inferInstance) kernel

end AnalysisLaws

end EntropyAPI
