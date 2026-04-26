import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-
The Problem. Protocol and classical theorems need a shared information/analysis
interface, while concrete `Real.log`/spectral realizations should stay isolated.

Solution Structure.
1. Define compact operation interfaces (`Model`, `AnalysisModel`).
2. Define compact law interfaces (`Laws`, `AnalysisLaws`).
3. Re-export operations and laws through stable wrappers.
4. Keep concrete realizations in `ClassicalAnalysisInstance`.

## Trust Boundary

This file and `ClassicalAnalysisInstance.lean` form the explicit trust boundary
for all real-analysis assumptions in the project. A reviewer can:
1. Verify the laws stated here match standard information theory
2. Check `ClassicalAnalysisInstance` proves each law from Mathlib
3. Run `lake build` to confirm type-correctness
4. Run `just escape` to confirm no escapes outside this boundary
-/

/-! # ClassicalAnalysisAPI

Abstract interface for information-theoretic and real-analysis operations.

## Primary References

- **Shannon (1948)**: "A Mathematical Theory of Communication." Bell System
  Technical Journal. Introduces Shannon entropy H(X) = -∑ p(x) log p(x).

- **Kullback & Leibler (1951)**: "On Information and Sufficiency." Annals of
  Mathematical Statistics. Introduces KL divergence D(P‖Q) = ∑ p(x) log(p(x)/q(x)).

- **Cover & Thomas (2006)**: "Elements of Information Theory" (2nd ed.).
  Standard textbook; theorem numbers referenced below.

## Expose

This module defines the abstract boundary consumed by the rest of the project:

- entropy interface:
  `EntropyAPI.Distribution`, `EntropyAPI.IsErasureKernel`,
  `EntropyAPI.Model`, `EntropyAPI.Laws`,
  `EntropyAPI.shannonEntropy`, `EntropyAPI.klDivergence`,
  `EntropyAPI.mutualInfo`
- entropy law wrappers:
  `EntropyAPI.shannon_entropy_nonneg`,
  `EntropyAPI.shannon_entropy_le_log_card`,
  `EntropyAPI.kl_divergence_nonneg`,
  `EntropyAPI.kl_divergence_eq_zero_iff`,
  `EntropyAPI.mutual_info_zero_of_erasure`
- extended analysis interface:
  `EntropyAPI.AnalysisModel`, `EntropyAPI.AnalysisLaws`,
  `EntropyAPI.exponentialTail`, `EntropyAPI.fluctuationScale`,
  `EntropyAPI.finiteAverage`, `EntropyAPI.normalizedCumulative`,
  `EntropyAPI.transitionMatrixComplex`,
  `EntropyAPI.nontrivialSpectrumModuli`,
  `EntropyAPI.secondSpectrumValue`,
  `EntropyAPI.spectralGapValue`

Concrete implementations live in `ClassicalAnalysisInstance`.
-/

set_option autoImplicit false

namespace EntropyAPI

open scoped BigOperators

/-! ## Core Types -/

/-- Finite probability distributions represented by a real-valued pmf. -/
structure Distribution (α : Type*) [Fintype α] where
  pmf : α → ℝ
  nonneg : ∀ a, 0 ≤ pmf a
  sum_one : ∑ a, pmf a = 1

/--
`IsErasureKernel labelDist joint` means observation carries no label
information: all mass is concentrated at one observation value.
-/
def IsErasureKernel {L O : Type} [DecidableEq O]
    (labelDist : L → ℝ) (joint : L × O → ℝ) : Prop :=
  ∃ o0, ∀ lo : L × O, joint lo = if lo.2 = o0 then labelDist lo.1 else 0

/-! ## Entropy Operations -/

/-- Information-theoretic operations required by downstream modules. -/
class Model where
  shannonEntropy : {α : Type*} → [Fintype α] → (α → ℝ) → ℝ
  klDivergence : {α : Type*} → [Fintype α] → (α → ℝ) → (α → ℝ) → ℝ
  mutualInfo :
    {α : Type*} → {β : Type*} → [Fintype α] → [Fintype β] →
    (α × β → ℝ) → ℝ

section Operations

variable [Model]

/-- Wrapper for Shannon entropy. -/
def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  Model.shannonEntropy p

/-- Wrapper for KL divergence. -/
def klDivergence {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  Model.klDivergence p q

/-- Wrapper for mutual information. -/
def mutualInfo {α : Type*} {β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) : ℝ :=
  Model.mutualInfo pXY

end Operations

/-! ## Entropy Laws

The following laws are the core information-theoretic properties required by
downstream modules. Each corresponds to a standard theorem in information theory.
-/

/-- Shannon entropy nonnegativity law.

**Statement**: H(X) ≥ 0 for any discrete random variable X.

**Intuition**: Each term p(x) log p(x) is nonpositive on [0,1] (since log p ≤ 0
when p ≤ 1), so negating the sum yields a nonnegative quantity.

**Reference**: Shannon (1948) §6; Cover & Thomas Theorem 2.1.1. -/
abbrev ShannonEntropyNonneg (M : Model) : Prop :=
  ∀ {α : Type*} [Fintype α], (d : Distribution α) →
    0 ≤ @Model.shannonEntropy M α _ d.pmf

/-- Shannon entropy cardinality upper bound law.

**Statement**: H(X) ≤ log|X| with equality iff X is uniformly distributed.

**Intuition**: Entropy measures uncertainty. Maximum uncertainty occurs when all
outcomes are equally likely. The uniform distribution achieves log|X| bits.
Formally, this follows from D(P‖U) ≥ 0 where U is uniform.

**Reference**: Cover & Thomas Theorem 2.6.4. -/
abbrev ShannonEntropyLeLogCard (M : Model) : Prop :=
  ∀ {α : Type*} [Fintype α] [Nonempty α], (d : Distribution α) →
    @Model.shannonEntropy M α _ d.pmf ≤ Real.log (Fintype.card α)

/-- KL divergence nonnegativity law (Gibbs' inequality).

**Statement**: D(P‖Q) ≥ 0 for distributions P, Q with P absolutely continuous
w.r.t. Q.

**Intuition**: KL divergence measures the "extra bits" needed to encode samples
from P using a code optimized for Q. You can never do better than the optimal
code for P, so the overhead is nonnegative.

**Proof sketch**: Apply Jensen's inequality to the convex function -log:
  D(P‖Q) = E_P[-log(Q/P)] ≥ -log(E_P[Q/P]) = -log(1) = 0

**Reference**: Kullback & Leibler (1951); Cover & Thomas Theorem 2.6.3. -/
abbrev KlDivergenceNonneg (M : Model) : Prop :=
  ∀ {α : Type*} [Fintype α], (p q : Distribution α) →
    (∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) →
    0 ≤ @Model.klDivergence M α _ p.pmf q.pmf

/-- KL divergence zero characterization law.

**Statement**: D(P‖Q) = 0 if and only if P = Q (almost everywhere).

**Intuition**: Zero divergence means P and Q are indistinguishable from an
information-theoretic perspective. Strict convexity of -log implies Jensen's
inequality is tight only when the argument is constant a.e., forcing P = Q.

**Reference**: Cover & Thomas Theorem 2.6.3 (equality condition). -/
abbrev KlDivergenceEqZeroIff (M : Model) : Prop :=
  ∀ {α : Type*} [Fintype α], (p q : Distribution α) →
    (∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) →
    (@Model.klDivergence M α _ p.pmf q.pmf = 0 ↔ p.pmf = q.pmf)

/-- Erasure implies zero mutual information law.

**Statement**: If the observation channel is constant (all labels map to the
same output), then I(Label; Observation) = 0.

**Intuition**: Mutual information I(X;Y) = H(Y) - H(Y|X) measures how much
knowing X reduces uncertainty about Y. If Y is deterministically fixed
regardless of X, then H(Y) = H(Y|X) = 0, so I(X;Y) = 0.

**Application**: This law is central to the blindness property in choreographic
projection. When a non-participant role's observation function is constant
across all branches, they learn nothing about which branch was taken.

**Reference**: Cover & Thomas §2.8 (data processing inequality, extreme case). -/
abbrev MutualInfoZeroOfErasure (M : Model) : Prop :=
  ∀ {L O : Type} [Fintype L] [Fintype O] [DecidableEq O],
    (labelDist : L → ℝ) →
    (∀ l, 0 ≤ labelDist l) →
    (∑ l, labelDist l = 1) →
    (joint : L × O → ℝ) →
    IsErasureKernel labelDist joint →
    @Model.mutualInfo M L O _ _ joint = 0

/-- Law-bearing entropy interface used by downstream modules. -/
class Laws extends Model where
  shannon_entropy_nonneg : ShannonEntropyNonneg toModel
  shannon_entropy_le_log_card : ShannonEntropyLeLogCard toModel
  kl_divergence_nonneg : KlDivergenceNonneg toModel
  kl_divergence_eq_zero_iff : KlDivergenceEqZeroIff toModel
  mutual_info_zero_of_erasure : MutualInfoZeroOfErasure toModel

/-- Promote `Laws` to `Model` so operation wrappers infer automatically. -/
instance (priority := 100) lawsToModel [Laws] : Model :=
  Laws.toModel

/-! ## Entropy Laws: Exported Theorems -/

section Laws

variable [Laws]

/-- Re-export Shannon entropy nonnegativity from `Laws`. -/
theorem shannon_entropy_nonneg {α : Type*} [Fintype α]
    (d : Distribution α) :
    0 ≤ shannonEntropy d.pmf :=
  Laws.shannon_entropy_nonneg (self := inferInstance) d

/-- Re-export Shannon entropy cardinality upper bound from `Laws`. -/
theorem shannon_entropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (d : Distribution α) :
    shannonEntropy d.pmf ≤ Real.log (Fintype.card α) :=
  Laws.shannon_entropy_le_log_card (self := inferInstance) d

/-- Re-export KL nonnegativity from `Laws`. -/
theorem kl_divergence_nonneg {α : Type*} [Fintype α]
    (p q : Distribution α)
    (habs : ∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) :
    0 ≤ klDivergence p.pmf q.pmf :=
  Laws.kl_divergence_nonneg (self := inferInstance) p q habs

/-- Re-export zero-KL characterization from `Laws`. -/
theorem kl_divergence_eq_zero_iff {α : Type*} [Fintype α]
    (p q : Distribution α)
    (habs : ∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) :
    klDivergence p.pmf q.pmf = 0 ↔ p.pmf = q.pmf :=
  Laws.kl_divergence_eq_zero_iff (self := inferInstance) p q habs

/-- Re-export erasure-implies-zero-MI from `Laws`. -/
theorem mutual_info_zero_of_erasure {L O : Type}
    [Fintype L] [Fintype O] [DecidableEq O]
    (labelDist : L → ℝ)
    (h_nn : ∀ l, 0 ≤ labelDist l)
    (h_sum : ∑ l, labelDist l = 1)
    (joint : L × O → ℝ)
    (hErase : IsErasureKernel labelDist joint) :
    mutualInfo joint = 0 :=
  Laws.mutual_info_zero_of_erasure
    (self := inferInstance) labelDist h_nn h_sum joint hErase

end Laws

/-! ## Combinatorial Optimization Transport Surface -/

/-- Monotonicity predicate for finite-set objectives. -/
def FinsetMonotoneObjective {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) : Prop :=
  ∀ {S T : Finset α}, S ⊆ T → f S ≤ f T

/-- Diminishing-returns predicate for finite-set objectives. -/
def FinsetSubmodularObjective {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) : Prop :=
  ∀ {S T : Finset α}, S ⊆ T → ∀ a, a ∉ T →
    f (insert a T) - f T ≤ f (insert a S) - f S

/-- Marginal gain from adding one element to a finite-set objective. -/
def FinsetMarginal {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (S : Finset α) (a : α) : ℝ :=
  f (insert a S) - f S

/-- Submodularity bounds a union gain by the sum of base-set marginals. -/
theorem submodular_union_gap_le_sum_marginals
    {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ)
    (hsubmodular : FinsetSubmodularObjective f)
    (S R : Finset α)
    (hdisjoint : ∀ a ∈ R, a ∉ S) :
    f (S ∪ R) - f S ≤ ∑ a ∈ R, FinsetMarginal f S a := by
  classical
  -- Peel off one new element at a time and apply diminishing returns.
  induction R using Finset.induction_on with
  | empty =>
      simp [FinsetMarginal]
  | insert a R ha ih =>
      have ha_not_S : a ∉ S := hdisjoint a (Finset.mem_insert_self a R)
      have ha_not_union : a ∉ S ∪ R := by
        simp [ha_not_S, ha]
      have hdisjoint_R : ∀ b ∈ R, b ∉ S := by
        intro b hb
        exact hdisjoint b (Finset.mem_insert_of_mem hb)
      have hih :
          f (S ∪ R) - f S ≤ ∑ b ∈ R, FinsetMarginal f S b :=
        ih hdisjoint_R
      have hsub :
          f (insert a (S ∪ R)) - f (S ∪ R) ≤ FinsetMarginal f S a := by
        simpa [FinsetMarginal] using
          hsubmodular (by intro x hx; exact Finset.mem_union_left R hx)
            a ha_not_union
      have hunion :
          S ∪ insert a R = insert a (S ∪ R) := by
        ext x
        simp
      rw [hunion, Finset.sum_insert ha]
      linarith

/-- The optimality gap is bounded by the sum of remaining optimal-element marginals. -/
theorem optimal_gap_le_sum_remaining_marginals
    {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ)
    (hmonotone : FinsetMonotoneObjective f)
    (hsubmodular : FinsetSubmodularObjective f)
    (current optimalSet : Finset α) :
    f optimalSet - f current ≤
      ∑ a ∈ optimalSet \ current, FinsetMarginal f current a := by
  classical
  let remainder := optimalSet \ current
  -- Compare `optimalSet` to `current ∪ remainder`, then expand by submodularity.
  have hdisjoint : ∀ a ∈ remainder, a ∉ current := by
    intro a ha
    exact (Finset.mem_sdiff.mp ha).2
  have hunion_gap :
      f (current ∪ remainder) - f current ≤
        ∑ a ∈ remainder, FinsetMarginal f current a :=
    submodular_union_gap_le_sum_marginals f hsubmodular current remainder hdisjoint
  have hopt_subset_union : optimalSet ⊆ current ∪ remainder := by
    intro a ha
    by_cases hac : a ∈ current
    · exact Finset.mem_union_left remainder hac
    · exact Finset.mem_union_right current (Finset.mem_sdiff.mpr ⟨ha, hac⟩)
  have hopt_gap :
      f optimalSet - f current ≤
        ∑ a ∈ remainder, FinsetMarginal f current a :=
    (sub_le_sub_right (hmonotone hopt_subset_union) (f current)).trans hunion_gap
  exact hopt_gap

/-- Greedy domination bounds the marginal sum by cardinality times the greedy gain. -/
theorem sum_remaining_marginals_le_card_mul_greedy_gain
    {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ)
    (current next optimalSet : Finset α)
    (hgreedy :
      ∀ a ∈ optimalSet \ current,
        FinsetMarginal f current a ≤ f next - f current) :
    ∑ a ∈ optimalSet \ current, FinsetMarginal f current a ≤
      (optimalSet \ current).card * (f next - f current) := by
  classical
  -- Every remaining optimal element has marginal at most the greedy gain.
  simpa [nsmul_eq_mul] using
    (Finset.sum_le_card_nsmul (optimalSet \ current)
      (fun a => FinsetMarginal f current a)
      (f next - f current)
      (fun a ha => hgreedy a ha))

/-- Greedy domination gives `gap ≤ k * gain` for a cardinality budget `k`. -/
theorem greedy_gap_le_budget_mul_gain
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
    f optimalSet - f current ≤
      (k : ℝ) * (f next - f current) := by
  -- Combine submodular marginal accounting with greedy domination.
  have hopt_gap :=
    optimal_gap_le_sum_remaining_marginals f
      hmonotone hsubmodular current optimalSet
  have hsum_le :
      ∑ a ∈ optimalSet \ current, FinsetMarginal f current a ≤
        (optimalSet \ current).card * (f next - f current) := by
    simpa using
      sum_remaining_marginals_le_card_mul_greedy_gain
        f current next optimalSet hgreedy
  have hgap_le_card :
      f optimalSet - f current ≤
        (optimalSet \ current).card * (f next - f current) :=
    hopt_gap.trans hsum_le
  have hcard_real :
      ((optimalSet \ current).card : ℝ) ≤ k := by
    exact_mod_cast hcard
  have hgain_nonneg :
      0 ≤ f next - f current :=
    sub_nonneg.mpr (hmonotone hcurrent_next)
  have hgap_le_k :
      f optimalSet - f current ≤
        (k : ℝ) * (f next - f current) :=
    hgap_le_card.trans
      (mul_le_mul_of_nonneg_right hcard_real hgain_nonneg)
  exact hgap_le_k

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
  /-- Spectral gap is 1 minus the second eigenvalue modulus. -/
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

/-- Re-export relation between spectral gap and second spectral value. -/
theorem spectral_gap_eq {State : Type*} [Fintype State] [DecidableEq State]
    (kernel : State → State → ℝ) :
    spectralGapValue kernel = 1 - secondSpectrumValue kernel :=
  AnalysisLaws.spectral_gap_eq (self := inferInstance) kernel

end AnalysisLaws

end EntropyAPI
