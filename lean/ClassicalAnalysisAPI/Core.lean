import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-! # ClassicalAnalysisAPI.CorennCore entropy API types, operations, entropy laws, and the first half of the combinatorial optimization transport surface. Re-exported by `ClassicalAnalysisAPI`. -/

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

end EntropyAPI
