import Mathlib
import ClassicalAnalysisAPI

/-
The Problem. `ClassicalAnalysisAPI` exposes abstract operations/laws, but the
project also needs one concrete real-analysis model.

Solution Structure.
1. Define concrete entropy/KL/mutual-information operations.
2. Prove the API law obligations for those operations.
3. Package them into `realLaws` and `realAnalysisLaws`.

## Trust Boundary

This file provides the concrete noncomputable realizations of the abstract
`ClassicalAnalysisAPI` interface. Together with `ClassicalAnalysisAPI.lean`,
it forms the explicit trust boundary for real-analysis assumptions.

**Why noncomputable?** Real.log is defined via limits/integrals in Mathlib's
classical real analysis. Computing logarithms to arbitrary precision requires
infinite operations, so the kernel cannot evaluate these terms. The laws
themselves are fully proved — noncomputability only means we cannot *execute*
entropy calculations within Lean, but we can still *reason* about them.

**Audit note**: All laws are proved from Mathlib foundations. No axioms or
open proof gaps in this file. Run `lake build` and `just escape`
to verify.
-/

/-! # ClassicalAnalysisInstance

Concrete real-valued realizations of the `ClassicalAnalysisAPI` interface.

## Expose

Concrete realizations consumed by downstream modules:

- entropy instance:
  `EntropyAPI.realModel`, `EntropyAPI.realLaws`
- extended analysis instance:
  `EntropyAPI.realAnalysisModel`, `EntropyAPI.realAnalysisLaws`

Everything in this file is an implementation detail except those exported
instances and definitions.

## Mathematical References

All implementations follow standard definitions from Cover & Thomas (2006):
- Shannon entropy: Definition 2.1, H(X) = -∑ p(x) log p(x)
- KL divergence: Definition 2.23, D(P‖Q) = ∑ p(x) log(p(x)/q(x))
- Mutual information: Definition 2.24, I(X;Y) = D(P_{XY} ‖ P_X × P_Y)
-/

set_option autoImplicit false

namespace EntropyAPI

open scoped BigOperators Classical

noncomputable section

namespace RealConcrete

/-! ## Core Information Operations

Standard definitions following Cover & Thomas (2006). The 0·log(0) = 0
convention is used throughout, consistent with the limit lim_{x→0⁺} x log x = 0.
-/

/-- Shannon entropy with the 0·log(0) = 0 convention.

H(X) = -∑ₓ p(x) log p(x)

The negative sign ensures H ≥ 0 since log p(x) ≤ 0 for p(x) ∈ [0,1].

**Reference**: Cover & Thomas Definition 2.1. -/
def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ a, if p a = 0 then 0 else p a * Real.log (p a)

/-- KL divergence (relative entropy) with the 0·log(0) = 0 convention.

D(P‖Q) = ∑ₓ p(x) log(p(x)/q(x))

Measures the expected log-likelihood ratio, or equivalently, the extra bits
needed to encode samples from P using a code optimized for Q.

**Reference**: Cover & Thomas Definition 2.23; Kullback & Leibler (1951). -/
def klDivergence {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, if p a = 0 then 0 else p a * Real.log (p a / q a)

/-- First marginal: P_X(x) = ∑_y P_{XY}(x,y). -/
def marginalFst {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, pXY (a, b)

/-- Second marginal: P_Y(y) = ∑_x P_{XY}(x,y). -/
def marginalSnd {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, pXY (a, b)

/-- Mutual information as KL divergence from joint to product of marginals.

I(X;Y) = D(P_{XY} ‖ P_X × P_Y) = ∑_{x,y} p(x,y) log(p(x,y) / (p(x)p(y)))

Measures the information shared between X and Y. Equivalently:
I(X;Y) = H(X) + H(Y) - H(X,Y) = H(X) - H(X|Y) = H(Y) - H(Y|X)

**Reference**: Cover & Thomas Definition 2.24. -/
def mutualInfo {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : ℝ :=
  klDivergence pXY (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2)

/-! ## KL and Entropy Laws

Proofs of the information-theoretic laws from `ClassicalAnalysisAPI`. Each
proof follows the standard argument from Cover & Thomas (2006).
-/

/-- Shannon entropy is nonnegative for distributions.

**Proof strategy**: Each term p(a)·log(p(a)) is nonpositive on [0,1] because:
- When p(a) = 0: the term is 0 by convention
- When 0 < p(a) ≤ 1: log(p(a)) ≤ 0, so p(a)·log(p(a)) ≤ 0

Negating the sum of nonpositive terms yields a nonnegative result.

**Reference**: Cover & Thomas Theorem 2.1.1. -/
theorem shannonEntropy_nonneg {α : Type*} [Fintype α]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    0 ≤ shannonEntropy p := by
  -- Each term `p(a) * log p(a)` is nonpositive on `[0, 1]`, so the negated sum is nonnegative.
  classical
  unfold shannonEntropy
  have hterm : ∀ a, (if p a = 0 then 0 else p a * Real.log (p a)) ≤ 0 := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    · have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
      have hpa_le_one : p a ≤ 1 := by
        have hle : p a ≤ ∑ b, p b := by
          have hmem : a ∈ (Finset.univ : Finset α) := by simp
          exact Finset.single_le_sum (f := p) (fun _ _ => hp_nn _) hmem
        simpa [hp_sum] using hle
      have hlog : Real.log (p a) ≤ 0 := by
        have hlog' : Real.log (p a) ≤ Real.log 1 :=
          Real.log_le_log hpa_pos (by simpa using hpa_le_one)
        simpa using hlog'
      have hmul : p a * Real.log (p a) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hp_nn a) hlog
      simpa [hpa] using hmul
  have hsum : ∑ a, (if p a = 0 then 0 else p a * Real.log (p a)) ≤ 0 := by
    simpa using
      (Finset.sum_nonpos (s := (Finset.univ : Finset α)) (fun a _ => hterm a))
  linarith

/-- KL divergence is nonnegative (Gibbs' inequality).

**Proof strategy**: Use the fundamental inequality log(x) ≤ x - 1 (with
equality iff x = 1). Apply this to q(a)/p(a) for each a, multiply by -p(a),
then sum over a:

  ∑ₐ p(a) log(p(a)/q(a)) ≥ ∑ₐ p(a)(1 - q(a)/p(a)) = ∑ₐ(p(a) - q(a)) = 1 - 1 = 0

**Reference**: Cover & Thomas Theorem 2.6.3; Kullback & Leibler (1951). -/
theorem klDivergence_nonneg {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    0 ≤ klDivergence p q := by
  -- Use `log x ≤ x - 1` pointwise, then sum and simplify masses to 1.
  classical
  have hterm : ∀ a, p a - q a ≤ (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
    intro a
    by_cases hpa : p a = 0
    · have hq : 0 ≤ q a := hq_nn a
      simp [hpa, hq]
    · have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
      have hq_pos : 0 < q a := lt_of_le_of_ne (hq_nn a) (Ne.symm (habs a hpa))
      have hlog : Real.log (q a / p a) ≤ q a / p a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hq_pos hpa_pos)
      have hmul : -p a * Real.log (q a / p a) ≥ -p a * (q a / p a - 1) := by
        have hpneg : -p a ≤ 0 := by linarith [hp_nn a]
        exact mul_le_mul_of_nonpos_left hlog hpneg
      have hleft : -p a * Real.log (q a / p a) = p a * Real.log (p a / q a) := by
        have hlog1 : Real.log (q a / p a) = Real.log (q a) - Real.log (p a) :=
          Real.log_div (habs a hpa) hpa
        have hlog2 : Real.log (p a / q a) = Real.log (p a) - Real.log (q a) :=
          Real.log_div hpa (habs a hpa)
        calc
          -p a * Real.log (q a / p a)
              = -p a * (Real.log (q a) - Real.log (p a)) := by simp [hlog1]
          _ = p a * (Real.log (p a) - Real.log (q a)) := by ring
          _ = p a * Real.log (p a / q a) := by simp [hlog2]
      have hright : -p a * (q a / p a - 1) = p a - q a := by
        calc
          -p a * (q a / p a - 1) = -p a * (q a / p a) + p a := by ring
          _ = -(p a * (q a / p a)) + p a := by ring
          _ = -q a + p a := by field_simp [hpa]
          _ = p a - q a := by ring
      have hineq : p a - q a ≤ p a * Real.log (p a / q a) := by
        have := hmul
        simpa [hleft, hright] using this
      simpa [hpa] using hineq
  have hsum : ∑ a, (p a - q a) ≤ ∑ a, (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
    exact Finset.sum_le_sum (fun a _ => hterm a)
  have hsum_pq : ∑ a, (p a - q a) = 0 := by
    simp [hp_sum, hq_sum]
  have : 0 ≤ ∑ a, (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
    linarith [hsum, hsum_pq]
  simpa [klDivergence] using this

/-- KL to uniform equals `log |α| - H(p)`. -/
private theorem kl_uniform_eq {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (_hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    klDivergence p (fun _ => 1 / Fintype.card α) =
      Real.log (Fintype.card α) - shannonEntropy p := by
  -- Expand definitions and use `log (p / (1/n)) = log p + log n` on nonzero terms.
  unfold klDivergence shannonEntropy
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [sub_neg_eq_add]
  have hterms : ∀ a, (if p a = 0 then 0 else p a * Real.log (p a / (1 / ↑(Fintype.card α)))) =
      (if p a = 0 then 0 else p a * Real.log (p a)) +
      p a * Real.log (Fintype.card α) := by
    intro a
    by_cases hp : p a = 0
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      rw [div_div_eq_mul_div, div_one,
        Real.log_mul hp (ne_of_gt hcard)]
      ring
  simp_rw [hterms]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp_sum, one_mul, add_comm]

/-- Shannon entropy is bounded by `log |α|`. -/
theorem shannonEntropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card α) := by
  -- Reduce to nonnegativity of KL divergence against the uniform distribution.
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hunif_nn : ∀ a : α, (0 : ℝ) ≤ 1 / Fintype.card α :=
    fun _ => div_nonneg zero_le_one (le_of_lt hcard)
  have hunif_sum : ∑ _ : α, (1 : ℝ) / Fintype.card α = 1 := by
    simp [Finset.card_univ]
  have habs : ∀ a : α, p a ≠ 0 → (1 : ℝ) / Fintype.card α ≠ 0 :=
    fun _ _ => ne_of_gt (div_pos one_pos hcard)
  have hkl := klDivergence_nonneg p _ hp_nn hp_sum hunif_nn hunif_sum habs
  rw [kl_uniform_eq p hp_nn hp_sum] at hkl
  linarith

/-- KL divergence of a distribution with itself is zero. -/
private theorem klDivergence_self_eq_zero {α : Type*} [Fintype α]
    (p : α → ℝ) (_hp_nn : ∀ a, 0 ≤ p a) :
    klDivergence p p = 0 := by
  -- Every term is either zero-by-branch or `p * log 1`.
  classical
  unfold klDivergence
  refine Finset.sum_eq_zero ?_
  intro a _
  by_cases hpa : p a = 0
  · simp [hpa]
  · simp [hpa]

/-- Pointwise KL lower bound by linear difference. -/
private theorem kl_term_ge_diff {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hq_nn : ∀ a, 0 ≤ q a)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) (a : α) :
    p a - q a ≤ (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
  -- Same `log x ≤ x - 1` rearrangement used in the global nonnegativity proof.
  classical
  by_cases hpa : p a = 0
  · simp [hpa, hq_nn a]
  · have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
    have hq_pos : 0 < q a := lt_of_le_of_ne (hq_nn a) (Ne.symm (habs a hpa))
    have hlog : Real.log (q a / p a) ≤ q a / p a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hq_pos hpa_pos)
    have hmul : -p a * Real.log (q a / p a) ≥ p a - q a := by
      have hrhs : -p a * (q a / p a - 1) = p a - q a := by field_simp; ring
      linarith [mul_le_mul_of_nonpos_left hlog (by linarith : -p a ≤ 0)]
    have hflip : -p a * Real.log (q a / p a) = p a * Real.log (p a / q a) := by
      rw [Real.log_div (habs a hpa) hpa, Real.log_div hpa (habs a hpa)]
      ring
    simp only [hpa, ↓reduceIte]
    linarith

/-- If KL is zero, each term matches its linear lower bound. -/
private theorem kl_term_eq_diff_of_zero {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hkl : klDivergence p q = 0) (a : α) :
    (if p a = 0 then 0 else p a * Real.log (p a / q a)) = p a - q a := by
  -- Sum of nonnegative differences is zero, so each difference is zero.
  classical
  have hkl' : ∑ b, (if p b = 0 then 0 else p b * Real.log (p b / q b)) = 0 := by
    simpa [klDivergence] using hkl
  have hpq : ∑ b, (p b - q b) = 0 := by
    have : ∑ b, p b - ∑ b, q b = 0 := by rw [hp_sum, hq_sum]; ring
    linarith [Finset.sum_sub_distrib (f := p) (g := q) (s := Finset.univ)]
  have hdiff :
      ∑ b, ((if p b = 0 then 0 else p b * Real.log (p b / q b)) - (p b - q b)) = 0 := by
    linarith [Finset.sum_sub_distrib
      (f := fun b => if p b = 0 then 0 else p b * Real.log (p b / q b))
      (g := fun b => p b - q b) (s := Finset.univ)]
  have hnn : ∀ b, 0 ≤
      (if p b = 0 then 0 else p b * Real.log (p b / q b)) - (p b - q b) :=
    fun b => by linarith [kl_term_ge_diff p q hp_nn hq_nn habs b]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn b)).mp hdiff
  linarith [hzero a (Finset.mem_univ a)]

/-- Zero KL divergence implies pointwise equality. -/
private theorem klDivergence_eq_zero_imp_eq {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hkl : klDivergence p q = 0) : p = q := by
  -- Characterize each term at equality and force each ratio to 1.
  classical
  funext a
  have hterm := kl_term_eq_diff_of_zero p q hp_nn hp_sum hq_nn hq_sum habs hkl a
  by_cases hpa : p a = 0
  · simp [hpa] at hterm
    linarith
  · have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
    have hq_pos : 0 < q a := lt_of_le_of_ne (hq_nn a) (Ne.symm (habs a hpa))
    simp only [hpa, ↓reduceIte] at hterm
    have hlog_pq : Real.log (p a / q a) = 1 - q a / p a := by
      have h := div_eq_div_iff (ne_of_gt hpa_pos) (ne_of_gt hpa_pos) |>.mpr (by linarith)
      field_simp at hterm ⊢
      linarith
    have hlog_qp : Real.log (q a / p a) = q a / p a - 1 := by
      rw [Real.log_div hpa (habs a hpa)] at hlog_pq
      rw [Real.log_div (habs a hpa) hpa]
      linarith
    have hqp : q a / p a = 1 := by
      by_contra hne
      exact absurd hlog_qp
        (ne_of_lt (Real.log_lt_sub_one_of_pos (div_pos hq_pos hpa_pos) hne))
    rw [div_eq_one_iff_eq (ne_of_gt hpa_pos)] at hqp
    linarith

/-- KL divergence vanishes iff the two distributions are pointwise equal. -/
theorem klDivergence_eq_zero_iff {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    klDivergence p q = 0 ↔ p = q := by
  constructor
  · exact klDivergence_eq_zero_imp_eq p q hp_nn hp_sum hq_nn hq_sum habs
  · intro heq
    subst heq
    exact klDivergence_self_eq_zero p hp_nn

/-! ## Erasure Law

The erasure law states that constant observation channels carry zero information.
This is the information-theoretic foundation for the **blindness property** in
choreographic projection: non-participant roles learn nothing about branch choices.

**Key insight**: When P(O|L) = δ_{o₀} for all L (deterministic constant output),
the joint distribution P_{LO} factors as P_L × P_O, so I(L;O) = D(P_{LO} ‖ P_L × P_O) = 0.
-/

/-- Helper: summing a Kronecker-delta-like finite family picks the single value. -/
private theorem sum_ite_eq_single {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} [AddCommMonoid β] (a0 : α) (c : β) :
    (∑ a, if a = a0 then c else 0) = c := by
  -- Reduce to `Finset.sum_eq_single` on `univ`.
  classical
  have hsum' :=
    Finset.sum_eq_single (s := (Finset.univ : Finset α))
      (f := fun a => if a = a0 then c else 0) a0
      (by
        intro a _ hne
        simp [hne])
      (by
        intro hnot
        exact False.elim (hnot (by simp)))
  calc
    (∑ a, if a = a0 then c else 0) = if a0 = a0 then c else 0 := hsum'
    _ = c := by simp

/-- Erasure form fixes the first marginal to the original label distribution. -/
private theorem marginalFst_of_erasure
    {L O : Type} [Fintype L] [Fintype O] [DecidableEq O]
    (labelDist : L → ℝ)
    (joint : L × O → ℝ)
    (hErase : IsErasureKernel labelDist joint) :
    marginalFst joint = labelDist := by
  -- Expand the erasure equation and collapse the indicator sum.
  classical
  rcases hErase with ⟨o0, hJoint⟩
  funext l
  calc
    marginalFst joint l = ∑ o, if o = o0 then labelDist l else 0 := by
      simp [marginalFst, hJoint, eq_comm]
    _ = labelDist l := sum_ite_eq_single o0 (labelDist l)

/-- Erasure form makes the second marginal a point mass. -/
private theorem marginalSnd_of_erasure
    {L O : Type} [Fintype L] [Fintype O] [DecidableEq O]
    (labelDist : L → ℝ)
    (h_sum : ∑ l, labelDist l = 1)
    (joint : L × O → ℝ)
    (o0 : O)
    (hJoint : ∀ lo : L × O, joint lo = if lo.2 = o0 then labelDist lo.1 else 0) :
    marginalSnd joint = fun o => if o = o0 then (1 : ℝ) else 0 := by
  -- Split on whether the observed value is the distinguished erased output.
  classical
  funext o
  by_cases ho : o = o0
  · subst ho
    simp [marginalSnd, hJoint, h_sum]
  · simp [marginalSnd, hJoint, ho]

/-- Under erasure, joint equals product of its marginals. -/
private theorem joint_eq_prod_of_erasure
    {L O : Type} [Fintype L] [Fintype O] [DecidableEq O]
    (labelDist : L → ℝ)
    (h_sum : ∑ l, labelDist l = 1)
    (joint : L × O → ℝ)
    (hErase : IsErasureKernel labelDist joint) :
    joint = fun lo => marginalFst joint lo.1 * marginalSnd joint lo.2 := by
  -- Combine the marginal characterizations and split on the erased observation.
  classical
  rcases hErase with ⟨o0, hJoint⟩
  have hfst : marginalFst joint = labelDist :=
    marginalFst_of_erasure labelDist joint ⟨o0, hJoint⟩
  have hsnd : marginalSnd joint = fun o => if o = o0 then 1 else 0 := by
    simpa using marginalSnd_of_erasure labelDist h_sum joint o0 hJoint
  funext lo
  rcases lo with ⟨l, o⟩
  by_cases ho : o = o0
  · subst ho
    simp [hJoint, hfst, hsnd]
  · simp [hJoint, hfst, hsnd, ho]

/-- Erasure implies zero mutual information in the concrete model. -/
theorem mutualInfo_zero_of_erasure
    {L O : Type} [Fintype L] [Fintype O] [DecidableEq O]
    (labelDist : L → ℝ)
    (h_nn : ∀ l, 0 ≤ labelDist l)
    (h_sum : ∑ l, labelDist l = 1)
    (joint : L × O → ℝ)
    (hErase : IsErasureKernel labelDist joint) :
    mutualInfo joint = 0 := by
  -- Erasure makes `joint` equal to product marginals, so KL reduces to `D(p || p) = 0`.
  classical
  have hJointNonneg : ∀ lo, 0 ≤ joint lo := by
    rcases hErase with ⟨o0, hJoint⟩
    intro lo
    by_cases h : lo.2 = o0
    · simp [hJoint lo, h, h_nn]
    · simp [hJoint lo, h]
  have hEq :
      (fun lo => marginalFst joint lo.1 * marginalSnd joint lo.2) = joint := by
    simpa using (joint_eq_prod_of_erasure labelDist h_sum joint hErase).symm
  unfold mutualInfo
  simpa [hEq] using klDivergence_self_eq_zero joint hJointNonneg

end RealConcrete

end

end EntropyAPI
