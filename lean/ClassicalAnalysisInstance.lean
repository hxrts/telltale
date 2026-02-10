import Mathlib
import ClassicalAnalysisAPI

/-
The Problem. `ClassicalAnalysisAPI` exposes abstract operations/laws, but the
project also needs one concrete real-analysis model.

Solution Structure.
1. Define concrete entropy/KL/mutual-information operations.
2. Prove the API law obligations for those operations.
3. Package them into `realLaws` and `realAnalysisLaws`.
-/

/-! # ClassicalAnalysisInstance

## Expose

Concrete realizations consumed by downstream modules:

- entropy instance:
  `EntropyAPI.realModel`, `EntropyAPI.realLaws`
- extended analysis instance:
  `EntropyAPI.realAnalysisModel`, `EntropyAPI.realAnalysisLaws`

Everything in this file is an implementation detail except those exported
instances and definitions.
-/

set_option autoImplicit false

namespace EntropyAPI

open scoped BigOperators Classical

noncomputable section

namespace RealConcrete

/-! ## Core Information Operations -/

/-- Shannon entropy with the 0*log 0 convention. -/
def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ a, if p a = 0 then 0 else p a * Real.log (p a)

/-- KL divergence with the 0*log 0 convention. -/
def klDivergence {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, if p a = 0 then 0 else p a * Real.log (p a / q a)

/-- First marginal of a finite joint distribution. -/
def marginalFst {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, pXY (a, b)

/-- Second marginal of a finite joint distribution. -/
def marginalSnd {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, pXY (a, b)

/-- Mutual information defined as KL divergence to product of marginals. -/
def mutualInfo {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : ℝ :=
  klDivergence pXY (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2)

/-! ## KL and Entropy Laws -/

/-- Shannon entropy is nonnegative for distributions. -/
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

/-- KL divergence is nonnegative (Gibbs inequality). -/
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

/-! ## Erasure Law -/

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
  spectral_gap_eq := by
    -- The gap field is defined as `1 - secondSpectrumValue`.
    intro State _ _ kernel
    simp [realAnalysisModel]

end
end EntropyAPI
