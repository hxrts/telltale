import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Information-Theoretic Cost Measures

Shannon entropy, KL divergence, mutual information, and conditional entropy
for finite distributions. Ported from Gibbs.Hamiltonian.Entropy — all
definitions are pure Mathlib arithmetic with no axioms or sorry.

These definitions provide the information-theoretic foundation for:
- `send_cost_plus_flow`: branch entropy quantifies the true cost of a select
- `cost_speculation_bounded`: KL divergence bounds speculative waste
- Channel capacity over `DeliveryModel`
-/

set_option autoImplicit false

namespace InformationCost

noncomputable section

open scoped BigOperators Classical

/-! ## Distributions -/

/-- Subtype for probability distributions on a finite type. -/
structure Distribution (α : Type*) [Fintype α] where
  pmf : α → ℝ
  nonneg : ∀ a, 0 ≤ pmf a
  sum_one : ∑ a, pmf a = 1

/-! ## Shannon Entropy -/

/-- Shannon entropy: H(p) = -∑ pᵢ log pᵢ with convention 0 log 0 = 0. -/
def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ a, if p a = 0 then 0 else p a * Real.log (p a)

/-- H(p) ≥ 0 for distributions. -/
theorem shannonEntropy_nonneg {α : Type*} [Fintype α]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    0 ≤ shannonEntropy p := by
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

/-- Entropy of a deterministic distribution is zero. -/
theorem shannonEntropy_deterministic {α : Type*} [Fintype α]
    (p : α → ℝ) (a₀ : α) (hp : ∀ a, p a = if a = a₀ then 1 else 0) :
    shannonEntropy p = 0 := by
  classical
  unfold shannonEntropy
  have hterm : ∀ a, (if p a = 0 then 0 else p a * Real.log (p a)) = 0 := by
    intro a
    by_cases h : a = a₀
    · subst h
      simp [hp]
    · have hp0 : p a = 0 := by simp [hp, h]
      simp [hp0]
  simp [hterm]

/-! ## KL Divergence -/

/-- KL divergence: D_KL(p‖q) = ∑ pᵢ log(pᵢ/qᵢ) with 0 log 0 = 0. -/
def klDivergence {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, if p a = 0 then 0 else p a * Real.log (p a / q a)

/-- Gibbs inequality: D_KL(p‖q) ≥ 0. -/
theorem klDivergence_nonneg {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    0 ≤ klDivergence p q := by
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
        -- combine the transformed inequality
        have := hmul
        -- rewrite both sides
        simpa [hleft, hright] using this
      simpa [hpa] using hineq
  have hsum : ∑ a, (p a - q a) ≤ ∑ a, (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
    exact Finset.sum_le_sum (fun a _ => hterm a)
  have hsum_pq : ∑ a, (p a - q a) = 0 := by
    simp [hp_sum, hq_sum]
  have : 0 ≤ ∑ a, (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
    linarith [hsum, hsum_pq]
  simpa [klDivergence] using this

/-- D_KL(p ‖ uniform) = log|α| - H(p). -/
private theorem kl_uniform_eq {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (_hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    klDivergence p (fun _ => 1 / Fintype.card α) =
      Real.log (Fintype.card α) - shannonEntropy p := by
  unfold klDivergence shannonEntropy
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hu_ne : (1 : ℝ) / Fintype.card α ≠ 0 := ne_of_gt (div_pos one_pos hcard)
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

/-- H(p) ≤ log |α| (Shannon bound) via D_KL(p ‖ uniform) ≥ 0. -/
theorem shannonEntropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card α) := by
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

/-- D_KL(p‖p) = 0: KL divergence of a distribution with itself vanishes. -/
private theorem klDivergence_self_eq_zero {α : Type*} [Fintype α]
    (p : α → ℝ) (_hp_nn : ∀ a, 0 ≤ p a) :
    klDivergence p p = 0 := by
  classical
  unfold klDivergence
  refine Finset.sum_eq_zero ?_
  intro a _
  by_cases hpa : p a = 0
  · simp [hpa]
  · simp [hpa]

/-- Each KL term satisfies p(a)*log(p(a)/q(a)) ≥ p(a) - q(a). -/
private theorem kl_term_ge_diff {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hq_nn : ∀ a, 0 ≤ q a)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) (a : α) :
    p a - q a ≤ (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
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
      rw [Real.log_div (habs a hpa) hpa, Real.log_div hpa (habs a hpa)]; ring
    simp only [hpa, ↓reduceIte]
    linarith

/-- When D_KL = 0, each KL term equals p(a) - q(a). -/
private theorem kl_term_eq_diff_of_zero {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hkl : klDivergence p q = 0) (a : α) :
    (if p a = 0 then 0 else p a * Real.log (p a / q a)) = p a - q a := by
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

/-- D_KL(p‖q) = 0 implies p = q pointwise. -/
private theorem klDivergence_eq_zero_imp_eq {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hkl : klDivergence p q = 0) : p = q := by
  classical
  funext a
  have hterm := kl_term_eq_diff_of_zero p q hp_nn hp_sum hq_nn hq_sum habs hkl a
  by_cases hpa : p a = 0
  · simp [hpa] at hterm; linarith
  · have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
    have hq_pos : 0 < q a := lt_of_le_of_ne (hq_nn a) (Ne.symm (habs a hpa))
    simp only [hpa, ↓reduceIte] at hterm
    have hlog_pq : Real.log (p a / q a) = 1 - q a / p a := by
      have h := div_eq_div_iff (ne_of_gt hpa_pos) (ne_of_gt hpa_pos) |>.mpr (by linarith)
      field_simp at hterm ⊢; linarith
    have hlog_qp : Real.log (q a / p a) = q a / p a - 1 := by
      rw [Real.log_div hpa (habs a hpa)] at hlog_pq
      rw [Real.log_div (habs a hpa) hpa]; linarith
    have hqp : q a / p a = 1 := by
      by_contra hne
      exact absurd hlog_qp (ne_of_lt (Real.log_lt_sub_one_of_pos
        (div_pos hq_pos hpa_pos) hne))
    rw [div_eq_one_iff_eq (ne_of_gt hpa_pos)] at hqp; linarith

/-- D_KL(p‖q) = 0 ↔ p = q. -/
theorem klDivergence_eq_zero_iff {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    klDivergence p q = 0 ↔ p = q := by
  constructor
  · exact klDivergence_eq_zero_imp_eq p q hp_nn hp_sum hq_nn hq_sum habs
  · intro heq; subst heq; exact klDivergence_self_eq_zero p hp_nn

/-- KL divergence decomposes as cross-entropy minus entropy. -/
theorem klDivergence_eq_crossEntropy_sub {α : Type*} [Fintype α]
    (p q : α → ℝ) (_hp_nn : ∀ a, 0 ≤ p a) (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    klDivergence p q =
      (∑ a, if p a = 0 then 0 else - p a * Real.log (q a)) - shannonEntropy p := by
  classical
  unfold klDivergence shannonEntropy
  have hterm : ∀ a,
      (if p a = 0 then 0 else p a * Real.log (p a / q a)) =
        (if p a = 0 then 0 else p a * Real.log (p a)) +
        (if p a = 0 then 0 else - p a * Real.log (q a)) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    · have hqne : q a ≠ 0 := habs a hpa
      have hlog : Real.log (p a / q a) = Real.log (p a) - Real.log (q a) :=
        Real.log_div hpa hqne
      simp [hpa, hlog, mul_add, sub_eq_add_neg]
  calc
    ∑ a, (if p a = 0 then 0 else p a * Real.log (p a / q a))
        = ∑ a, ((if p a = 0 then 0 else p a * Real.log (p a)) +
                (if p a = 0 then 0 else - p a * Real.log (q a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact hterm a
    _ = (∑ a, (if p a = 0 then 0 else p a * Real.log (p a))) +
        (∑ a, (if p a = 0 then 0 else - p a * Real.log (q a))) := by
          simp [Finset.sum_add_distrib]
    _ = (∑ a, (if p a = 0 then 0 else - p a * Real.log (q a))) -
        (-(∑ a, (if p a = 0 then 0 else p a * Real.log (p a)))) := by
          ring
    _ = (∑ a, (if p a = 0 then 0 else - p a * Real.log (q a))) - shannonEntropy p := by
          simp [shannonEntropy]

/-! ## Marginals and Joint Distributions -/

/-- Marginal over the first variable. -/
def marginalFst {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, pXY (a, b)

/-- Marginal over the second variable. -/
def marginalSnd {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, pXY (a, b)

/-! ## Mutual Information -/

def mutualInfo {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : ℝ :=
  shannonEntropy (marginalFst pXY) + shannonEntropy (marginalSnd pXY) - shannonEntropy pXY

/-- Product of marginals is nonneg. -/
private theorem prodMarginals_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) (ab : α × β) :
    0 ≤ marginalFst pXY ab.1 * marginalSnd pXY ab.2 := by
  exact mul_nonneg
    (Finset.sum_nonneg fun b _ => h_nn (ab.1, b))
    (Finset.sum_nonneg fun a _ => h_nn (a, ab.2))

/-- Product of marginals sums to 1. -/
private theorem prodMarginals_sum_one {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_sum : ∑ ab, pXY ab = 1) :
    ∑ ab : α × β, marginalFst pXY ab.1 * marginalSnd pXY ab.2 = 1 := by
  have hfst : ∑ a, marginalFst pXY a = 1 := by
    simp only [marginalFst]
    rw [show ∑ a, ∑ b, pXY (a, b) = ∑ ab : α × β, pXY ab from
      (Fintype.sum_prod_type _).symm]
    exact h_sum
  have hsnd : ∑ b, marginalSnd pXY b = 1 := by
    simp only [marginalSnd]
    rw [show ∑ b, ∑ a, pXY (a, b) = ∑ ab : α × β, pXY ab from
      (Fintype.sum_prod_type_right _).symm]
    exact h_sum
  have hprod : ∑ ab : α × β, marginalFst pXY ab.1 * marginalSnd pXY ab.2 =
      (∑ a, marginalFst pXY a) * (∑ b, marginalSnd pXY b) := by
    have h1 : ∑ ab : α × β, marginalFst pXY ab.1 * marginalSnd pXY ab.2 =
        ∑ a, ∑ b, marginalFst pXY a * marginalSnd pXY b := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [h1]; simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]
  rw [hprod, hfst, hsnd, one_mul]

/-- Absolute continuity: pXY(a,b) > 0 implies pX(a)*pY(b) > 0. -/
private theorem prodMarginals_abs_cont {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) (ab : α × β) :
    pXY ab ≠ 0 → marginalFst pXY ab.1 * marginalSnd pXY ab.2 ≠ 0 := by
  intro hne
  have hpos : 0 < pXY ab := lt_of_le_of_ne (h_nn ab) (Ne.symm hne)
  have hfst : 0 < marginalFst pXY ab.1 :=
    lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun b => pXY (ab.1, b)) (fun _ _ => h_nn _) (Finset.mem_univ ab.2))
  have hsnd : 0 < marginalSnd pXY ab.2 :=
    lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun a => pXY (a, ab.2)) (fun _ _ => h_nn _) (Finset.mem_univ ab.1))
  exact ne_of_gt (mul_pos hfst hsnd)

/-- Rewrite marginal entropy sum as a double sum with joint weights. -/
private theorem entropy_margFst_as_joint {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    (∑ a, if marginalFst pXY a = 0 then 0 else marginalFst pXY a *
      Real.log (marginalFst pXY a)) =
    ∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab *
      Real.log (marginalFst pXY ab.1) := by
  classical
  have h_rhs : (∑ ab : α × β, if pXY ab = 0 then 0
      else pXY ab * Real.log (marginalFst pXY ab.1)) =
      ∑ a, ∑ b, (if pXY (a, b) = 0 then 0
      else pXY (a, b) * Real.log (marginalFst pXY a)) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [h_rhs]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hpa : marginalFst pXY a = 0
  · have hzero : ∀ b, pXY (a, b) = 0 := fun b =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => h_nn (a, b))).mp
        (by simp [marginalFst] at hpa; exact hpa) b (Finset.mem_univ b)
    simp [hpa, hzero]
  · conv_rhs => rw [show ∑ b, (if pXY (a, b) = 0 then 0
      else pXY (a, b) * Real.log (marginalFst pXY a)) =
      ∑ b, pXY (a, b) * Real.log (marginalFst pXY a) from by
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h : pXY (a, b) = 0 <;> simp [h]]
    rw [← Finset.sum_mul]
    unfold marginalFst at hpa
    split
    · contradiction
    · rfl

/-- Same rewrite for the second marginal. -/
private theorem entropy_margSnd_as_joint {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    (∑ b, if marginalSnd pXY b = 0 then 0 else marginalSnd pXY b *
      Real.log (marginalSnd pXY b)) =
    ∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab *
      Real.log (marginalSnd pXY ab.2) := by
  classical
  have h_rhs : (∑ ab : α × β, if pXY ab = 0 then 0
      else pXY ab * Real.log (marginalSnd pXY ab.2)) =
      ∑ b, ∑ a, (if pXY (a, b) = 0 then 0
      else pXY (a, b) * Real.log (marginalSnd pXY b)) := by
    rw [← Finset.univ_product_univ, Finset.sum_product_right]
  rw [h_rhs]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hpb : marginalSnd pXY b = 0
  · have hzero : ∀ a, pXY (a, b) = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => h_nn (a, b))).mp
        (by simp [marginalSnd] at hpb; exact hpb) a (Finset.mem_univ a)
    simp [hpb, hzero]
  · conv_rhs => rw [show ∑ a, (if pXY (a, b) = 0 then 0
      else pXY (a, b) * Real.log (marginalSnd pXY b)) =
      ∑ a, pXY (a, b) * Real.log (marginalSnd pXY b) from by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : pXY (a, b) = 0 <;> simp [h]]
    rw [← Finset.sum_mul]
    unfold marginalSnd at hpb
    split
    · contradiction
    · rfl

/-- Mutual information equals KL divergence from joint to product of marginals. -/
private theorem mutualInfo_eq_klDivergence {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    mutualInfo pXY = klDivergence pXY
      (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2) := by
  classical
  unfold mutualInfo shannonEntropy klDivergence
  rw [entropy_margFst_as_joint pXY h_nn, entropy_margSnd_as_joint pXY h_nn]
  rw [sub_neg_eq_add]
  simp only [← Finset.sum_neg_distrib (f := fun ab =>
    if pXY ab = 0 then 0 else pXY ab * Real.log (marginalFst pXY ab.1)),
    ← Finset.sum_neg_distrib (f := fun ab =>
    if pXY ab = 0 then 0 else pXY ab * Real.log (marginalSnd pXY ab.2)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ab _ => ?_
  by_cases h : pXY ab = 0
  · simp [h]
  · have hprod := prodMarginals_abs_cont pXY h_nn ab h
    simp only [h, ↓reduceIte]
    have hfst : marginalFst pXY ab.1 ≠ 0 := left_ne_zero_of_mul hprod
    have hsnd : marginalSnd pXY ab.2 ≠ 0 := right_ne_zero_of_mul hprod
    rw [Real.log_div h hprod, Real.log_mul hfst hsnd]
    ring

/-- Mutual information is nonnegative: I(X;Y) = D_KL(p_XY ‖ p_X ⊗ p_Y) ≥ 0. -/
theorem mutualInfo_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab)
    (h_sum : ∑ ab, pXY ab = 1) :
    0 ≤ mutualInfo pXY := by
  rw [mutualInfo_eq_klDivergence pXY h_nn]
  exact klDivergence_nonneg pXY _ h_nn h_sum
    (fun ab => prodMarginals_nonneg pXY h_nn ab)
    (prodMarginals_sum_one pXY h_sum)
    (fun ab => prodMarginals_abs_cont pXY h_nn ab)

/-! ## Conditional Entropy -/

/-- Conditional entropy H(X|Y) = H(X,Y) - H(Y). -/
def condEntropy {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : ℝ :=
  shannonEntropy pXY - shannonEntropy (marginalSnd pXY)

/-- Conditional entropy is nonnegative. -/
theorem condEntropy_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) (_h_sum : ∑ ab, pXY ab = 1) :
    0 ≤ condEntropy pXY := by
  classical
  let pY : β → ℝ := marginalSnd pXY
  have hpY_nonneg : ∀ y, 0 ≤ pY y := by
    intro y
    unfold pY
    refine Finset.sum_nonneg ?_
    intro x hx
    exact h_nn (x, y)
  have hpXY_le : ∀ x y, pXY (x, y) ≤ pY y := by
    intro x y
    have hmem : x ∈ (Finset.univ : Finset α) := by simp
    have hle : pXY (x, y) ≤ ∑ x', pXY (x', y) := by
      exact Finset.single_le_sum (f := fun x' => pXY (x', y)) (fun _ _ => h_nn _) hmem
    simpa [pY] using hle
  have hpXY_eq_zero_of_pY_eq_zero :
      ∀ y, pY y = 0 → ∀ x, pXY (x, y) = 0 := by
    intro y hy x
    have hsum' : ∑ x', pXY (x', y) = 0 := by
      simpa [pY] using hy
    have hzero : ∀ x' ∈ (Finset.univ : Finset α), pXY (x', y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset α))
        (fun x' _ => h_nn (x', y))).1 hsum'
    exact hzero x (by simp)
  have hsum_log :
      (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) =
        (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) := by
    have hinner :
        (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) =
          ∑ y, ∑ x, if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y) := by
      refine Finset.sum_congr rfl ?_
      intro y hy
      by_cases hpy : pY y = 0
      · have hzero : ∀ x, pXY (x, y) = 0 := hpXY_eq_zero_of_pY_eq_zero y hpy
        simp [hpy, hzero]
      · have hterm :
            ∀ x, (if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y)) =
              pXY (x, y) * Real.log (pY y) := by
            intro x
            by_cases hxy : pXY (x, y) = 0
            · simp [hxy]
            · simp [hxy]
        have hcalc :
            (∑ x, if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y)) =
              pY y * Real.log (pY y) := by
          calc
            (∑ x, if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y))
                = (∑ x, pXY (x, y) * Real.log (pY y)) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    exact hterm x
            _ = (∑ x, pXY (x, y)) * Real.log (pY y) := by
                    simp [Finset.sum_mul]
            _ = pY y * Real.log (pY y) := by rfl
        simpa [hpy] using hcalc.symm
    have hsum_prod :
        (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) =
          ∑ y, ∑ x, if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y) := by
      simpa using (Fintype.sum_prod_type_right
        (f := fun ab : α × β => if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)))
    exact hinner.trans hsum_prod.symm
  unfold condEntropy shannonEntropy
  have hrewrite :
      -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
        (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) =
        (∑ ab : α × β,
          (if pXY ab = 0 then 0
           else pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab)))) := by
    have hsum_y :
        (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) =
          (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) := by
      simp [hsum_log]
    have hcomb :
        -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
            (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) =
          (∑ ab : α × β,
            (-(if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
              (if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)))) := by
      calc
        -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
            (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2))
            = (∑ ab, -(if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab))) +
                (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) := by
                simp [Finset.sum_neg_distrib]
        _ = (∑ ab : α × β,
              (-(if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
                (if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)))) := by
              simpa using
                (Finset.sum_add_distrib
                  (f := fun ab => -(if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)))
                  (g := fun ab => if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2))).symm
    calc
      -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
          (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y))
          = -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
              (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) := by
                simp [hsum_y]
      _ = (∑ ab : α × β,
            (if pXY ab = 0 then 0
             else pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab)))) := by
            refine (hcomb.trans ?_)
            refine Finset.sum_congr rfl ?_
            intro ab hab
            by_cases hpa : pXY ab = 0
            · simp [hpa]
            ·
              have hring :
                  -(pXY ab * Real.log (pXY ab)) + pXY ab * Real.log (pY ab.2) =
                    pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab)) := by
                ring
              simpa [hpa] using hring
  have hterm_nonneg :
      ∀ ab, 0 ≤
        (if pXY ab = 0 then 0
         else pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab))) := by
    intro ab
    by_cases hpa : pXY ab = 0
    · simp [hpa]
    · have hpa_pos : 0 < pXY ab := lt_of_le_of_ne (h_nn ab) (Ne.symm hpa)
      have hpy_ge : pXY ab ≤ pY ab.2 := hpXY_le ab.1 ab.2
      have hlog_le : Real.log (pXY ab) ≤ Real.log (pY ab.2) :=
        Real.log_le_log hpa_pos hpy_ge
      have hdiff_nonneg : 0 ≤ Real.log (pY ab.2) - Real.log (pXY ab) := by
        linarith
      have hmul_nonneg :
          0 ≤ pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab)) :=
        mul_nonneg (h_nn ab) hdiff_nonneg
      simpa [hpa] using hmul_nonneg
  have hsum_nonneg :
      0 ≤ ∑ ab : α × β,
        (if pXY ab = 0 then 0
         else pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab))) := by
    refine Finset.sum_nonneg ?_
    intro ab hab
    exact hterm_nonneg ab
  have : 0 ≤
      -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
        (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) := by
    simpa [hrewrite] using hsum_nonneg
  linarith

/-- Conditioning reduces entropy: H(X|Y) ≤ H(X). -/
theorem condEntropy_le_entropy {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab)
    (h_sum : ∑ ab, pXY ab = 1) :
    condEntropy pXY ≤ shannonEntropy (marginalFst pXY) := by
  have hmi : 0 ≤ mutualInfo pXY := by
    exact mutualInfo_nonneg pXY h_nn h_sum
  have hmi' :
      0 ≤ shannonEntropy (marginalFst pXY) + shannonEntropy (marginalSnd pXY) -
            shannonEntropy pXY := by
    simpa [mutualInfo] using hmi
  unfold condEntropy
  linarith

/-! ## Mutual Information Symmetry -/

/-- I(X;Y) = I(Y;X). -/
theorem mutualInfo_symm {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) :
    mutualInfo pXY = mutualInfo (fun ⟨b, a⟩ => pXY (a, b)) := by
  classical
  let pYX : β × α → ℝ := fun ab => pXY (ab.2, ab.1)
  unfold mutualInfo
  have hfst : marginalFst pYX = marginalSnd pXY := by
    funext b
    change (∑ a, pYX (b, a)) = ∑ a, pXY (a, b)
    simp [pYX]
  have hsnd : marginalSnd pYX = marginalFst pXY := by
    funext a
    change (∑ b, pYX (b, a)) = ∑ b, pXY (a, b)
    simp [pYX]
  have hswap :
      shannonEntropy pYX = shannonEntropy pXY := by
    unfold shannonEntropy
    have hsum :
        ∑ ab : β × α,
          (if pYX ab = 0 then 0 else pYX ab * Real.log (pYX ab)) =
        ∑ ab : α × β,
          (if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) := by
      simpa using (Equiv.sum_comp (Equiv.prodComm α β)
        (fun ab : β × α =>
          if pYX ab = 0 then 0 else pYX ab * Real.log (pYX ab))).symm
    simp [hsum]
  simp [pYX, hfst, hsnd, hswap, add_comm]

/-! ## Data Processing Inequality -/

/-- A Markov kernel (stochastic map) from β to γ. -/
structure MarkovKernel (β γ : Type*) [Fintype β] [Fintype γ] where
  transition : β → γ → ℝ
  nonneg : ∀ b c, 0 ≤ transition b c
  sum_one : ∀ b, ∑ c, transition b c = 1

/-- Push a joint distribution through a kernel on the second variable. -/
def pushforward {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) : α × γ → ℝ :=
  fun ⟨a, c⟩ => ∑ b, pXY (a, b) * K.transition b c

/-- Pushforward preserves nonnegativity. -/
private theorem pushforward_nonneg {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ)
    (h_nn : ∀ ab, 0 ≤ pXY ab) : ∀ ac, 0 ≤ pushforward pXY K ac := by
  intro ⟨a, c⟩
  exact Finset.sum_nonneg fun b _ => mul_nonneg (h_nn (a, b)) (K.nonneg b c)

/-- Pushforward preserves total mass. -/
private theorem pushforward_sum_one {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ)
    (h_sum : ∑ ab, pXY ab = 1) : ∑ ac, pushforward pXY K ac = 1 := by
  simp only [pushforward]
  have : ∀ a, ∑ c, ∑ b, pXY (a, b) * K.transition b c =
      ∑ b, pXY (a, b) := by
    intro a; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, K.sum_one, mul_one]
  rw [← Finset.univ_product_univ, Finset.sum_product]; simp_rw [this]
  rw [← Fintype.sum_prod_type]; exact h_sum

/-- First marginal of pushforward equals first marginal of original. -/
private theorem pushforward_marginalFst {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) (a : α) :
    marginalFst (pushforward pXY K) a = marginalFst pXY a := by
  simp only [marginalFst, pushforward]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, K.sum_one, mul_one]

/-- Second marginal of pushforward: pZ(c) = Σ_b pY(b)·K(b,c). -/
private theorem pushforward_marginalSnd {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) (c : γ) :
    marginalSnd (pushforward pXY K) c =
      ∑ b, marginalSnd pXY b * K.transition b c := by
  simp only [marginalSnd, pushforward]
  rw [Finset.sum_comm]; congr 1; ext b; exact (Finset.sum_mul ..).symm

/-! ### Log-Sum Inequality -/

/-- Per-term bound from log(x) ≤ x - 1. -/
private theorem log_sum_term_bound {a_y b_y Sa Sb : ℝ}
    (ha : 0 < a_y) (hb : 0 < b_y) (hSa : 0 < Sa) (hSb : 0 < Sb) :
    a_y * Real.log (b_y * Sa / (a_y * Sb)) ≤ b_y * Sa / Sb - a_y := by
  have hratio : 0 < b_y * Sa / (a_y * Sb) := div_pos (mul_pos hb hSa) (mul_pos ha hSb)
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hsimp : a_y * (b_y * Sa / (a_y * Sb) - 1) = b_y * Sa / Sb - a_y := by
    field_simp
  linarith [mul_le_mul_of_nonneg_left hlog ha.le]

/-- Log splitting: a·log(b·Sa/(a·Sb)) = -a·log(a/b) + a·log(Sa/Sb). -/
private theorem log_sum_term_split {a_y b_y Sa Sb : ℝ}
    (ha : a_y ≠ 0) (hb : b_y ≠ 0) (hSa : 0 < Sa) (hSb : 0 < Sb) :
    a_y * Real.log (b_y * Sa / (a_y * Sb)) =
      -(a_y * Real.log (a_y / b_y)) + a_y * Real.log (Sa / Sb) := by
  have h1 : b_y * Sa / (a_y * Sb) = (b_y / a_y) * (Sa / Sb) := by field_simp
  rw [h1, Real.log_mul (div_ne_zero hb ha) (ne_of_gt (div_pos hSa hSb))]
  have h2 : b_y / a_y = (a_y / b_y)⁻¹ := by field_simp
  rw [h2, Real.log_inv]; ring

/-- RHS of log-sum per-term bound sums to ≤ 0. -/
private theorem log_sum_rhs_le {β : Type*} [Fintype β]
    (a b : β → ℝ) (hb_nn : ∀ y, 0 ≤ b y) (hSa : 0 < ∑ y, a y)
    (hSb : 0 < ∑ y, b y) :
    ∑ y, (if a y = 0 then 0
      else b y * (∑ y, a y) / (∑ y, b y) - a y) ≤ 0 := by
  calc ∑ y, (if a y = 0 then 0
        else b y * (∑ y, a y) / (∑ y, b y) - a y)
      ≤ ∑ y, (b y * (∑ y, a y) / (∑ y, b y) - a y) := by
        apply Finset.sum_le_sum; intro y _; split_ifs with h
        · linarith [div_nonneg (mul_nonneg (hb_nn y) hSa.le) hSb.le]
        · exact le_refl _
    _ = (∑ y, b y) * (∑ y, a y) / (∑ y, b y) - ∑ y, a y := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    _ = 0 := by
        rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hSb), mul_one, sub_self]

/-- LHS of log-sum rewritten via log splitting. -/
private theorem log_sum_lhs_eq {β : Type*} [Fintype β]
    (a b : β → ℝ) (_ha_nn : ∀ y, 0 ≤ a y)
    (habs : ∀ y, a y ≠ 0 → b y ≠ 0)
    (hSa : 0 < ∑ y, a y) (hSb : 0 < ∑ y, b y) :
    ∑ y, (if a y = 0 then 0
      else a y * Real.log (b y * (∑ y, a y) / (a y * (∑ y, b y)))) =
    -(∑ y, if a y = 0 then 0 else a y * Real.log (a y / b y)) +
      (∑ y, a y) * Real.log ((∑ y, a y) / (∑ y, b y)) := by
  have hterms : ∀ y, (if a y = 0 then 0
      else a y * Real.log (b y * (∑ y, a y) / (a y * (∑ y, b y)))) =
    (if a y = 0 then 0 else -(a y * Real.log (a y / b y))) +
      a y * Real.log ((∑ y, a y) / (∑ y, b y)) := by
    intro y; by_cases hay : a y = 0
    · simp [hay]
    · simp only [hay, ↓reduceIte]
      exact log_sum_term_split hay (habs y hay) hSa hSb
  simp_rw [hterms, Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1; rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun y _ => by by_cases hay : a y = 0 <;> simp [hay]

/-- Log-sum inequality, positive-sum case. -/
private theorem log_sum_ineq_pos {β : Type*} [Fintype β]
    (a b : β → ℝ) (ha_nn : ∀ y, 0 ≤ a y) (hb_nn : ∀ y, 0 ≤ b y)
    (habs : ∀ y, a y ≠ 0 → b y ≠ 0) (hSb : 0 < ∑ y, b y)
    (hSa : ∑ y, a y ≠ 0) :
    (∑ y, a y) * Real.log ((∑ y, a y) / (∑ y, b y)) ≤
      ∑ y, if a y = 0 then 0 else a y * Real.log (a y / b y) := by
  have hSa_pos : 0 < ∑ y, a y :=
    lt_of_le_of_ne (Finset.sum_nonneg fun y _ => ha_nn y) (Ne.symm hSa)
  have hbound : ∀ y, (if a y = 0 then 0
      else a y * Real.log (b y * (∑ y, a y) / (a y * (∑ y, b y)))) ≤
      (if a y = 0 then 0 else b y * (∑ y, a y) / (∑ y, b y) - a y) := by
    intro y; by_cases hay : a y = 0
    · simp [hay]
    · simp only [hay, ↓reduceIte]
      exact log_sum_term_bound (lt_of_le_of_ne (ha_nn y) (Ne.symm hay))
        (lt_of_le_of_ne (hb_nn y) (Ne.symm (habs y hay))) hSa_pos hSb
  linarith [le_trans (Finset.sum_le_sum fun y _ => hbound y)
    (log_sum_rhs_le a b hb_nn hSa_pos hSb),
    log_sum_lhs_eq a b ha_nn habs hSa_pos hSb]

/-- Log-sum inequality: (Σa)·log(Σa/Σb) ≤ Σ aᵢ·log(aᵢ/bᵢ). -/
private theorem log_sum_inequality {β : Type*} [Fintype β]
    (a b : β → ℝ) (ha_nn : ∀ y, 0 ≤ a y) (hb_nn : ∀ y, 0 ≤ b y)
    (habs : ∀ y, a y ≠ 0 → b y ≠ 0)
    (hSb : 0 < ∑ y, b y) :
    (∑ y, a y) * Real.log ((∑ y, a y) / (∑ y, b y)) ≤
      ∑ y, if a y = 0 then 0 else a y * Real.log (a y / b y) := by
  by_cases hSa : ∑ y, a y = 0
  · have ha0 : ∀ y, a y = 0 := fun y => le_antisymm
      (le_trans (Finset.single_le_sum (fun y _ => ha_nn y) (Finset.mem_univ y))
        (le_of_eq hSa)) (ha_nn y)
    simp [ha0]
  · exact log_sum_ineq_pos a b ha_nn hb_nn habs hSb hSa

/-! ### KL Decrease Under Marginalization -/

/-- Per-component bound for KL marginalization. -/
private theorem kl_margin_term {A B : Type*} [Fintype A] [Fintype B]
    (f g : A × B → ℝ) (hf_nn : ∀ ab, 0 ≤ f ab) (hg_nn : ∀ ab, 0 ≤ g ab)
    (habs : ∀ ab, f ab ≠ 0 → g ab ≠ 0) (a : A) :
    (if marginalFst f a = 0 then 0
      else marginalFst f a * Real.log (marginalFst f a / marginalFst g a)) ≤
    ∑ b, (if f (a, b) = 0 then 0
      else f (a, b) * Real.log (f (a, b) / g (a, b))) := by
  by_cases hfa : marginalFst f a = 0
  · have hzero : ∀ b, f (a, b) = 0 := fun b => le_antisymm
      (le_trans (Finset.single_le_sum (fun b _ => hf_nn (a, b)) (Finset.mem_univ b))
        (le_of_eq hfa)) (hf_nn (a, b))
    simp [hfa, hzero]
  · have hga_pos : 0 < marginalFst g a := by
      by_contra hga; push_neg at hga
      have hga0 : marginalFst g a = 0 := le_antisymm hga
        (Finset.sum_nonneg fun b _ => hg_nn (a, b))
      have hg0 : ∀ b, g (a, b) = 0 := fun b => le_antisymm (le_trans
        (Finset.single_le_sum (fun b _ => hg_nn (a, b)) (Finset.mem_univ b))
        (le_of_eq hga0)) (hg_nn (a, b))
      have hf0 : ∀ b, f (a, b) = 0 := fun b => by
        by_contra hfab; exact absurd (hg0 b) (habs (a, b) hfab)
      exact absurd (show marginalFst f a = 0 by simp [marginalFst, hf0]) hfa
    simp only [hfa, ↓reduceIte]
    exact log_sum_inequality (fun b => f (a, b)) (fun b => g (a, b))
      (fun b => hf_nn (a, b)) (fun b => hg_nn (a, b))
      (fun b hb => habs (a, b) hb) hga_pos

/-- KL divergence decreases under marginalization. -/
private theorem kl_marginalize_le {A B : Type*} [Fintype A] [Fintype B]
    (f g : A × B → ℝ) (hf_nn : ∀ ab, 0 ≤ f ab) (hg_nn : ∀ ab, 0 ≤ g ab)
    (habs : ∀ ab, f ab ≠ 0 → g ab ≠ 0) :
    klDivergence (marginalFst f) (marginalFst g) ≤ klDivergence f g := by
  unfold klDivergence
  rw [show ∑ ab : A × B, (if f ab = 0 then 0 else f ab * Real.log (f ab / g ab)) =
    ∑ a, ∑ b, (if f (a, b) = 0 then 0 else f (a, b) * Real.log (f (a, b) / g (a, b))) from
      Fintype.sum_prod_type _]
  exact Finset.sum_le_sum fun a _ => kl_margin_term f g hf_nn hg_nn habs a

/-! ### Data Processing Inequality -/

/-- Joint distribution pXYZ(x,y,c) = pXY(x,y)·K(c|y) on (α×γ) × β. -/
private def dpiJoint {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) : (α × γ) × β → ℝ :=
  fun ⟨⟨x, c⟩, y⟩ => pXY (x, y) * K.transition y c

/-- Reference distribution qXYZ(x,y,c) = pX(x)·pY(y)·K(c|y). -/
private def dpiRef {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) : (α × γ) × β → ℝ :=
  fun ⟨⟨x, c⟩, y⟩ => marginalFst pXY x * marginalSnd pXY y * K.transition y c

private theorem dpiJoint_nonneg {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    ∀ t, 0 ≤ dpiJoint pXY K t := by
  intro ⟨⟨x, c⟩, y⟩; exact mul_nonneg (h_nn (x, y)) (K.nonneg y c)

private theorem dpiRef_nonneg {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    ∀ t, 0 ≤ dpiRef pXY K t := by
  intro ⟨⟨x, c⟩, y⟩
  exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun b _ => h_nn (x, b))
    (Finset.sum_nonneg fun a _ => h_nn (a, y))) (K.nonneg y c)

private theorem dpi_abs_cont {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    ∀ t, dpiJoint pXY K t ≠ 0 → dpiRef pXY K t ≠ 0 := by
  intro ⟨⟨x, c⟩, y⟩ hne
  simp only [dpiJoint] at hne
  have hxy := left_ne_zero_of_mul hne
  have hk := right_ne_zero_of_mul hne
  have hxy_pos := lt_of_le_of_ne (h_nn (x, y)) (Ne.symm hxy)
  have hpx : marginalFst pXY x ≠ 0 := ne_of_gt (lt_of_lt_of_le hxy_pos
    (Finset.single_le_sum (fun b _ => h_nn (x, b)) (Finset.mem_univ y)))
  have hpy : marginalSnd pXY y ≠ 0 := ne_of_gt (lt_of_lt_of_le hxy_pos
    (Finset.single_le_sum (fun a _ => h_nn (a, y)) (Finset.mem_univ x)))
  simp only [dpiRef]; exact mul_ne_zero (mul_ne_zero hpx hpy) hk

private theorem dpiJoint_margFst {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) :
    marginalFst (dpiJoint pXY K) = pushforward pXY K := by
  ext ⟨x, c⟩; simp [marginalFst, dpiJoint, pushforward]

private theorem dpiRef_margFst {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) :
    marginalFst (dpiRef pXY K) =
      fun ac => marginalFst pXY ac.1 * marginalSnd (pushforward pXY K) ac.2 := by
  ext ⟨x, c⟩
  show ∑ y, marginalFst pXY x * marginalSnd pXY y * K.transition y c =
    marginalFst pXY x * marginalSnd (pushforward pXY K) c
  simp_rw [mul_assoc]; rw [← Finset.mul_sum, pushforward_marginalSnd]

/-- K cancels in KL if-then-else. -/
private theorem kl_ite_mul_cancel {a b k : ℝ} (_hk : 0 ≤ k) :
    (if a * k = 0 then (0 : ℝ) else a * k * Real.log (a * k / (b * k))) =
    k * (if a = 0 then 0 else a * Real.log (a / b)) := by
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hk0 : k = 0
    · simp [hk0]
    · simp only [mul_ne_zero ha hk0, ha, ↓reduceIte]
      rw [mul_div_mul_right _ _ hk0]; ring

/-- KL of dpiJoint vs dpiRef equals KL of pXY vs pX⊗pY (K cancels). -/
private theorem dpi_kl_eq {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) (_h_nn : ∀ ab, 0 ≤ pXY ab) :
    klDivergence (dpiJoint pXY K) (dpiRef pXY K) =
      klDivergence pXY (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2) := by
  have rhs_eq : klDivergence pXY
      (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2) =
    ∑ x, ∑ y, (if pXY (x, y) = 0 then 0 else pXY (x, y) *
      Real.log (pXY (x, y) / (marginalFst pXY x * marginalSnd pXY y))) := by
    unfold klDivergence; exact Fintype.sum_prod_type _
  rw [rhs_eq]; unfold klDivergence dpiJoint dpiRef
  have hsplit : ∀ (F : (α × γ) × β → ℝ),
      ∑ t, F t = ∑ x, ∑ c, ∑ y, F ((x, c), y) := fun F => by
    simp only [Fintype.sum_prod_type]
  rw [hsplit]
  simp_rw [kl_ite_mul_cancel (K.nonneg _ _)]
  congr 1; ext x; rw [Finset.sum_comm]
  congr 1; ext y; rw [← Finset.sum_mul, K.sum_one, one_mul]

/-- Data processing inequality: I(X;Z) ≤ I(X;Y) for Markov chain X → Y → Z. -/
theorem data_processing_inequality {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ)
    (h_nn : ∀ ab, 0 ≤ pXY ab) (_h_sum : ∑ ab, pXY ab = 1) :
    mutualInfo (pushforward pXY K) ≤ mutualInfo pXY := by
  rw [mutualInfo_eq_klDivergence _ (pushforward_nonneg pXY K h_nn),
      mutualInfo_eq_klDivergence pXY h_nn]
  have hlhs : klDivergence (pushforward pXY K)
      (fun ac => marginalFst (pushforward pXY K) ac.1 *
        marginalSnd (pushforward pXY K) ac.2) =
    klDivergence (marginalFst (dpiJoint pXY K)) (marginalFst (dpiRef pXY K)) := by
    rw [dpiJoint_margFst, dpiRef_margFst]
    congr 1; ext ⟨x, _⟩; simp only; rw [pushforward_marginalFst]
  rw [hlhs]
  calc klDivergence (marginalFst (dpiJoint pXY K)) (marginalFst (dpiRef pXY K))
      ≤ klDivergence (dpiJoint pXY K) (dpiRef pXY K) :=
        kl_marginalize_le _ _ (dpiJoint_nonneg pXY K h_nn) (dpiRef_nonneg pXY K h_nn)
          (dpi_abs_cont pXY K h_nn)
    _ = klDivergence pXY (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2) :=
        dpi_kl_eq pXY K h_nn

/-! ## Telltale Integration -/

/-- Entropy cost of a branching label distribution.
    Wraps shannonEntropy for use in session type cost models. -/
def branchEntropy {L : Type*} [Fintype L] (labelDist : L → ℝ) : ℝ :=
  shannonEntropy labelDist

/-- Branch entropy is nonneg for distributions. -/
theorem branchEntropy_nonneg {L : Type*} [Fintype L]
    (d : Distribution L) :
    0 ≤ branchEntropy d.pmf :=
  shannonEntropy_nonneg d.pmf d.nonneg d.sum_one

/-- Branch entropy bounded by log |L| (Shannon bound). -/
theorem branchEntropy_le_log_card {L : Type*} [Fintype L] [Nonempty L]
    (d : Distribution L) :
    branchEntropy d.pmf ≤ Real.log (Fintype.card L) :=
  shannonEntropy_le_log_card d.pmf d.nonneg d.sum_one

/-- Total cost of a select operation: computation cost plus information-theoretic
    entropy of the label distribution. -/
def selectCost {L : Type*} [Fintype L] (compCost : ℝ) (labelDist : L → ℝ) : ℝ :=
  compCost + branchEntropy labelDist

/-- Speculative divergence: KL divergence from speculative label distribution
    to committed distribution. Measures potential wasted work. -/
def speculationDivergence {L : Type*} [Fintype L]
    (specDist commitDist : L → ℝ) : ℝ :=
  klDivergence specDist commitDist

/-! ## Information-Theoretic Projection

Connection between information theory and blindness in projection.

**Key insight**: When a role r is blind to a communication between p and q,
r's local information (entropy) is unchanged by the communication. This is
the information-theoretic counterpart to the noninterference theorem.

**Data processing interpretation**: The projection map for a non-participant
is a deterministic function (all branches project to the same type), so by
data processing inequality, no information about the branch choice can flow
to the non-participant.
-/

/-- A projection function that maps global branch labels to local behavior.
    For non-participants, this function is constant (all branches same). -/
structure ProjectionMap (L : Type*) (T : Type*) where
  /-- The projection function. -/
  proj : L → T

/-- Whether the projection is constant (for non-participants). -/
def ProjectionMap.isConstant {L T : Type*} (p : ProjectionMap L T) : Prop :=
  ∃ t, ∀ l, p.proj l = t

private theorem sum_ite_eq_single {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} [AddCommMonoid β] (a0 : α) (c : β) :
    (∑ a, if a0 = a then c else 0) = c := by
  classical
  have hsum' :=
    Finset.sum_eq_single (s := (Finset.univ : Finset α))
      (f := fun a => if a0 = a then c else 0) a0
      (by
        intro a _ hne
        have hne' : a0 ≠ a := by exact Ne.symm hne
        simp [hne'])
      (by
        intro hnot
        exact (False.elim (hnot (by simp))))
  have hsum :
      Finset.sum (Finset.univ : Finset α) (fun a => if a0 = a then c else 0) =
        if a0 = a0 then c else 0 := by
    exact hsum'
  calc
    (∑ a, if a0 = a then c else 0) = if a0 = a0 then c else 0 := hsum
    _ = c := by simp

private theorem marginalFst_const_projection
    {L T : Type*} [Fintype L] [Fintype T] [DecidableEq T]
    (p : ProjectionMap L T) (hConst : p.isConstant) (labelDist : L → ℝ) :
    marginalFst (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) =
      labelDist := by
  classical
  obtain ⟨t0, ht0⟩ := hConst
  funext l
  have hsum := sum_ite_eq_single t0 (labelDist l)
  calc
    marginalFst (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) l =
        ∑ t, if t0 = t then labelDist l else 0 := by
      simp [marginalFst, ht0]
    _ = labelDist l := hsum

private theorem marginalSnd_const_projection
    {L T : Type*} [Fintype L] [Fintype T] [DecidableEq T]
    (p : ProjectionMap L T) (t0 : T) (ht0 : ∀ l, p.proj l = t0)
    (labelDist : L → ℝ) (h_sum : ∑ l, labelDist l = 1) :
    marginalSnd (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) =
      fun t => if t0 = t then 1 else 0 := by
  classical
  funext t
  by_cases ht : t0 = t
  · subst ht
    simp [marginalSnd, ht0, h_sum]
  · simp [marginalSnd, ht0, ht]

private theorem joint_eq_prod_marginals_const_projection
    {L T : Type*} [Fintype L] [Fintype T] [DecidableEq T]
    (p : ProjectionMap L T) (hConst : p.isConstant)
    (labelDist : L → ℝ) (h_sum : ∑ l, labelDist l = 1) :
    (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) =
      fun ab =>
        marginalFst (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) ab.1 *
          marginalSnd (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) ab.2 := by
  classical
  obtain ⟨t0, ht0⟩ := hConst
  have hfst := marginalFst_const_projection p ⟨t0, ht0⟩ labelDist
  have hsnd := marginalSnd_const_projection p t0 ht0 labelDist h_sum
  funext ab
  cases ab with
  | mk l t =>
      have hfst_l : marginalFst (fun lt : L × T =>
          if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) l = labelDist l := by
        simpa using congrArg (fun f => f l) hfst
      have hsnd_t : marginalSnd (fun lt : L × T =>
          if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) t =
          if t0 = t then 1 else 0 := by
        simpa using congrArg (fun f => f t) hsnd
      by_cases ht : t0 = t
      · subst ht
        have hfst_l' :
            marginalFst (fun lt : L × T => if t0 = lt.2 then labelDist lt.1 else 0) l =
              labelDist l := by
          simpa [ht0] using hfst_l
        have hsnd_t' :
            marginalSnd (fun lt : L × T => if t0 = lt.2 then labelDist lt.1 else 0) t0 = 1 := by
          have hsnd_t'' :
              marginalSnd (fun lt : L × T => if t0 = lt.2 then labelDist lt.1 else 0) t0 =
                if t0 = t0 then 1 else 0 := by
            simpa [ht0] using hsnd_t
          simpa using hsnd_t''
        simp [ht0, hfst_l', hsnd_t']
      · have hsnd_t' :
            marginalSnd (fun lt : L × T => if t0 = lt.2 then labelDist lt.1 else 0) t = 0 := by
          have hsnd_t'' :
              marginalSnd (fun lt : L × T => if t0 = lt.2 then labelDist lt.1 else 0) t =
                if t0 = t then 1 else 0 := by
            simpa [ht0] using hsnd_t
          simpa [ht] using hsnd_t''
        simp [ht0, ht, hsnd_t']

/-- When projection is constant, mutual information with the projected type is zero.
    This is the information-theoretic formulation of blindness. -/
theorem mutualInfo_zero_of_constant_projection
    {L T : Type*} [Fintype L] [Fintype T] [DecidableEq T]
    (p : ProjectionMap L T) (hConst : p.isConstant)
    (labelDist : L → ℝ) (h_nn : ∀ l, 0 ≤ labelDist l) (h_sum : ∑ l, labelDist l = 1) :
    mutualInfo (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) = 0 := by
  classical
  let pXY : L × T → ℝ := fun lt => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0
  have h_nn' : ∀ ab, 0 ≤ pXY ab := by
    intro ab
    by_cases h : p.proj ab.1 = ab.2
    · simp [pXY, h, h_nn]
    · simp [pXY, h]
  have hEq : (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2) = pXY := by
    simpa [pXY] using
      (joint_eq_prod_marginals_const_projection p hConst labelDist h_sum).symm
  have hmi :
      mutualInfo pXY =
        klDivergence pXY (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2) :=
    mutualInfo_eq_klDivergence pXY h_nn'
  have hkl : klDivergence pXY (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2) = 0 := by
    simpa [hEq] using (klDivergence_self_eq_zero pXY h_nn')
  simpa [pXY] using hmi.trans hkl

/-- Blind projection preserves local entropy.

    If role r is blind to a communication (p → q : branches), then r's
    local type entropy is unchanged regardless of which branch is taken.

    **Proof sketch**: By constancy of blind projection, all branches
    give the same local type, so the conditional entropy H(L_r | branch)
    equals the unconditional entropy H(L_r). -/
theorem blind_projection_entropy_unchanged
    {L : Type*} [Fintype L] [Nonempty L]
    (branchDist : L → ℝ)
    (localEntropy : L → ℝ) -- H(local type) for each branch
    (_h_nn : ∀ l, 0 ≤ branchDist l)
    (h_sum : ∑ l, branchDist l = 1)
    (hBlind : ∀ l₁ l₂, localEntropy l₁ = localEntropy l₂) :
    ∑ l, branchDist l * localEntropy l = localEntropy (Classical.arbitrary L) := by
  -- When local entropy is constant across branches, expected entropy
  -- equals that constant value.
  let l₀ := Classical.arbitrary L
  have hconst : ∀ l, localEntropy l = localEntropy l₀ := fun l => hBlind l l₀
  calc ∑ l, branchDist l * localEntropy l
      = ∑ l, branchDist l * localEntropy l₀ := by
          congr 1; ext l; rw [hconst]
    _ = localEntropy l₀ * ∑ l, branchDist l := by
          rw [Finset.mul_sum]; congr 1; ext l; ring
    _ = localEntropy l₀ := by rw [h_sum, mul_one]

/-- Information cost of a non-participant observing a branch choice is zero.
    This quantifies the noninterference property in information-theoretic terms. -/
def blindObservationCost : ℝ := 0

/-- Blind observation has zero cost (by definition). -/
theorem blindObservationCost_eq_zero : blindObservationCost = 0 := rfl

end

end InformationCost
