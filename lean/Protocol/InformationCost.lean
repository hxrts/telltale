import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import ClassicalAnalysisAPI
import Choreography.Projection.Project

/-!
# Information-Theoretic Cost Measures

Protocol-facing wrappers around `EntropyAPI`, plus blindness/erasure bridge
lemmas used in projection reasoning.
-/

set_option autoImplicit false

namespace InformationCost

open scoped BigOperators Classical

/-
The Problem. Protocol-level statements should use information-theoretic notions
without depending on concrete real-analysis implementations.

Solution Structure.
1. Re-expose entropy/KL/mutual-information operations through `EntropyAPI`.
2. Re-expose the minimal laws needed by protocol statements.
3. Keep protocol-specific blindness/projection lemmas in this file.
-/

/-! ## Distribution Wrapper -/

/-- Finite probability distributions used in protocol statements. -/
abbrev Distribution := EntropyAPI.Distribution

/-! ## Core Operations -/

/-- Shannon entropy wrapper. -/
def shannonEntropy {α : Type*} [Fintype α] [EntropyAPI.Model] (p : α → ℝ) : ℝ :=
  EntropyAPI.shannonEntropy p

/-- KL divergence wrapper. -/
def klDivergence {α : Type*} [Fintype α] [EntropyAPI.Model] (p q : α → ℝ) : ℝ :=
  EntropyAPI.klDivergence p q

/-- First marginal of a finite joint distribution. -/
def marginalFst {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, pXY (a, b)

/-- Second marginal of a finite joint distribution. -/
def marginalSnd {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, pXY (a, b)

/-- Mutual information wrapper. -/
def mutualInfo {α β : Type*} [Fintype α] [Fintype β] [EntropyAPI.Model]
    (pXY : α × β → ℝ) : ℝ :=
  EntropyAPI.mutualInfo pXY

/-- Conditional entropy wrapper. -/
def condEntropy {α β : Type} [Fintype α] [Fintype β] [EntropyAPI.Model]
    (pXY : α × β → ℝ) : ℝ :=
  EntropyAPI.shannonEntropy pXY -
    EntropyAPI.shannonEntropy (marginalSnd (α := α) (β := β) pXY)

/-! ## Core Law Wrappers -/

/-- Shannon entropy is nonnegative for distributions. -/
theorem shannonEntropy_nonneg {α : Type*} [Fintype α] [EntropyAPI.Laws]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    0 ≤ shannonEntropy p := by
  -- Package the raw assumptions as an API distribution and reuse the API law.
  let d : Distribution α :=
    { pmf := p, nonneg := hp_nn, sum_one := hp_sum }
  simpa [shannonEntropy, d] using EntropyAPI.shannonEntropy_nonneg d

/-- Shannon entropy is bounded by `log |α|`. -/
theorem shannonEntropy_le_log_card {α : Type*} [Fintype α] [Nonempty α] [EntropyAPI.Laws]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card α) := by
  -- Package the raw assumptions as an API distribution and reuse the API law.
  let d : Distribution α :=
    { pmf := p, nonneg := hp_nn, sum_one := hp_sum }
  simpa [shannonEntropy, d] using EntropyAPI.shannonEntropy_le_log_card d

/-- KL divergence is nonnegative (Gibbs inequality). -/
theorem klDivergence_nonneg {α : Type*} [Fintype α] [EntropyAPI.Laws]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    0 ≤ klDivergence p q := by
  -- Package both raw assumptions as API distributions and reuse the API law.
  let pd : Distribution α :=
    { pmf := p, nonneg := hp_nn, sum_one := hp_sum }
  let qd : Distribution α :=
    { pmf := q, nonneg := hq_nn, sum_one := hq_sum }
  simpa [klDivergence, pd, qd] using EntropyAPI.klDivergence_nonneg pd qd habs

/-- KL divergence vanishes iff distributions are pointwise equal. -/
theorem klDivergence_eq_zero_iff {α : Type*} [Fintype α] [EntropyAPI.Laws]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    klDivergence p q = 0 ↔ p = q := by
  -- Package both raw assumptions as API distributions and reuse the API law.
  let pd : Distribution α :=
    { pmf := p, nonneg := hp_nn, sum_one := hp_sum }
  let qd : Distribution α :=
    { pmf := q, nonneg := hq_nn, sum_one := hq_sum }
  simpa [klDivergence, pd, qd] using EntropyAPI.klDivergence_eq_zero_iff pd qd habs

/-! ## Protocol Cost Combinators -/

/-- Entropy cost of a branching-label distribution. -/
def branchEntropy {L : Type*} [Fintype L] [EntropyAPI.Model]
    (labelDist : L → ℝ) : ℝ :=
  shannonEntropy labelDist

/-- Branch entropy is nonnegative for distributions. -/
theorem branchEntropy_nonneg {L : Type*} [Fintype L] [EntropyAPI.Laws]
    (d : Distribution L) :
    0 ≤ branchEntropy d.pmf := by
  -- This is direct from Shannon entropy nonnegativity.
  simpa [branchEntropy, shannonEntropy] using EntropyAPI.shannonEntropy_nonneg d

/-- Branch entropy is bounded by `log |L|`. -/
theorem branchEntropy_le_log_card {L : Type*} [Fintype L] [Nonempty L] [EntropyAPI.Laws]
    (d : Distribution L) :
    branchEntropy d.pmf ≤ Real.log (Fintype.card L) := by
  -- This is direct from the Shannon entropy cardinality bound.
  simpa [branchEntropy, shannonEntropy] using EntropyAPI.shannonEntropy_le_log_card d

/-- Total select cost: computation cost plus entropy cost. -/
def selectCost {L : Type*} [Fintype L] [EntropyAPI.Model]
    (compCost : ℝ) (labelDist : L → ℝ) : ℝ :=
  compCost + branchEntropy labelDist

/-- Speculative divergence wrapper. -/
def speculationDivergence {L : Type*} [Fintype L] [EntropyAPI.Model]
    (specDist commitDist : L → ℝ) : ℝ :=
  klDivergence specDist commitDist

/-! ## Projection Erasure Bridge -/

/-- Projection function from branch labels to observer-local views. -/
structure ProjectionMap (L : Type*) (T : Type*) where
  /-- The projection function. -/
  proj : L → T

/-- Constancy predicate for projection maps. -/
def ProjectionMap.isConstant {L T : Type*} (p : ProjectionMap L T) : Prop :=
  ∃ t, ∀ l, p.proj l = t

/-- Erasure-kernel formulation of zero mutual information. -/
theorem mutualInfo_zero_of_erasure
    {L O : Type} [Fintype L] [Fintype O] [DecidableEq O] [EntropyAPI.Laws]
    (labelDist : L → ℝ) (h_nn : ∀ l, 0 ≤ labelDist l) (h_sum : ∑ l, labelDist l = 1)
    (joint : L × O → ℝ)
    (hErase : EntropyAPI.IsErasureKernel labelDist joint) :
    mutualInfo joint = 0 := by
  -- This is exactly the API erasure law.
  simpa [mutualInfo] using
    EntropyAPI.mutualInfo_zero_of_erasure labelDist h_nn h_sum joint hErase

/-- Constant projection implies zero mutual information with observations. -/
theorem mutualInfo_zero_of_constant_projection
    {L T : Type} [Fintype L] [Fintype T] [DecidableEq T] [EntropyAPI.Laws]
    (p : ProjectionMap L T) (hConst : p.isConstant)
    (labelDist : L → ℝ) (h_nn : ∀ l, 0 ≤ labelDist l) (h_sum : ∑ l, labelDist l = 1) :
    mutualInfo (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) = 0 := by
  -- Constancy gives an erasure kernel, then the API erasure law yields zero MI.
  obtain ⟨t0, ht0⟩ := hConst
  have hErase : EntropyAPI.IsErasureKernel labelDist
      (fun lt : L × T => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) := by
    refine ⟨t0, ?_⟩
    intro lt
    simpa [ht0 lt.1, eq_comm]
  exact mutualInfo_zero_of_erasure labelDist h_nn h_sum _ hErase

/-- Constant local quantity has expectation equal to that constant. -/
theorem blind_projection_entropy_unchanged
    {L : Type*} [Fintype L] [Nonempty L]
    (branchDist : L → ℝ)
    (localEntropy : L → ℝ)
    (_h_nn : ∀ l, 0 ≤ branchDist l)
    (h_sum : ∑ l, branchDist l = 1)
    (hBlind : ∀ l₁ l₂, localEntropy l₁ = localEntropy l₂) :
    ∑ l, branchDist l * localEntropy l = localEntropy (Classical.arbitrary L) := by
  -- If local entropy is constant over labels, weighted averaging returns that value.
  let l0 := Classical.arbitrary L
  have hconst : ∀ l, localEntropy l = localEntropy l0 := fun l => hBlind l l0
  calc
    ∑ l, branchDist l * localEntropy l
        = ∑ l, branchDist l * localEntropy l0 := by
            congr 1
            ext l
            rw [hconst]
    _ = localEntropy l0 * ∑ l, branchDist l := by
            rw [Finset.mul_sum]
            congr 1
            ext l
            ring
    _ = localEntropy l0 := by
            rw [h_sum, mul_one]

/-- Constant projection preserves expected local information. -/
theorem projection_preserves_local_information
    {L T : Type*} [Fintype L]
    (p : ProjectionMap L T) (hConst : p.isConstant)
    (labelDist : L → ℝ) (_h_nn : ∀ l, 0 ≤ labelDist l)
    (h_sum : ∑ l, labelDist l = 1) (localInfo : T → ℝ) :
    ∑ l, labelDist l * localInfo (p.proj l) = localInfo (Classical.choose hConst) := by
  -- Constancy lets us factor `localInfo` out of the weighted sum.
  classical
  have ht0 : ∀ l, p.proj l = Classical.choose hConst :=
    Classical.choose_spec hConst
  calc
    ∑ l, labelDist l * localInfo (p.proj l)
        = ∑ l, labelDist l * localInfo (Classical.choose hConst) := by
            congr 1
            ext l
            rw [ht0]
    _ = localInfo (Classical.choose hConst) * ∑ l, labelDist l := by
            rw [Finset.mul_sum]
            congr 1
            ext l
            ring
    _ = localInfo (Classical.choose hConst) := by
            simp [h_sum]

/-! ## Blindness Bridge -/

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Blind

/-- Projection map over branch indices for a fixed observer role. -/
def branchProjectionMap (branches : List (Label × GlobalType)) (role : String) :
    ProjectionMap (Fin branches.length) LocalTypeR :=
  -- Each branch index selects a continuation and projects it to the role.
  { proj := fun i => Choreography.Projection.Trans.trans (branches.get i).2 role }

/-- Blind communication implies constant projected local behavior for non-participants. -/
theorem branchProjectionMap_isConstant_of_commBlindFor
    {sender receiver role : String} {branches : List (Label × GlobalType)}
    (hblind : commBlindFor sender receiver branches = true)
    (hns : role ≠ sender) (hnr : role ≠ receiver) (hne : branches ≠ []) :
    (branchProjectionMap branches role).isConstant := by
  -- Uniform projection for non-participants follows from the blindness lemma.
  classical
  refine ⟨Choreography.Projection.Trans.trans (branches.head!.2) role, ?_⟩
  intro i
  have hmem : branches.get i ∈ branches := by
    exact List.get_mem _ _
  have huniform :=
    trans_uniform_for_nonparticipant (sender := sender) (receiver := receiver) (role := role)
      (branches := branches) hblind hns hnr hne (branches.get i) hmem
  simpa [branchProjectionMap] using huniform

/-- `isBlind` on a communication implies constant projected local behavior. -/
theorem branchProjectionMap_isConstant_of_isBlind_comm
    {sender receiver role : String} {branches : List (Label × GlobalType)}
    (hblind : isBlind (GlobalType.comm sender receiver branches) = true)
    (hns : role ≠ sender) (hnr : role ≠ receiver) (hne : branches ≠ []) :
    (branchProjectionMap branches role).isConstant := by
  -- Extract `commBlindFor` from `isBlind` and reuse the previous theorem.
  have hcomm : commBlindFor sender receiver branches = true := by
    have hblind' := hblind
    simp [isBlind, Bool.and_eq_true] at hblind'
    exact hblind'.1
  exact branchProjectionMap_isConstant_of_commBlindFor hcomm hns hnr hne

/-- Information cost of blind observation is zero by definition. -/
def blindObservationCost : ℝ := 0

/-- Blind-observation cost simplifies to zero. -/
theorem blindObservationCost_eq_zero : blindObservationCost = 0 := rfl

/-- Main bridge theorem from syntactic blindness to invariant local expectation. -/
theorem isBlind_preserves_local_information
    {sender receiver role : String} {branches : List (Label × GlobalType)}
    (hblind : isBlind (GlobalType.comm sender receiver branches) = true)
    (hns : role ≠ sender) (hnr : role ≠ receiver) (hne : branches ≠ [])
    (labelDist : Fin branches.length → ℝ)
    (_h_nn : ∀ l, 0 ≤ labelDist l)
    (h_sum : ∑ l, labelDist l = 1)
    (localInfo : LocalTypeR → ℝ) :
    let p := branchProjectionMap branches role
    ∑ l, labelDist l * localInfo (p.proj l) =
      localInfo (Classical.choose (branchProjectionMap_isConstant_of_isBlind_comm
        hblind hns hnr hne)) := by
  -- Combine blindness-induced constancy with the generic constant-projection lemma.
  have hConst := branchProjectionMap_isConstant_of_isBlind_comm hblind hns hnr hne
  exact projection_preserves_local_information
    (branchProjectionMap branches role) hConst labelDist _h_nn h_sum localInfo

/-- Corollary: blindness implies deterministic projected local type. -/
theorem isBlind_implies_constant_local_type
    {sender receiver role : String} {branches : List (Label × GlobalType)}
    (hblind : isBlind (GlobalType.comm sender receiver branches) = true)
    (hns : role ≠ sender) (hnr : role ≠ receiver) (hne : branches ≠ [])
    (i j : Fin branches.length) :
    (branchProjectionMap branches role).proj i =
    (branchProjectionMap branches role).proj j := by
  -- Specialize the constant map witness at two branch indices.
  have hConst := branchProjectionMap_isConstant_of_isBlind_comm hblind hns hnr hne
  obtain ⟨t, ht⟩ := hConst
  simp [ht]

end InformationCost
