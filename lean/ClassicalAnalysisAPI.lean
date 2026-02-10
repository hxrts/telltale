import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
-/

/-! # ClassicalAnalysisAPI

## Expose

This module defines the abstract boundary consumed by the rest of the project:

- entropy interface:
  `EntropyAPI.Distribution`, `EntropyAPI.IsErasureKernel`,
  `EntropyAPI.Model`, `EntropyAPI.Laws`,
  `EntropyAPI.shannonEntropy`, `EntropyAPI.klDivergence`,
  `EntropyAPI.mutualInfo`
- entropy law wrappers:
  `EntropyAPI.shannonEntropy_nonneg`,
  `EntropyAPI.shannonEntropy_le_log_card`,
  `EntropyAPI.klDivergence_nonneg`,
  `EntropyAPI.klDivergence_eq_zero_iff`,
  `EntropyAPI.mutualInfo_zero_of_erasure`
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

/-! ## Entropy Laws -/

/-- Shannon entropy nonnegativity law. -/
abbrev ShannonEntropyNonneg (M : Model) : Prop :=
  ∀ {α : Type*} [Fintype α], (d : Distribution α) →
    0 ≤ @Model.shannonEntropy M α _ d.pmf

/-- Shannon entropy cardinality upper bound law. -/
abbrev ShannonEntropyLeLogCard (M : Model) : Prop :=
  ∀ {α : Type*} [Fintype α] [Nonempty α], (d : Distribution α) →
    @Model.shannonEntropy M α _ d.pmf ≤ Real.log (Fintype.card α)

/-- KL nonnegativity law (Gibbs inequality). -/
abbrev KlDivergenceNonneg (M : Model) : Prop :=
  ∀ {α : Type*} [Fintype α], (p q : Distribution α) →
    (∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) →
    0 ≤ @Model.klDivergence M α _ p.pmf q.pmf

/-- Zero-KL characterization law. -/
abbrev KlDivergenceEqZeroIff (M : Model) : Prop :=
  ∀ {α : Type*} [Fintype α], (p q : Distribution α) →
    (∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) →
    (@Model.klDivergence M α _ p.pmf q.pmf = 0 ↔ p.pmf = q.pmf)

/-- Erasure implies zero mutual information law. -/
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
  shannonEntropy_nonneg : ShannonEntropyNonneg toModel
  shannonEntropy_le_log_card : ShannonEntropyLeLogCard toModel
  klDivergence_nonneg : KlDivergenceNonneg toModel
  klDivergence_eq_zero_iff : KlDivergenceEqZeroIff toModel
  mutualInfo_zero_of_erasure : MutualInfoZeroOfErasure toModel

/-- Promote `Laws` to `Model` so operation wrappers infer automatically. -/
instance (priority := 100) lawsToModel [Laws] : Model :=
  Laws.toModel

section Laws

variable [Laws]

/-- Re-export Shannon entropy nonnegativity from `Laws`. -/
theorem shannonEntropy_nonneg {α : Type*} [Fintype α]
    (d : Distribution α) :
    0 ≤ shannonEntropy d.pmf :=
  Laws.shannonEntropy_nonneg (self := inferInstance) d

/-- Re-export Shannon entropy cardinality upper bound from `Laws`. -/
theorem shannonEntropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (d : Distribution α) :
    shannonEntropy d.pmf ≤ Real.log (Fintype.card α) :=
  Laws.shannonEntropy_le_log_card (self := inferInstance) d

/-- Re-export KL nonnegativity from `Laws`. -/
theorem klDivergence_nonneg {α : Type*} [Fintype α]
    (p q : Distribution α)
    (habs : ∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) :
    0 ≤ klDivergence p.pmf q.pmf :=
  Laws.klDivergence_nonneg (self := inferInstance) p q habs

/-- Re-export zero-KL characterization from `Laws`. -/
theorem klDivergence_eq_zero_iff {α : Type*} [Fintype α]
    (p q : Distribution α)
    (habs : ∀ a, p.pmf a ≠ 0 → q.pmf a ≠ 0) :
    klDivergence p.pmf q.pmf = 0 ↔ p.pmf = q.pmf :=
  Laws.klDivergence_eq_zero_iff (self := inferInstance) p q habs

/-- Re-export erasure-implies-zero-MI from `Laws`. -/
theorem mutualInfo_zero_of_erasure {L O : Type}
    [Fintype L] [Fintype O] [DecidableEq O]
    (labelDist : L → ℝ)
    (h_nn : ∀ l, 0 ≤ labelDist l)
    (h_sum : ∑ l, labelDist l = 1)
    (joint : L × O → ℝ)
    (hErase : IsErasureKernel labelDist joint) :
    mutualInfo joint = 0 :=
  Laws.mutualInfo_zero_of_erasure
    (self := inferInstance) labelDist h_nn h_sum joint hErase

end Laws

/-! ## Extended Analysis Operations -/

/-- Neutral operations for real/complex-analysis touchpoints. -/
class AnalysisModel where
  exponentialTail : ℝ → ℝ → ℝ
  fluctuationScale : Nat → ℝ
  finiteAverage : {n : Nat} → (Fin n → ℝ) → ℝ
  normalizedCumulative : (Nat → ℝ) → ℝ → Nat → Nat → ℝ
  transitionMatrixComplex :
    {State : Type*} → [Fintype State] → [DecidableEq State] →
      (State → State → ℝ) → Matrix State State ℂ
  nontrivialSpectrumModuli :
    {State : Type*} → [Fintype State] → [DecidableEq State] →
      (State → State → ℝ) → Set ℝ
  secondSpectrumValue :
    {State : Type*} → [Fintype State] → [DecidableEq State] →
      (State → State → ℝ) → ℝ
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

/-! ## Extended Analysis Laws -/

/-- Minimal laws required by downstream users of `AnalysisModel`. -/
class AnalysisLaws extends AnalysisModel where
  exponentialTail_nonneg :
    ∀ (σ t : ℝ), 0 ≤ toAnalysisModel.exponentialTail σ t
  exponentialTail_zero :
    ∀ (σ : ℝ), toAnalysisModel.exponentialTail σ 0 = 2
  fluctuationScale_pos :
    ∀ {n : Nat}, 0 < n → 0 < toAnalysisModel.fluctuationScale n
  fluctuationScale_sq :
    ∀ (n : Nat), (toAnalysisModel.fluctuationScale n) ^ 2 = n
  finiteAverage_perm :
    ∀ {n : Nat}, (σ : Equiv.Perm (Fin n)) → (x : Fin n → ℝ) →
      toAnalysisModel.finiteAverage (fun i => x (σ i)) =
      toAnalysisModel.finiteAverage x
  finiteAverage_const :
    ∀ {n : Nat}, (c : ℝ) → n ≠ 0 →
      toAnalysisModel.finiteAverage (fun _ : Fin n => c) = c
  normalizedCumulative_const_zero :
    ∀ (c : ℝ) (N t : Nat), N ≠ 0 →
      toAnalysisModel.normalizedCumulative (fun _ => c) c N t = 0
  spectral_gap_eq :
    ∀ {State : Type*} [Fintype State] [DecidableEq State]
      (kernel : State → State → ℝ),
      toAnalysisModel.spectralGapValue kernel =
      1 - toAnalysisModel.secondSpectrumValue kernel

section AnalysisLaws

variable [AnalysisLaws]

/-- Re-export nonnegativity of the exponential-tail form. -/
theorem exponentialTail_nonneg (σ t : ℝ) : 0 ≤ exponentialTail σ t :=
  AnalysisLaws.exponentialTail_nonneg (self := inferInstance) σ t

/-- Re-export normalization at zero threshold for the exponential-tail form. -/
theorem exponentialTail_zero (σ : ℝ) : exponentialTail σ 0 = 2 :=
  AnalysisLaws.exponentialTail_zero (self := inferInstance) σ

/-- Re-export positivity of fluctuation scale for positive index. -/
theorem fluctuationScale_pos {n : Nat} (hn : 0 < n) :
    0 < fluctuationScale n :=
  AnalysisLaws.fluctuationScale_pos (self := inferInstance) hn

/-- Re-export squared-scale identity. -/
theorem fluctuationScale_sq (n : Nat) :
    (fluctuationScale n) ^ 2 = n :=
  AnalysisLaws.fluctuationScale_sq (self := inferInstance) n

/-- Re-export permutation invariance of finite averages. -/
theorem finiteAverage_perm {n : Nat} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    finiteAverage (fun i => x (σ i)) = finiteAverage x :=
  AnalysisLaws.finiteAverage_perm (self := inferInstance) σ x

/-- Re-export constant-family identity for finite averages. -/
theorem finiteAverage_const {n : Nat} (c : ℝ) (hn : n ≠ 0) :
    finiteAverage (fun _ : Fin n => c) = c :=
  AnalysisLaws.finiteAverage_const (self := inferInstance) c hn

/-- Re-export zero fluctuation for centered constant cumulative process. -/
theorem normalizedCumulative_const_zero (c : ℝ) (N t : Nat) (hN : N ≠ 0) :
    normalizedCumulative (fun _ => c) c N t = 0 :=
  AnalysisLaws.normalizedCumulative_const_zero (self := inferInstance) c N t hN

/-- Re-export relation between spectral gap and second spectral value. -/
theorem spectral_gap_eq {State : Type*} [Fintype State] [DecidableEq State]
    (kernel : State → State → ℝ) :
    spectralGapValue kernel = 1 - secondSpectrumValue kernel :=
  AnalysisLaws.spectral_gap_eq (self := inferInstance) kernel

end AnalysisLaws

end EntropyAPI
