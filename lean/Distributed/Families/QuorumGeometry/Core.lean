import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-! # Distributed.Families.QuorumGeometry

Quorum-geometry safety derived from a concrete Byzantine fault model:
- `n` validators, at most `f` of them Byzantine,
- every certificate is signed by a quorum of at least `q` validators,
- the threshold condition `n + f < 2 * q` (e.g. `n = 3f+1`, `q = 2f+1`),
- honest validators never sign two conflicting decisions at one state.

From these we prove (not assume) that two quorums share an honest validator,
and derive no-conflicting-commits, fork exclusion, and safe finality.
-/

/-
The Problem. Earlier versions stored a "lock monotonicity" field that was
the no-conflicting-commits conclusion itself. Safety must instead follow
from counting plus per-validator honesty.
Solution Structure. State the numeric fault model and local honesty rule,
prove honest quorum intersection by cardinality, then derive safety.
-/

/-! ## Core Development -/

namespace Distributed
namespace QuorumGeometry

universe u v w x

/-- Model interface for quorum-geometry reasoning. `signed s p d` means validator
`p` cast a signature/vote for `d` in the round/height represented by `s`. -/
structure Model (State : Type u) (Decision : Type v) (Certificate : Type w) (Party : Type x) where
  certified : State → Decision → Certificate → Prop
  signers : Certificate → Finset Party
  signed : State → Party → Decision → Prop
  conflicts : Decision → Decision → Prop

/-- A decision is committed at state `s` if it has a certificate at `s`. -/
def Committed
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Model State Decision Certificate Party)
    (s : State) (d : Decision) : Prop :=
  ∃ c, M.certified s d c

/-- Finalized decisions are committed decisions in this abstraction. -/
def Finalized
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Model State Decision Certificate Party)
    (s : State) (d : Decision) : Prop :=
  Committed M s d

/-- Fork predicate: two conflicting committed decisions coexist at one state. -/
def Forked
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Model State Decision Certificate Party)
    (s : State) : Prop :=
  ∃ d₁ d₂, Committed M s d₁ ∧ Committed M s d₂ ∧ M.conflicts d₁ d₂

/-! ## Fault Model and Assumptions -/

/-- Numeric fault-model parameters: validator count, Byzantine bound, quorum size. -/
structure Params where
  n : Nat
  f : Nat
  q : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Threshold condition making any two quorums overlap in more than `f` validators. -/
def Params.ThresholdOK (P : Params) : Prop := P.n + P.f < 2 * P.q

instance (P : Params) : Decidable P.ThresholdOK := by
  unfold Params.ThresholdOK; infer_instance

/-- Classical BFT sizing `n = 3f+1`, `q = 2f+1` satisfies the threshold. -/
theorem classical_bft_threshold (f : Nat) :
    ({ n := 3 * f + 1, f := f, q := 2 * f + 1 } : Params).ThresholdOK := by
  simp only [Params.ThresholdOK]; omega

/-- Fault-model assumptions. None of these fields mentions commits jointly:
`honestNoEquivocation` is a per-validator, per-state behavioural rule. -/
structure Assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Model State Decision Certificate Party) where
  params : Params
  validators : Finset Party
  byzantine : Finset Party
  validatorCount : validators.card = params.n
  byzantineBound : byzantine.card ≤ params.f
  threshold : params.ThresholdOK
  certSignersValidators : ∀ {s d c}, M.certified s d c → M.signers c ⊆ validators
  certQuorumSize : ∀ {s d c}, M.certified s d c → params.q ≤ (M.signers c).card
  certSignaturesGenuine :
    ∀ {s d c p}, M.certified s d c → p ∈ M.signers c → M.signed s p d
  honestNoEquivocation :
    ∀ {s p d₁ d₂}, p ∉ byzantine → M.signed s p d₁ → M.signed s p d₂ →
      ¬ M.conflicts d₁ d₂

/-! ## Honest Quorum Intersection -/

/-- Two size-`q` subsets of an `n`-set overlap in at least `2q - n` elements. -/
theorem inter_card_lower {Party : Type x} [DecidableEq Party]
    (A B V : Finset Party) (hA : A ⊆ V) (hB : B ⊆ V) :
    A.card + B.card ≤ V.card + (A ∩ B).card := by
  have hU : (A ∪ B).card ≤ V.card := Finset.card_le_card (Finset.union_subset hA hB)
  have := Finset.card_union_add_card_inter A B
  omega

/-- Generic counting lemma: quorums of size `≥ q` inside `n` validators with
`n + f < 2q` share a validator outside any set of at most `f` Byzantine parties. -/
theorem honest_in_inter {Party : Type x} [DecidableEq Party]
    (A B V Byz : Finset Party) (n f q : Nat)
    (hA : A ⊆ V) (hB : B ⊆ V) (hV : V.card = n) (hByz : Byz.card ≤ f)
    (hqA : q ≤ A.card) (hqB : q ≤ B.card) (hT : n + f < 2 * q) :
    ∃ p, p ∈ A ∧ p ∈ B ∧ p ∉ Byz := by
  have hI := inter_card_lower A B V hA hB
  have hSd := Finset.le_card_sdiff Byz (A ∩ B)
  obtain ⟨p, hp⟩ : ((A ∩ B) \ Byz).Nonempty := by
    rw [← Finset.card_pos]; omega
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hp
  exact ⟨p, hp.1.1, hp.1.2, hp.2⟩

/-- Certificates for any two decisions at one state share an honest signer. -/
theorem honest_quorum_intersection
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party} (a : Assumptions M)
    {s : State} {d₁ d₂ : Decision} {c₁ c₂ : Certificate}
    (h₁ : M.certified s d₁ c₁) (h₂ : M.certified s d₂ c₂) :
    ∃ p, p ∈ M.signers c₁ ∧ p ∈ M.signers c₂ ∧ p ∉ a.byzantine := by
  classical
  exact honest_in_inter _ _ a.validators a.byzantine a.params.n a.params.f a.params.q
    (a.certSignersValidators h₁) (a.certSignersValidators h₂) a.validatorCount
    a.byzantineBound (a.certQuorumSize h₁) (a.certQuorumSize h₂) a.threshold

/-! ## Assumption Validation API -/

/-- Assumption labels for summary/validation APIs. -/
inductive Assumption where
  | thresholdCondition
  | classicalSizing
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Assumptions every `Assumptions` bundle guarantees (sizing is optional). -/
def coreAssumptions : List Assumption :=
  [.thresholdCondition]

/-- Proposition named by each assumption label over concrete parameters. -/
def Assumption.Holds (P : Params) : Assumption → Prop
  | .thresholdCondition => P.ThresholdOK
  | .classicalSizing => 3 * P.f + 1 ≤ P.n ∧ 2 * P.f + 1 ≤ P.q

instance (P : Params) (h : Assumption) : Decidable (h.Holds P) := by
  cases h <;> unfold Assumption.Holds <;> infer_instance

/-- Validate one assumption by deciding it over the concrete parameters. -/
def validateAssumption (P : Params) (h : Assumption) : AssumptionResult :=
  { assumption := h, passed := decide (h.Holds P)
  , detail := match h with
      | .thresholdCondition => "n + f < 2q (quorums intersect in > f validators)."
      | .classicalSizing => "n ≥ 3f+1 and q ≥ 2f+1." }

/-- Soundness: a passing validation result establishes the named assumption. -/
theorem validateAssumption_sound (P : Params) (h : Assumption)
    (hPass : (validateAssumption P h).passed = true) : h.Holds P :=
  of_decide_eq_true hPass

/-- Validate a list of assumptions. -/
def validateAssumptions (P : Params) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption P)

/-- True iff every validation atom passed. -/
def allAssumptionsPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of assumption validation. -/
structure AssumptionSummary where
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Summary API for assumption validation. -/
def runAssumptionValidation (P : Params) (hs : List Assumption) : AssumptionSummary :=
  let rs := validateAssumptions P hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-- Soundness of the summary: if all passed, every listed assumption holds. -/
theorem runAssumptionValidation_sound (P : Params) (hs : List Assumption)
    (hAll : (runAssumptionValidation P hs).allPassed = true) :
    ∀ h ∈ hs, h.Holds P := by
  intro h hMem
  simp only [runAssumptionValidation, allAssumptionsPassed, validateAssumptions,
    List.all_map, List.all_eq_true, Function.comp] at hAll
  exact validateAssumption_sound P h (hAll h hMem)

/-! ## Derived Safety and Finality Results -/

/-- No conflicting commits: proved from honest quorum intersection and the
honest no-equivocation rule. -/
theorem no_conflicting_commits_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M)
    {s : State} {d₁ d₂ : Decision}
    (hCommitted₁ : Committed M s d₁)
    (hCommitted₂ : Committed M s d₂) :
    ¬ M.conflicts d₁ d₂ := by
  rcases hCommitted₁ with ⟨c₁, hCert₁⟩
  rcases hCommitted₂ with ⟨c₂, hCert₂⟩
  obtain ⟨p, hp₁, hp₂, hHonest⟩ := honest_quorum_intersection a hCert₁ hCert₂
  exact a.honestNoEquivocation hHonest
    (a.certSignaturesGenuine hCert₁ hp₁) (a.certSignaturesGenuine hCert₂ hp₂)

/-- Fork exclusion follows from no-conflicting-commits. -/
theorem fork_exclusion_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M)
    (s : State) :
    ¬ Forked M s := by
  rintro ⟨d₁, d₂, hCommitted₁, hCommitted₂, hConflicts⟩
  exact (no_conflicting_commits_of_assumptions a hCommitted₁ hCommitted₂) hConflicts

/-- Safe-finality corollary: finalized decisions cannot conflict with committed ones. -/
theorem safe_finality_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    {M : Model State Decision Certificate Party}
    (a : Assumptions M)
    {s : State} {d : Decision}
    (hFinalized : Finalized M s d) :
    ∀ d', Committed M s d' → ¬ M.conflicts d d' :=
  fun _ hCommitted => no_conflicting_commits_of_assumptions a hFinalized hCommitted

end QuorumGeometry
end Distributed
