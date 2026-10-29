import Distributed.Families.QuorumGeometry.Core

set_option autoImplicit false

/-! # Distributed.Families.Reconfiguration

Reconfiguration safety derived from a concrete joint-consensus model:
- each epoch `e` has a validator set `config e` and a quorum size `quorum e`,
- a commit step appends an entry certified by a quorum of the current epoch,
- a reconfiguration step advances the epoch and keeps the committed log,
- at most `f` validators are Byzantine; honest validators never sign two
  conflicting decisions,
- same-epoch threshold `|config e| + f < 2 * quorum e` and joint-consensus
  overlap `|config e ∪ config (e+1)| + f < quorum e + quorum (e+1)`.

From these we prove (not assume) that commits certified in the same or
adjacent epochs never conflict, that a step preserves the committed prefix,
and that liveness (an honest quorum in the current epoch) is preserved.
-/

/-
The Problem. Earlier versions stored `overlapSignerExcludesConflict` and
`handoffPreservesCommittedPrefix` fields that were the conclusions.
Solution Structure. Fix a concrete state (epoch + certified log) and step
relation, state numeric per-epoch thresholds, and prove safety by counting
via `QuorumGeometry.inter_card_lower`.
-/

/-! ## Core Development -/

namespace Distributed
namespace Reconfiguration

universe v w x

/-- One committed log entry: the certifying epoch, the decision, its certificate. -/
structure Entry (Decision : Type v) (Certificate : Type w) where
  epoch : Nat
  decision : Decision
  cert : Certificate

/-- Concrete replicated state: current epoch and committed log. -/
structure RState (Decision : Type v) (Certificate : Type w) where
  epoch : Nat
  log : List (Entry Decision Certificate)

/-- Reconfiguration model: per-epoch configurations and signature semantics.
`signed p d` means validator `p` signed decision `d` at some point. -/
structure Model (Decision : Type v) (Certificate : Type w) (Party : Type x) where
  config : Nat → Finset Party
  quorum : Nat → Nat
  signers : Certificate → Finset Party
  signed : Party → Decision → Prop
  conflicts : Decision → Decision → Prop

variable {Decision : Type v} {Certificate : Type w} {Party : Type x}

/-- `c` is a valid quorum certificate for `d` in epoch `e`. -/
def Model.ValidCert (M : Model Decision Certificate Party)
    (e : Nat) (d : Decision) (c : Certificate) : Prop :=
  M.signers c ⊆ M.config e ∧ M.quorum e ≤ (M.signers c).card ∧
    ∀ p ∈ M.signers c, M.signed p d

/-- Protocol steps: certified commit in the current epoch, or reconfiguration. -/
inductive Step (M : Model Decision Certificate Party) :
    RState Decision Certificate → RState Decision Certificate → Prop
  | commit (s : RState Decision Certificate) (d : Decision) (c : Certificate) :
      M.ValidCert s.epoch d c → Step M s ⟨s.epoch, s.log ++ [⟨s.epoch, d, c⟩]⟩
  | reconfigure (s : RState Decision Certificate) :
      Step M s ⟨s.epoch + 1, s.log⟩

/-- Initial state: epoch 0, empty log. -/
def initState : RState Decision Certificate := ⟨0, []⟩

/-- States reachable from `initState`. -/
inductive Reachable (M : Model Decision Certificate Party) :
    RState Decision Certificate → Prop
  | init : Reachable M initState
  | step {s s'} : Reachable M s → Step M s s' → Reachable M s'

/-- `d` is committed at `s`. -/
def Committed (s : RState Decision Certificate) (d : Decision) : Prop :=
  ∃ en ∈ s.log, en.decision = d

/-- `d` is committed at `s` by an entry certified in epoch `e`. -/
def CommittedAt (s : RState Decision Certificate) (e : Nat) (d : Decision) : Prop :=
  ∃ en ∈ s.log, en.epoch = e ∧ en.decision = d

/-- Two epochs are equal or adjacent (one reconfiguration apart). -/
def Adjacent (e e' : Nat) : Prop := e ≤ e' + 1 ∧ e' ≤ e + 1

/-! ## Assumptions -/

/-- Fault model. No field mentions commits or steps: all are numeric
per-epoch thresholds or the per-validator honesty rule. -/
structure Assumptions [DecidableEq Party] (M : Model Decision Certificate Party) where
  byzantine : Finset Party
  f : Nat
  byzantineBound : byzantine.card ≤ f
  sameEpochThreshold : ∀ e, (M.config e).card + f < 2 * M.quorum e
  jointOverlap : ∀ e,
    (M.config e ∪ M.config (e + 1)).card + f < M.quorum e + M.quorum (e + 1)
  honestNoEquivocation :
    ∀ {p d₁ d₂}, p ∉ byzantine → M.signed p d₁ → M.signed p d₂ → ¬ M.conflicts d₁ d₂
  honestQuorumAvailable : ∀ e, M.quorum e ≤ (M.config e \ byzantine).card

/-- Liveness of a state: honest members of the current epoch form a quorum. -/
def Live [DecidableEq Party] (M : Model Decision Certificate Party)
    (byz : Finset Party) (s : RState Decision Certificate) : Prop :=
  M.quorum s.epoch ≤ (M.config s.epoch \ byz).card

/-! ## Properties -/

/-- No split brain: across a step from a reachable state, decisions certified
in the same or adjacent epochs never conflict. -/
def NoSplitBrainAcrossReconfiguration (M : Model Decision Certificate Party) : Prop :=
  ∀ {sOld sNew e e' dOld dNew},
    Reachable M sOld → Step M sOld sNew →
    CommittedAt sOld e dOld → CommittedAt sNew e' dNew → Adjacent e e' →
    ¬ M.conflicts dOld dNew

/-- Safe handoff: the committed log of the old state is a prefix of the new one. -/
def SafeHandoff (M : Model Decision Certificate Party) : Prop :=
  ∀ {sOld sNew}, Step M sOld sNew → sOld.log <+: sNew.log

/-- Liveness preservation across one step. -/
def LivenessPreserved [DecidableEq Party] (M : Model Decision Certificate Party)
    (byz : Finset Party) : Prop :=
  ∀ {sOld sNew}, Step M sOld sNew → Live M byz sOld → Live M byz sNew

/-! ## Counting -/

/-- Two sets inside `V` whose sizes exceed `|V| + |Byz|` share an honest member. -/
theorem honest_common {P : Type x} [DecidableEq P] (A B V Byz : Finset P)
    (hA : A ⊆ V) (hB : B ⊆ V) (h : V.card + Byz.card < A.card + B.card) :
    ∃ p, p ∈ A ∧ p ∈ B ∧ p ∉ Byz := by
  have hI := QuorumGeometry.inter_card_lower A B V hA hB
  have hSd := Finset.le_card_sdiff Byz (A ∩ B)
  obtain ⟨p, hp⟩ : ((A ∩ B) \ Byz).Nonempty := by
    rw [← Finset.card_pos]; omega
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hp
  exact ⟨p, hp.1.1, hp.1.2, hp.2⟩

/-- Valid certificates in epochs `e` and `e+1` share an honest signer. -/
theorem honest_signer_joint [DecidableEq Party] {M : Model Decision Certificate Party}
    (a : Assumptions M) {e d d' c c'}
    (h : M.ValidCert e d c) (h' : M.ValidCert (e + 1) d' c') :
    ∃ p, p ∈ M.signers c ∧ p ∈ M.signers c' ∧ p ∉ a.byzantine := by
  have := a.jointOverlap e; have := a.byzantineBound; have := h.2.1; have := h'.2.1
  exact honest_common _ _ _ _ (h.1.trans Finset.subset_union_left)
    (h'.1.trans Finset.subset_union_right) (by omega)

/-- Valid certificates in the same epoch share an honest signer. -/
theorem honest_signer_same [DecidableEq Party] {M : Model Decision Certificate Party}
    (a : Assumptions M) {e d d' c c'}
    (h : M.ValidCert e d c) (h' : M.ValidCert e d' c') :
    ∃ p, p ∈ M.signers c ∧ p ∈ M.signers c' ∧ p ∉ a.byzantine := by
  have := a.sameEpochThreshold e; have := a.byzantineBound; have := h.2.1; have := h'.2.1
  exact honest_common _ _ _ _ h.1 h'.1 (by omega)

/-- A shared honest signer excludes a conflict (honesty rule). -/
theorem no_conflict_of_honest [DecidableEq Party] {M : Model Decision Certificate Party}
    (a : Assumptions M) {e e' d d' c c'}
    (h : M.ValidCert e d c) (h' : M.ValidCert e' d' c')
    (hp : ∃ p, p ∈ M.signers c ∧ p ∈ M.signers c' ∧ p ∉ a.byzantine) :
    ¬ M.conflicts d d' := by
  obtain ⟨p, hp, hp', hH⟩ := hp
  exact a.honestNoEquivocation hH (h.2.2 p hp) (h'.2.2 p hp')

/-- Valid certificates in adjacent epochs never certify conflicting decisions. -/
theorem valid_certs_no_conflict [DecidableEq Party] {M : Model Decision Certificate Party}
    (a : Assumptions M) {e e' d d' c c'}
    (h : M.ValidCert e d c) (h' : M.ValidCert e' d' c') (hAdj : Adjacent e e') :
    ¬ M.conflicts d d' := by
  apply no_conflict_of_honest a h h'
  rcases Nat.lt_trichotomy e e' with hlt | rfl | hgt
  · obtain rfl : e' = e + 1 := by unfold Adjacent at hAdj; omega
    exact honest_signer_joint a h h'
  · exact honest_signer_same a h h'
  · obtain rfl : e = e' + 1 := by unfold Adjacent at hAdj; omega
    obtain ⟨p, h1, h2, h3⟩ := honest_signer_joint a h' h
    exact ⟨p, h2, h1, h3⟩

/-! ## Step Invariants -/

/-- Every log entry carries a valid certificate for its epoch. -/
def WellCertified (M : Model Decision Certificate Party)
    (s : RState Decision Certificate) : Prop :=
  ∀ en ∈ s.log, M.ValidCert en.epoch en.decision en.cert

/-- Steps only append to the log. -/
theorem step_log_prefix {M : Model Decision Certificate Party} {s s'}
    (h : Step M s s') : s.log <+: s'.log := by
  cases h with
  | commit _ _ _ => exact List.prefix_append _ _
  | reconfigure => exact List.prefix_refl _

/-- Steps preserve `WellCertified`. -/
theorem step_wellCertified {M : Model Decision Certificate Party} {s s'}
    (h : Step M s s') (hW : WellCertified M s) : WellCertified M s' := by
  cases h with
  | commit d c hc =>
    intro en hen
    rcases List.mem_append.1 hen with hen | hen
    · exact hW en hen
    · rw [List.mem_singleton.1 hen]; exact hc
  | reconfigure => exact hW

/-- Reachable states are well certified. -/
theorem reachable_wellCertified {M : Model Decision Certificate Party} {s}
    (h : Reachable M s) : WellCertified M s := by
  induction h with
  | init => intro en hen; simp [initState] at hen
  | step _ hs ih => exact step_wellCertified hs ih

/-! ## Derived Results -/

/-- No split brain, proved from the joint-consensus thresholds and honesty. -/
theorem no_split_brain_of_assumptions [DecidableEq Party]
    {M : Model Decision Certificate Party} (a : Assumptions M) :
    NoSplitBrainAcrossReconfiguration M := by
  intro sOld sNew e e' dOld dNew hR hStep hOld hNew hAdj
  have hW' := reachable_wellCertified (Reachable.step hR hStep)
  obtain ⟨en, hen, rfl, rfl⟩ := hOld
  obtain ⟨en', hen', rfl, rfl⟩ := hNew
  exact valid_certs_no_conflict a (hW' en ((step_log_prefix hStep).subset hen))
    (hW' en' hen') hAdj

/-- Safe handoff (committed-prefix preservation), proved from the step relation. -/
theorem safe_handoff (M : Model Decision Certificate Party) : SafeHandoff M :=
  fun h => step_log_prefix h

/-- Committed decisions remain committed across a step. -/
theorem committed_preserved {M : Model Decision Certificate Party} {s s' d}
    (h : Step M s s') (hc : Committed s d) : Committed s' d := by
  obtain ⟨en, hen, hd⟩ := hc
  exact ⟨en, (step_log_prefix h).subset hen, hd⟩

/-- Liveness preservation, proved from per-epoch honest-quorum availability. -/
theorem liveness_preserved_of_assumptions [DecidableEq Party]
    {M : Model Decision Certificate Party} (a : Assumptions M) :
    LivenessPreserved M a.byzantine := by
  intro sOld sNew _ _
  exact a.honestQuorumAvailable sNew.epoch

/-! ## Assumption Validation API -/

/-- Assumption labels checkable over a finite epoch horizon. -/
inductive Assumption where
  | sameEpochThreshold
  | jointOverlap
  | honestQuorumAvailable
  deriving Repr, DecidableEq, Inhabited

/-- Proposition named by each label for epochs `< horizon`. -/
def Assumption.Holds [DecidableEq Party] (M : Model Decision Certificate Party)
    (byz : Finset Party) (f horizon : Nat) : Assumption → Prop
  | .sameEpochThreshold => ∀ e < horizon, (M.config e).card + f < 2 * M.quorum e
  | .jointOverlap => ∀ e < horizon,
      (M.config e ∪ M.config (e + 1)).card + f < M.quorum e + M.quorum (e + 1)
  | .honestQuorumAvailable => ∀ e < horizon, M.quorum e ≤ (M.config e \ byz).card

instance [DecidableEq Party] (M : Model Decision Certificate Party) (byz : Finset Party)
    (f horizon : Nat) (h : Assumption) : Decidable (h.Holds M byz f horizon) := by
  cases h <;> unfold Assumption.Holds <;> infer_instance

/-- Core assumption labels. -/
def coreAssumptions : List Assumption :=
  [.sameEpochThreshold, .jointOverlap, .honestQuorumAvailable]

/-- Decide one label over the concrete configuration schedule. -/
def validateAssumption [DecidableEq Party] (M : Model Decision Certificate Party)
    (byz : Finset Party) (f horizon : Nat) (h : Assumption) : Bool :=
  decide (h.Holds M byz f horizon)

/-- Soundness of the decision procedure. -/
theorem validateAssumption_sound [DecidableEq Party] (M : Model Decision Certificate Party)
    (byz : Finset Party) (f horizon : Nat) (h : Assumption)
    (hPass : validateAssumption M byz f horizon h = true) : h.Holds M byz f horizon :=
  of_decide_eq_true hPass

/-- Validate all labels in a list. -/
def runAssumptionValidation [DecidableEq Party] (M : Model Decision Certificate Party)
    (byz : Finset Party) (f horizon : Nat) (hs : List Assumption) : Bool :=
  hs.all (validateAssumption M byz f horizon)

/-- Soundness of the list validation. -/
theorem runAssumptionValidation_sound [DecidableEq Party]
    (M : Model Decision Certificate Party) (byz : Finset Party) (f horizon : Nat)
    (hs : List Assumption) (hAll : runAssumptionValidation M byz f horizon hs = true) :
    ∀ h ∈ hs, h.Holds M byz f horizon := by
  intro h hMem
  exact validateAssumption_sound M byz f horizon h (List.all_eq_true.1 hAll h hMem)

end Reconfiguration
end Distributed
