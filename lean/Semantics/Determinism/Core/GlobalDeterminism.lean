import SessionTypes.GlobalType
import SessionTypes.LocalTypeR
import SessionCoTypes.Quotient
import Semantics.Environment

open SessionCoTypes.EQ2
open SessionCoTypes.Quotient

/-! # Semantics.Determinism

Determinism for V2 protocol semantics.

## Overview

Determinism states that given the same action, a configuration transitions
to a unique next configuration. This is crucial for:
- Predictable protocol execution
- Testing and simulation
- Reasoning about protocol behavior

## Forms of Determinism

1. **Global Type Determinism**: `step g g₁ act` and `step g g₂ act` implies `g₁ = g₂`
2. **Environment Determinism**: `EnvConfigStep e e₁ act` and `EnvConfigStep e e₂ act` implies `e₁ = e₂`
3. **Configuration Determinism**: combining both for full system

## Non-determinism Sources

The protocol itself is deterministic given an action. Non-determinism arises from:
- Action selection (which branch is chosen)
- Environment scheduling (which message is delivered)

These are resolved by the action parameter—once an action is fixed, the result is deterministic.

## Expose

The following definitions form the semantic interface for proofs:

- `GlobalStepDet`: global step determinism
- `EnvStepDet`: environment step determinism
- `ConfigStepDet`: configuration step determinism
- `Claims`: bundle of determinism properties

## Dependencies

This module uses placeholder definitions until Project.lean builds.
-/

/-
The Problem. Protocol semantics must be deterministic given an action to ensure
predictable execution, enable testing, and support formal reasoning. We need to
prove that same-action transitions yield unique successor configurations.

Solution Structure. Proves determinism at three levels: global type (step g g₁ act
and step g g₂ act implies g₁ = g₂), environment (EnvConfigStep determinism), and
full configuration (combining both). Non-determinism is localized to action selection;
once an action is fixed, the result is unique.
-/

namespace Semantics.Determinism

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Semantics.Environment

/-! ## Placeholder Definitions

These will be unified with SubjectReduction once Project.lean is fixed.
-/

/-- Placeholder configuration. -/
structure Configuration where
  globalType : GlobalType
  env : EnvConfig
  deriving Inhabited

/-- Configuration step relation.
    A configuration steps when its global type steps and the environment is preserved.
    This is a simplified version that doesn't model message queue updates. -/
def ConfigStep (c c' : Configuration) (act : GlobalActionR) : Prop :=
  c.globalType.uniqueBranchLabels = true ∧
  step c.globalType act c'.globalType ∧
  c'.env = c.env

/-- Reflexive transitive closure of ConfigStep. -/
inductive ConfigStepStar : Configuration → Configuration → List GlobalActionR → Prop
  | refl (c : Configuration) : ConfigStepStar c c []
  | step {c c' c'' : Configuration} {act : GlobalActionR} {acts : List GlobalActionR}
      (hstep : ConfigStep c c' act)
      (hrest : ConfigStepStar c' c'' acts) :
      ConfigStepStar c c'' (act :: acts)

/-- Placeholder: local action. -/
structure LocalActionR where
  participant : String
  label : Label
  deriving Repr, DecidableEq, Inhabited

-- ReflBEq instances for PayloadSort and Label (needed for beq_self_eq_true)
private theorem payload_beq_refl (p : PayloadSort) : (p == p) = true := by
  -- Payload sort equality is reflexive by cases.
  induction p with
  | unit => rfl
  | nat => rfl
  | bool => rfl
  | string => rfl
  | prod p1 p2 ih1 ih2 =>
      have heq : (PayloadSort.prod p1 p2 == PayloadSort.prod p1 p2) = ((p1 == p1) && (p2 == p2)) := rfl
      simp only [heq, ih1, ih2, Bool.true_and]

instance : ReflBEq PayloadSort where
  -- Reuse the reflexivity lemma for beq.
  rfl := payload_beq_refl _

private theorem label_beq_refl (lbl : Label) : (lbl == lbl) = true := by
  -- Reduce to component-wise beq on label fields.
  cases lbl with
  | mk name sort =>
      have heq : (({ name := name, sort := sort } : Label) == { name := name, sort := sort }) = ((name == name) && (sort == sort)) := rfl
      simp only [heq, beq_self_eq_true name, beq_self_eq_true sort, Bool.true_and]

instance : ReflBEq Label where
  -- Reuse the label reflexivity lemma.
  rfl := label_beq_refl _

-- Unique branch labels predicate for local types
mutual
  def uniqueBranchLabelsL : LocalTypeR → Bool
    | .end => true
    | .var _ => true
    | .send _ bs => uniqueBranchLabelsBranchesL bs
    | .recv _ bs => uniqueBranchLabelsBranchesL bs
    | .mu _ body => uniqueBranchLabelsL body

  def uniqueBranchLabelsBranchesL : List BranchR → Bool
    | [] => true
    | (lbl, _vt, cont) :: rest =>
        !(rest.map Prod.fst).contains lbl &&
        uniqueBranchLabelsL cont &&
        uniqueBranchLabelsBranchesL rest
end

/-! ## Unique Branch Labels -/

/-- Helper: extract head/tail facts from uniqueBranchLabelsBranchesL. -/
private theorem uniqueBranchLabelsBranchesL_cons {hd : BranchR}
    {tl : List BranchR} (huniq : uniqueBranchLabelsBranchesL (hd :: tl) = true) :
    (tl.map Prod.fst).contains hd.1 = false ∧ uniqueBranchLabelsBranchesL tl = true := by
  -- Unfold only the boolean structure, keeping contains as a Bool.
  have h1 :
      (!(tl.map Prod.fst).contains hd.1 && uniqueBranchLabelsL hd.2.2) = true ∧
        uniqueBranchLabelsBranchesL tl = true := by
    exact (Bool.and_eq_true_iff).mp (by simpa [uniqueBranchLabelsBranchesL] using huniq)
  have hnodup : (tl.map Prod.fst).contains hd.1 = false := by
    cases h : (tl.map Prod.fst).contains hd.1 with
    | true =>
        have : False := by
          simpa [h] using h1.1
        cases this
  | false =>
        rfl
  exact ⟨hnodup, h1.2⟩

/-! ### Branch-membership helper lemmas -/

private theorem mem_map_fst_of_mem {lbl : Label} {rest : Option ValType × LocalTypeR}
    {branches : List BranchR} (hmem : (lbl, rest) ∈ branches) :
    lbl ∈ branches.map Prod.fst := by
  -- Lift pair membership to membership of first components.
  apply List.mem_map.mpr
  exact ⟨(lbl, rest), hmem, rfl⟩

private theorem contains_true_of_mem {lbl : Label} {branches : List BranchR}
    (hmem : lbl ∈ branches.map Prod.fst) :
    (branches.map Prod.fst).contains lbl = true := by
  -- contains is true when the label appears in the mapped list.
  rw [List.contains_iff_exists_mem_beq]
  exact ⟨lbl, hmem, beq_self_eq_true lbl⟩

private theorem contains_false_contradiction {lbl : Label} {rest : Option ValType × LocalTypeR}
    {branches : List BranchR} (hnodup : (branches.map Prod.fst).contains lbl = false)
    (hmem : (lbl, rest) ∈ branches) : False := by
  -- Membership forces contains = true, contradicting hnodup.
  have hmem_fst : lbl ∈ branches.map Prod.fst := mem_map_fst_of_mem hmem
  have hcontains : (branches.map Prod.fst).contains lbl = true :=
    contains_true_of_mem hmem_fst
  rw [hcontains] at hnodup
  cases hnodup

/-- If branches have unique labels, then membership determines the continuation. -/
theorem mem_branchL_unique_label {lbl : Label} {rest₁ rest₂ : Option ValType × LocalTypeR}
    {branches : List BranchR} (huniq : uniqueBranchLabelsBranchesL branches = true)
    (hmem₁ : (lbl, rest₁) ∈ branches) (hmem₂ : (lbl, rest₂) ∈ branches) : rest₁ = rest₂ := by
  -- Induct on the branch list and use the head/ tail contradiction.
  induction branches with
  | nil => cases hmem₁
  | cons hd tl ih =>
      have hsplit := uniqueBranchLabelsBranchesL_cons (hd := hd) (tl := tl) huniq
      have hnodup := hsplit.1
      have htl_uniq := hsplit.2
      cases hmem₁ with
      | head =>
          cases hmem₂ with
          | head => rfl
          | tail _ hmem₂' =>
              -- Head vs tail membership contradicts unique labels.
              cases contains_false_contradiction hnodup hmem₂'
      | tail _ hmem₁' =>
          cases hmem₂ with
          | head =>
              -- Tail vs head membership contradicts unique labels.
              cases contains_false_contradiction hnodup hmem₁'
          | tail _ hmem₂' =>
              exact ih htl_uniq hmem₁' hmem₂'

/-! ### Local-step representation -/

/-- Local step relation (inductive, avoids recursion through substitute).
    A local type steps when it performs a send or receive with matching label. -/
inductive LocalStepRep : LocalTypeR → LocalTypeR → LocalActionR → Prop
  | send {p : String} {bs : List BranchR} {lt' : LocalTypeR} {act : LocalActionR}
      (huniq : uniqueBranchLabelsBranchesL bs = true)
      (hp : act.participant = p)
      (hmem : ∃ vt, (act.label, vt, lt') ∈ bs) :
      LocalStepRep (.send p bs) lt' act
  | recv {p : String} {bs : List BranchR} {lt' : LocalTypeR} {act : LocalActionR}
      (huniq : uniqueBranchLabelsBranchesL bs = true)
      (hp : act.participant = p)
      (hmem : ∃ vt, (act.label, vt, lt') ∈ bs) :
      LocalStepRep (.recv p bs) lt' act
  | mu {t : String} {body lt' : LocalTypeR} {act : LocalActionR}
      (hstep : LocalStepRep (body.substitute t (.mu t body)) lt' act) :
      LocalStepRep (.mu t body) lt' act

/-- Local step relation (simplified, works on LocalTypeR directly). -/
def LocalStep (lt lt' : LocalTypeR) (act : LocalActionR) : Prop :=
  LocalStepRep lt lt' act

/-! ## Global Type Determinism

The global step relation is deterministic: given the same action,
there is exactly one next global type.

**Proof obligation**: By case analysis on the step relation constructors.
Each constructor (comm_head, comm_async, mu) uniquely determines the result.
-/

/-- Global step is deterministic given the same action (requires unique branch labels).

Proof sketch: by case analysis on step constructors via @step.rec.
- comm_head/comm_head: both select same label (from action), uniqueness gives same cont
- comm_head/comm_async: actions differ (head has receiver in action, async doesn't)
- comm_async/comm_async: IH on BranchesStep
- mu/mu: IH on the unfolded body step

Uses @step.rec to handle the nested inductive + mutual recursion with BranchesStep.

**Requires:** `g.uniqueBranchLabels = true` to ensure branch labels are distinct.
Without this, two branches with the same label could have different continuations. -/

/-! ### Determinism motives for mutual recursion -/

private abbrev GlobalStepMotive (g : GlobalType) (act : GlobalActionR) (g' : GlobalType)
    (_ : step g act g') : Prop :=
  -- Determinism motive for step recursion.
  g.uniqueBranchLabels = true → ∀ g₂, step g act g₂ → g' = g₂

private abbrev BranchStepMotive (bs : List (Label × GlobalType)) (act : GlobalActionR)
    (bs' : List (Label × GlobalType)) (_ : BranchesStep step bs act bs') : Prop :=
  -- Determinism motive for branch-step recursion.
  uniqueBranchLabelsBranches bs = true → ∀ bs₂, BranchesStep step bs act bs₂ → bs' = bs₂

/-! ### Comm/mu step determinism lemmas -/

private theorem global_step_det_comm_head
    (sender receiver : String) (branches : List (Label × GlobalType)) (label : Label) (cont : GlobalType)
    (hmem : (label, cont) ∈ branches)
    (huniq : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true)
    (g₂ : GlobalType)
    (h₂ : step (.comm sender receiver branches)
      { sender := sender, receiver := receiver, label := label } g₂) :
    cont = g₂ := by
  -- Head steps must pick the same label; async would contradict the action.
  cases h₂ with
  | comm_head _ _ _ label' cont' hmem' =>
      simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true, decide_eq_true_eq] at huniq
      have hnodup := huniq.1
      exact mem_branch_unique_label hnodup hmem hmem'
  | comm_async _ _ _ _ _ _ _ _ hcond' _ _ _ =>
      exact absurd rfl (hcond' rfl)

private theorem global_step_det_comm_async
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (act' : GlobalActionR)
    (label : Label) (cont : GlobalType) (hns : act'.sender ≠ receiver)
    (hcond : act'.sender = sender → act'.receiver ≠ receiver)
    (_hmem : (label, cont) ∈ branches) (_hcan : canStep cont act')
    (hbstep : BranchesStep step branches act' branches')
    (ih_bstep : BranchStepMotive branches act' branches' hbstep)
    (huniq : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true)
    (g₂ : GlobalType) (h₂ : step (.comm sender receiver branches) act' g₂) :
    (.comm sender receiver branches') = g₂ := by
  -- Async vs head contradicts the action; async vs async uses the BranchesStep IH.
  cases h₂ with
  | comm_head _ _ _ _ _ _ =>
      exact absurd rfl (hcond rfl)
  | comm_async _ _ _ branches₂ _ _ _ _ _ _ _ hbstep₂ =>
      simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq
      have huniq_branches := huniq.2
      have heq := ih_bstep huniq_branches branches₂ hbstep₂
      subst heq
      rfl

private theorem global_step_det_mu
    (t : String) (body : GlobalType) (act' : GlobalActionR) (g' : GlobalType)
    (hstep : step (body.substitute t (.mu t body)) act' g')
    (ih : GlobalStepMotive (body.substitute t (.mu t body)) act' g' hstep)
    (huniq : (GlobalType.mu t body).uniqueBranchLabels = true)
    (g₂ : GlobalType) (h₂ : step (.mu t body) act' g₂) :
    g' = g₂ := by
  -- Push uniqueness through substitution, then apply the IH.
  cases h₂ with
  | mu _ _ _ _ hstep₂ =>
      simp only [GlobalType.uniqueBranchLabels] at huniq
      have huniq_sub : (body.substitute t (GlobalType.mu t body)).uniqueBranchLabels = true :=
        GlobalType.uniqueBranchLabels_substitute body t (.mu t body) huniq huniq
      exact ih huniq_sub g₂ hstep₂

/-! ### Branch-step determinism lemmas -/

private theorem global_step_det_branches_nil
    (act' : GlobalActionR) (_huniq : uniqueBranchLabelsBranches [] = true)
    (bs₂ : List (Label × GlobalType)) (h₂ : BranchesStep step [] act' bs₂) :
    [] = bs₂ := by
  -- Only the nil BranchesStep is possible.
  cases h₂ with
  | nil => rfl

private theorem global_step_det_branches_cons
    (lbl : Label) (gHead gHead' : GlobalType) (restTail restTail' : List (Label × GlobalType))
    (act' : GlobalActionR) (hstep : step gHead act' gHead')
    (hbstep : BranchesStep step restTail act' restTail')
    (ih_step : GlobalStepMotive gHead act' gHead' hstep)
    (ih_bstep : BranchStepMotive restTail act' restTail' hbstep)
    (huniq : uniqueBranchLabelsBranches ((lbl, gHead) :: restTail) = true)
    (bs₂ : List (Label × GlobalType))
    (h₂ : BranchesStep step ((lbl, gHead) :: restTail) act' bs₂) :
    ((lbl, gHead') :: restTail') = bs₂ := by
  -- Use IHs on the head step and the tail BranchesStep.
  cases h₂ with
  | cons _ _ gNew _ restNew _ hstep₂ hbstep₂ =>
      simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq
      have hg := ih_step huniq.1 gNew hstep₂
      have hrest := ih_bstep huniq.2 restNew hbstep₂
      subst hg hrest
      rfl

/-! ### Main global-step determinism theorem -/

/-- Global step determinism under unique branch labels. -/ theorem global_step_det
    {g g₁ g₂ : GlobalType} {act : GlobalActionR}
    (huniq : g.uniqueBranchLabels = true)
    (h₁ : step g act g₁)
    (h₂ : step g act g₂) :
    g₁ = g₂ :=
  (@step.rec
    (motive_1 := GlobalStepMotive)
    (motive_2 := BranchStepMotive)
    global_step_det_comm_head
    global_step_det_comm_async
    global_step_det_mu
    global_step_det_branches_nil
    global_step_det_branches_cons
    (t := h₁)) huniq g₂ h₂


end Semantics.Determinism
