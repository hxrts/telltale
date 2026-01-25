import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.Quotient
import RumpsteakV2.Semantics.Environment

open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Quotient

/-! # RumpsteakV2.Proofs.Safety.Determinism

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

namespace RumpsteakV2.Proofs.Safety.Determinism

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Semantics.Environment

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

  def uniqueBranchLabelsBranchesL : List (Label × LocalTypeR) → Bool
    | [] => true
    | (lbl, cont) :: rest =>
        !(rest.map Prod.fst).contains lbl &&
        uniqueBranchLabelsL cont &&
        uniqueBranchLabelsBranchesL rest
end

/-! ## Unique Branch Labels -/

/-- Helper: extract head/tail facts from uniqueBranchLabelsBranchesL. -/
private theorem uniqueBranchLabelsBranchesL_cons {hd : Label × LocalTypeR}
    {tl : List (Label × LocalTypeR)} (huniq : uniqueBranchLabelsBranchesL (hd :: tl) = true) :
    (tl.map Prod.fst).contains hd.1 = false ∧ uniqueBranchLabelsBranchesL tl = true := by
  -- Unfold only the boolean structure, keeping contains as a Bool.
  have h1 :
      (!(tl.map Prod.fst).contains hd.1 && uniqueBranchLabelsL hd.2) = true ∧
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

private theorem mem_map_fst_of_mem {lbl : Label} {cont : LocalTypeR}
    {branches : List (Label × LocalTypeR)} (hmem : (lbl, cont) ∈ branches) :
    lbl ∈ branches.map Prod.fst := by
  -- Lift pair membership to membership of first components.
  apply List.mem_map.mpr
  exact ⟨(lbl, cont), hmem, rfl⟩

private theorem contains_true_of_mem {lbl : Label} {branches : List (Label × LocalTypeR)}
    (hmem : lbl ∈ branches.map Prod.fst) :
    (branches.map Prod.fst).contains lbl = true := by
  -- contains is true when the label appears in the mapped list.
  rw [List.contains_iff_exists_mem_beq]
  exact ⟨lbl, hmem, beq_self_eq_true lbl⟩

private theorem contains_false_contradiction {lbl : Label} {cont : LocalTypeR}
    {branches : List (Label × LocalTypeR)} (hnodup : (branches.map Prod.fst).contains lbl = false)
    (hmem : (lbl, cont) ∈ branches) : False := by
  -- Membership forces contains = true, contradicting hnodup.
  have hmem_fst : lbl ∈ branches.map Prod.fst := mem_map_fst_of_mem hmem
  have hcontains : (branches.map Prod.fst).contains lbl = true :=
    contains_true_of_mem hmem_fst
  rw [hcontains] at hnodup
  cases hnodup

/-- If branches have unique labels, then membership determines the continuation. -/
theorem mem_branchL_unique_label {lbl : Label} {cont₁ cont₂ : LocalTypeR}
    {branches : List (Label × LocalTypeR)} (huniq : uniqueBranchLabelsBranchesL branches = true)
    (hmem₁ : (lbl, cont₁) ∈ branches) (hmem₂ : (lbl, cont₂) ∈ branches) : cont₁ = cont₂ := by
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

/-- Local step relation (inductive, avoids recursion through substitute).
    A local type steps when it performs a send or receive with matching label. -/
inductive LocalStepRep : LocalTypeR → LocalTypeR → LocalActionR → Prop
  | send {p : String} {bs : List (Label × LocalTypeR)} {lt' : LocalTypeR} {act : LocalActionR}
      (huniq : uniqueBranchLabelsBranchesL bs = true)
      (hp : act.participant = p)
      (hmem : (act.label, lt') ∈ bs) :
      LocalStepRep (.send p bs) lt' act
  | recv {p : String} {bs : List (Label × LocalTypeR)} {lt' : LocalTypeR} {act : LocalActionR}
      (huniq : uniqueBranchLabelsBranchesL bs = true)
      (hp : act.participant = p)
      (hmem : (act.label, lt') ∈ bs) :
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
private abbrev GlobalStepMotive (g : GlobalType) (act : GlobalActionR) (g' : GlobalType)
    (_ : step g act g') : Prop :=
  -- Determinism motive for step recursion.
  g.uniqueBranchLabels = true → ∀ g₂, step g act g₂ → g' = g₂

private abbrev BranchStepMotive (bs : List (Label × GlobalType)) (act : GlobalActionR)
    (bs' : List (Label × GlobalType)) (_ : BranchesStep step bs act bs') : Prop :=
  -- Determinism motive for branch-step recursion.
  uniqueBranchLabelsBranches bs = true → ∀ bs₂, BranchesStep step bs act bs₂ → bs' = bs₂

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

theorem global_step_det {g g₁ g₂ : GlobalType} {act : GlobalActionR}
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

/-! ## Environment Determinism

Environment transitions are deterministic given the same action.
The action uniquely determines which queue/timeout is affected.
-/

private theorem env_step_det_deliver {env env₁ env₂ : EnvConfig} {ch : Channel} {msg : Message}
    {rest₁ rest₂ : List Message}
    (hq₁ : env.queues ch = msg :: rest₁)
    (henv₁ : env₁ = { env with
      queues := fun c => if c == ch then rest₁ else env.queues c
      deliveryCount := env.deliveryCount + 1 })
    (hq₂ : env.queues ch = msg :: rest₂)
    (henv₂ : env₂ = { env with
      queues := fun c => if c == ch then rest₂ else env.queues c
      deliveryCount := env.deliveryCount + 1 }) :
    env₁ = env₂ := by
  -- Queue heads match, so the tails and updates coincide.
  rw [hq₁] at hq₂
  obtain ⟨_, hrest⟩ := List.cons.inj hq₂
  subst hrest henv₁ henv₂
  rfl

private theorem env_step_det_drop {env env₁ env₂ : EnvConfig} {ch : Channel} {msg : Message}
    {rest₁ rest₂ : List Message}
    (hq₁ : env.queues ch = msg :: rest₁)
    (henv₁ : env₁ = { env with queues := fun c => if c == ch then rest₁ else env.queues c })
    (hq₂ : env.queues ch = msg :: rest₂)
    (henv₂ : env₂ = { env with queues := fun c => if c == ch then rest₂ else env.queues c }) :
    env₁ = env₂ := by
  -- Same as deliver but without deliveryCount.
  rw [hq₁] at hq₂
  obtain ⟨_, hrest⟩ := List.cons.inj hq₂
  subst hrest henv₁ henv₂
  rfl

/-- Environment step is deterministic given the same action. -/
theorem env_step_det {env env₁ env₂ : EnvConfig} {act : EnvAction}
    (h₁ : EnvConfigStep env act env₁)
    (h₂ : EnvConfigStep env act env₂) :
    env₁ = env₂ := by
  -- Split on the EnvConfigStep constructors.
  cases h₁ with
  | deliver _ ch msg _ hq₁ henv₁ =>
      cases h₂ with
      | deliver _ _ _ _ hq₂ henv₂ =>
          exact env_step_det_deliver hq₁ henv₁ hq₂ henv₂
  | timeout _ role label _ hhas₁ henv₁ =>
      cases h₂ with
      | timeout _ _ _ _ hhas₂ henv₂ =>
          -- Timeout is a pure update, so equality is by substitution.
          subst henv₁ henv₂
          rfl
  | drop _ ch msg _ hq₁ henv₁ =>
      cases h₂ with
      | drop _ _ _ _ hq₂ henv₂ =>
          exact env_step_det_drop hq₁ henv₁ hq₂ henv₂

/-! ## Configuration Determinism

A configuration combines global type and environment. Determinism follows
from determinism of each component.
-/

/-- Configuration step is deterministic given the same action.

ConfigStep requires uniqueBranchLabels, so we can use global_step_det. -/
theorem config_step_det {c c₁ c₂ : Configuration} {act : GlobalActionR}
    (h₁ : ConfigStep c c₁ act)
    (h₂ : ConfigStep c c₂ act) :
    c₁ = c₂ := by
  obtain ⟨huniq₁, hstep₁, henv₁⟩ := h₁
  obtain ⟨_huniq₂, hstep₂, henv₂⟩ := h₂
  have hg : c₁.globalType = c₂.globalType := global_step_det huniq₁ hstep₁ hstep₂
  have he : c₁.env = c₂.env := henv₁.trans henv₂.symm
  cases c₁; cases c₂
  simp only [Configuration.mk.injEq]
  exact ⟨hg, he⟩

/-! ## Local Type Determinism

For projected local types, transitions are also deterministic.
This follows from global determinism + projection coherence.
-/

/-- Local step is deterministic.
    If a local type steps to two results under the same action, they are equal. -/
theorem local_step_det {lt lt₁ lt₂ : LocalTypeR} {act : LocalActionR}
    (h₁ : LocalStep lt lt₁ act)
    (h₂ : LocalStep lt lt₂ act) :
    lt₁ = lt₂ := by
  unfold LocalStep at h₁ h₂
  induction h₁ with
  | send huniq₁ hp₁ hmem₁ =>
      cases h₂ with
      | send huniq₂ hp₂ hmem₂ =>
          exact mem_branchL_unique_label huniq₁ hmem₁ hmem₂
  | recv huniq₁ hp₁ hmem₁ =>
      cases h₂ with
      | recv huniq₂ hp₂ hmem₂ =>
          exact mem_branchL_unique_label huniq₁ hmem₁ hmem₂
  | mu hstep₁ ih =>
      cases h₂ with
      | mu hstep₂ =>
          exact ih hstep₂

/-! ## Uniqueness of Enabled Actions

While multiple actions may be enabled at a configuration, each enabled
action leads to a unique next state. This is the key property for
predictable execution.
-/

/-- If an action is enabled, it determines a unique next configuration. -/
def UniqueNext (c : Configuration) (act : GlobalActionR) : Prop :=
  ∀ c₁ c₂, ConfigStep c c₁ act → ConfigStep c c₂ act → c₁ = c₂

/-- All enabled actions have unique next states. -/
theorem all_unique_next (c : Configuration) (act : GlobalActionR) :
    UniqueNext c act := by
  intro c₁ c₂ h₁ h₂
  exact config_step_det h₁ h₂

/-! ## Confluence (Weaker Property)

For some applications, we need confluence rather than determinism:
different action sequences may reach the same final state.

This is NOT generally true for MPST—different branch choices lead
to different protocol states. We include the definition for completeness.
-/

/-- Confluence: if c steps to c₁ and c₂ via different actions, they can rejoin. -/
def Confluent (_c c₁ c₂ : Configuration) : Prop :=
  ∃ c₃ acts₁ acts₂,
    ConfigStepStar c₁ c₃ acts₁ ∧
    ConfigStepStar c₂ c₃ acts₂

/-- There is no step from a var type (vars are stuck without enclosing mu). -/
theorem no_step_from_var {x : String} {act : GlobalActionR} {g' : GlobalType} :
    ¬step (.var x) act g' := by
  intro h
  cases h

/-- A configuration with a var global type can only reach itself. -/
theorem var_only_reaches_self {x : String} {env : EnvConfig} {c' : Configuration} {acts : List GlobalActionR}
    (h : ConfigStepStar ⟨.var x, env⟩ c' acts) :
    c' = ⟨.var x, env⟩ := by
  cases h with
  | refl => rfl
  | step hstep _ =>
      -- hstep : ConfigStep ⟨.var x, env⟩ c' act
      -- But there's no step from .var x
      obtain ⟨_, hstep', _⟩ := hstep
      exact absurd hstep' no_step_from_var

/-- MPST is NOT confluent in general (branch choices diverge).

**Proof strategy:** Construct a counterexample protocol where:
1. A branch choice leads to two different configurations c₁ and c₂
2. The branches have incompatible continuations that can never rejoin

Counterexample: `comm A B [(l1, var X), (l2, var Y)]`
- Choosing l1 leads to `.var X` (stuck, no further steps)
- Choosing l2 leads to `.var Y` (stuck, no further steps)
- These configurations can never reach the same state since X ≠ Y

**Note:** We use free vars which are stuck states (no step from .var).
This demonstrates that different branch choices can lead to incompatible states.
-/
private def counter_label1 : Label := ⟨"l1", .unit⟩ -- counterexample label 1
private def counter_label2 : Label := ⟨"l2", .unit⟩ -- counterexample label 2
private def counter_branches : List (Label × GlobalType) :=
  -- Two distinct branches with stuck continuations.
  [(counter_label1, .var "X"), (counter_label2, .var "Y")]
private def counter_protocol : GlobalType := .comm "A" "B" counter_branches -- counterexample comm
private def counter_env : EnvConfig := default -- empty env
private def counter_c0 : Configuration := ⟨counter_protocol, counter_env⟩ -- initial config
private def counter_c1 : Configuration := ⟨.var "X", counter_env⟩ -- branch l1 result
private def counter_c2 : Configuration := ⟨.var "Y", counter_env⟩ -- branch l2 result
private def counter_act1 : GlobalActionR := ⟨"A", "B", counter_label1⟩ -- action for l1
private def counter_act2 : GlobalActionR := ⟨"A", "B", counter_label2⟩ -- action for l2

private theorem counter_mem1 :
    (counter_label1, GlobalType.var "X") ∈ counter_branches := by
  -- Head branch membership.
  simp [counter_branches]

private theorem counter_mem2 :
    (counter_label2, GlobalType.var "Y") ∈ counter_branches := by
  -- Tail branch membership.
  simp [counter_branches]

private theorem counter_step1 : ConfigStep counter_c0 counter_c1 counter_act1 := by
  -- Step selecting label1.
  constructor
  · native_decide
  constructor
  · simpa [counter_c0, counter_c1, counter_protocol, counter_act1] using
      (step.comm_head "A" "B" counter_branches counter_label1 (.var "X") counter_mem1)
  · rfl

private theorem counter_step2 : ConfigStep counter_c0 counter_c2 counter_act2 := by
  -- Step selecting label2.
  constructor
  · native_decide
  constructor
  · simpa [counter_c0, counter_c2, counter_protocol, counter_act2] using
      (step.comm_head "A" "B" counter_branches counter_label2 (.var "Y") counter_mem2)
  · rfl

private theorem counter_act_ne : counter_act1 ≠ counter_act2 := by
  -- Actions differ by label.
  intro h
  have hlabel : counter_label1 = counter_label2 := by
    simpa [counter_act1, counter_act2] using congrArg GlobalActionR.label h
  simp [counter_label1, counter_label2] at hlabel

private theorem counter_c1_ne_c2 : counter_c1 ≠ counter_c2 := by
  -- Distinct var continuations.
  intro h
  have htype : GlobalType.var "X" = GlobalType.var "Y" := by
    simpa [counter_c1, counter_c2] using congrArg Configuration.globalType h
  have hxy : ("X" : String) = "Y" := by
    injection htype
  exact (by decide : ("X" : String) ≠ "Y") hxy

theorem not_confluent_general :
    ¬∀ c c₁ c₂ act₁ act₂,
      ConfigStep c c₁ act₁ → ConfigStep c c₂ act₂ → act₁ ≠ act₂ →
      Confluent c c₁ c₂ := by
  -- Apply the universal claim to the concrete counterexample.
  intro hall
  have hconf :=
    hall counter_c0 counter_c1 counter_c2 counter_act1 counter_act2
      counter_step1 counter_step2 counter_act_ne

  -- Unfold Confluent to get common state
  obtain ⟨c3, acts1, acts2, hreach1, hreach2⟩ := hconf

  -- c1 can only reach itself (var "X" is stuck)
  have heq1 : c3 = counter_c1 := var_only_reaches_self hreach1

  -- c2 can only reach itself (var "Y" is stuck)
  have heq2 : c3 = counter_c2 := var_only_reaches_self hreach2

  -- But c1 ≠ c2, contradiction
  rw [heq1] at heq2
  exact counter_c1_ne_c2 heq2

end RumpsteakV2.Proofs.Safety.Determinism
