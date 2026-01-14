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
  induction p with
  | unit => rfl
  | nat => rfl
  | bool => rfl
  | string => rfl
  | prod p1 p2 ih1 ih2 =>
      have heq : (PayloadSort.prod p1 p2 == PayloadSort.prod p1 p2) = ((p1 == p1) && (p2 == p2)) := rfl
      simp only [heq, ih1, ih2, Bool.true_and]

instance : ReflBEq PayloadSort where
  rfl := payload_beq_refl _

private theorem label_beq_refl (lbl : Label) : (lbl == lbl) = true := by
  cases lbl with
  | mk name sort =>
      have heq : (({ name := name, sort := sort } : Label) == { name := name, sort := sort }) = ((name == name) && (sort == sort)) := rfl
      simp only [heq, beq_self_eq_true name, beq_self_eq_true sort, Bool.true_and]

instance : ReflBEq Label where
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

/-- If branches have unique labels, then membership determines the continuation. -/
theorem mem_branchL_unique_label {lbl : Label} {cont₁ cont₂ : LocalTypeR}
    {branches : List (Label × LocalTypeR)}
    (huniq : uniqueBranchLabelsBranchesL branches = true)
    (hmem₁ : (lbl, cont₁) ∈ branches)
    (hmem₂ : (lbl, cont₂) ∈ branches) :
    cont₁ = cont₂ := by
  induction branches with
  | nil => cases hmem₁
  | cons hd tl ih =>
      -- uniqueBranchLabelsBranchesL (hd :: tl) =
      --   !(tl.map Prod.fst).contains hd.1 && uniqueBranchLabelsL hd.2 && uniqueBranchLabelsBranchesL tl
      simp only [uniqueBranchLabelsBranchesL] at huniq
      -- Structure: ((!A && B) && C) = true
      have hand1 := Bool.and_eq_true_iff.mp huniq
      -- hand1.1 : !A && B = true
      -- hand1.2 : C = true (uniqueBranchLabelsBranchesL tl)
      have hand2 := Bool.and_eq_true_iff.mp hand1.1
      -- hand2.1 : !A = true
      -- hand2.2 : B = true
      have hnodup : (tl.map Prod.fst).contains hd.1 = false := by
        simp only [Bool.not_eq_true'] at hand2
        exact hand2.1
      have htl_uniq : uniqueBranchLabelsBranchesL tl = true := hand1.2
      cases hmem₁ with
      | head =>
          cases hmem₂ with
          | head => rfl
          | tail _ hmem₂' =>
              -- lbl = hd.1 is in tl, contradicting hnodup
              -- hmem₂' : (lbl, cont₂) ∈ tl, so lbl ∈ tl.map Prod.fst
              have hmem_fst : lbl ∈ tl.map Prod.fst := by
                apply List.mem_map.mpr
                exact ⟨(lbl, cont₂), hmem₂', rfl⟩
              have hcontains : (tl.map Prod.fst).contains lbl = true := by
                rw [List.contains_iff_exists_mem_beq]
                exact ⟨lbl, hmem_fst, beq_self_eq_true lbl⟩
              rw [hcontains] at hnodup
              cases hnodup
      | tail _ hmem₁' =>
          cases hmem₂ with
          | head =>
              -- lbl = hd.1 is in tl (via hmem₁'), contradicting hnodup
              have hmem_fst : lbl ∈ tl.map Prod.fst := by
                apply List.mem_map.mpr
                exact ⟨(lbl, cont₁), hmem₁', rfl⟩
              have hcontains : (tl.map Prod.fst).contains lbl = true := by
                rw [List.contains_iff_exists_mem_beq]
                exact ⟨lbl, hmem_fst, beq_self_eq_true lbl⟩
              rw [hcontains] at hnodup
              cases hnodup
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
theorem global_step_det {g g₁ g₂ : GlobalType} {act : GlobalActionR}
    (huniq : g.uniqueBranchLabels = true)
    (h₁ : step g act g₁)
    (h₂ : step g act g₂) :
    g₁ = g₂ :=
  (@step.rec
    (motive_1 := fun g act g' _ => g.uniqueBranchLabels = true → ∀ g₂, step g act g₂ → g' = g₂)
    (motive_2 := fun bs act bs' _ => uniqueBranchLabelsBranches bs = true → ∀ bs₂, BranchesStep step bs act bs₂ → bs' = bs₂)
    -- Case 1: comm_head
    (fun sender receiver branches label cont (hmem : (label, cont) ∈ branches)
        (huniq : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true)
        (g₂ : GlobalType) (h₂ : step (.comm sender receiver branches)
          { sender := sender, receiver := receiver, label := label } g₂) => by
      cases h₂ with
      | comm_head _ _ _ label' cont' hmem' =>
          -- Both comm_head with same action, so label = label'
          simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true, decide_eq_true_eq] at huniq
          have hnodup := huniq.1
          exact mem_branch_unique_label hnodup hmem hmem'
      | comm_async _ _ _ _ _ _ _ _ hcond' _ _ _ =>
          exact absurd rfl (hcond' rfl))
    -- Case 2: comm_async
    (fun sender receiver branches branches' act' label cont hns hcond hmem hcan
        (_hbstep : BranchesStep step branches act' branches')
        (ih_bstep : uniqueBranchLabelsBranches branches = true → ∀ bs₂, BranchesStep step branches act' bs₂ → branches' = bs₂)
        (huniq : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true)
        (g₂ : GlobalType) (h₂ : step (.comm sender receiver branches) act' g₂) => by
      cases h₂ with
      | comm_head _ _ _ _ _ _ =>
          exact absurd rfl (hcond rfl)
      | comm_async _ _ _ branches₂ _ _ _ _ _ _ _ hbstep₂ =>
          simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq
          have huniq_branches := huniq.2
          have heq := ih_bstep huniq_branches branches₂ hbstep₂
          subst heq
          rfl)
    -- Case 3: mu
    (fun t body act' g' (_hstep : step (body.substitute t (.mu t body)) act' g')
        (ih : (body.substitute t (.mu t body)).uniqueBranchLabels = true → ∀ g₂, step (body.substitute t (.mu t body)) act' g₂ → g' = g₂)
        (huniq : (GlobalType.mu t body).uniqueBranchLabels = true)
        (g₂ : GlobalType) (h₂ : step (.mu t body) act' g₂) => by
      cases h₂ with
      | mu _ _ _ _ hstep₂ =>
          -- uniqueBranchLabels preserved through substitution
          simp only [GlobalType.uniqueBranchLabels] at huniq
          have huniq_sub : (body.substitute t (GlobalType.mu t body)).uniqueBranchLabels = true :=
            GlobalType.uniqueBranchLabels_substitute body t (.mu t body) huniq huniq
          exact ih huniq_sub g₂ hstep₂)
    -- Case 4: BranchesStep.nil
    (fun act' (huniq : uniqueBranchLabelsBranches [] = true)
        (bs₂ : List (Label × GlobalType))
        (h₂ : BranchesStep step [] act' bs₂) => by
      cases h₂ with
      | nil => rfl)
    -- Case 5: BranchesStep.cons
    (fun lbl gHead gHead' restTail restTail' act'
        (_hstep : step gHead act' gHead')
        (_hbstep : BranchesStep step restTail act' restTail')
        (ih_step : gHead.uniqueBranchLabels = true → ∀ g₂, step gHead act' g₂ → gHead' = g₂)
        (ih_bstep : uniqueBranchLabelsBranches restTail = true → ∀ bs₂, BranchesStep step restTail act' bs₂ → restTail' = bs₂)
        (huniq : uniqueBranchLabelsBranches ((lbl, gHead) :: restTail) = true)
        (bs₂ : List (Label × GlobalType))
        (h₂ : BranchesStep step ((lbl, gHead) :: restTail) act' bs₂) => by
      cases h₂ with
      | cons _ _ gNew _ restNew _ hstep₂ hbstep₂ =>
          simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq
          have hg := ih_step huniq.1 gNew hstep₂
          have hrest := ih_bstep huniq.2 restNew hbstep₂
          subst hg hrest
          rfl)
    (t := h₁)) huniq g₂ h₂

/-! ## Environment Determinism

Environment transitions are deterministic given the same action.
The action uniquely determines which queue/timeout is affected.
-/

/-- Environment step is deterministic given the same action. -/
theorem env_step_det {env env₁ env₂ : EnvConfig} {act : EnvAction}
    (h₁ : EnvConfigStep env act env₁)
    (h₂ : EnvConfigStep env act env₂) :
    env₁ = env₂ := by
  cases h₁ with
  | deliver _ ch msg _ hq₁ henv₁ =>
      cases h₂ with
      | deliver _ _ _ _ hq₂ henv₂ =>
          -- Both dequeue same message from same channel
          rw [hq₁] at hq₂
          obtain ⟨_, hrest⟩ := List.cons.inj hq₂
          subst henv₁ henv₂ hrest
          rfl
  | timeout _ role label _ hhas₁ henv₁ =>
      cases h₂ with
      | timeout _ _ _ _ hhas₂ henv₂ =>
          subst henv₁ henv₂
          rfl
  | drop _ ch msg _ hq₁ henv₁ =>
      cases h₂ with
      | drop _ _ _ _ hq₂ henv₂ =>
          rw [hq₁] at hq₂
          obtain ⟨_, hrest⟩ := List.cons.inj hq₂
          subst henv₁ henv₂ hrest
          rfl

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
theorem not_confluent_general :
    ¬∀ c c₁ c₂ act₁ act₂,
      ConfigStep c c₁ act₁ → ConfigStep c c₂ act₂ → act₁ ≠ act₂ →
      Confluent c c₁ c₂ := by
  -- Construct counterexample
  let label1 : Label := ⟨"l1", .unit⟩
  let label2 : Label := ⟨"l2", .unit⟩
  let protocol : GlobalType := .comm "A" "B" [(label1, .var "X"), (label2, .var "Y")]
  let env0 : EnvConfig := default
  let c0 : Configuration := ⟨protocol, env0⟩
  let c1 : Configuration := ⟨.var "X", env0⟩
  let c2 : Configuration := ⟨.var "Y", env0⟩
  let act1 : GlobalActionR := ⟨"A", "B", label1⟩
  let act2 : GlobalActionR := ⟨"A", "B", label2⟩

  intro hall

  -- Show ConfigStep c0 c1 act1
  have hmem1 : (label1, GlobalType.var "X") ∈ [(label1, GlobalType.var "X"), (label2, GlobalType.var "Y")] := by
    left

  have hstep1 : ConfigStep c0 c1 act1 := by
    constructor
    · -- uniqueBranchLabels protocol = true
      native_decide
    constructor
    · -- step protocol act1 (.var "X")
      exact step.comm_head "A" "B" _ label1 (.var "X") hmem1
    · -- c1.env = c0.env
      rfl

  -- Show ConfigStep c0 c2 act2
  have hmem2 : (label2, GlobalType.var "Y") ∈ [(label1, GlobalType.var "X"), (label2, GlobalType.var "Y")] := by
    right; left

  have hstep2 : ConfigStep c0 c2 act2 := by
    constructor
    · native_decide
    constructor
    · -- step protocol act2 (.var "Y")
      exact step.comm_head "A" "B" _ label2 (.var "Y") hmem2
    · rfl

  -- Show act1 ≠ act2
  have hneq : act1 ≠ act2 := by
    intro heq
    have hlabel : label1 = label2 := by
      have : act1.label = act2.label := by rw [heq]
      exact this
    simp [label1, label2] at hlabel

  -- Apply universal claim to get confluence
  have hconf := hall c0 c1 c2 act1 act2 hstep1 hstep2 hneq

  -- Unfold Confluent to get common state
  obtain ⟨c3, acts1, acts2, hreach1, hreach2⟩ := hconf

  -- c1 can only reach itself (var "X" is stuck)
  have heq1 : c3 = c1 := var_only_reaches_self hreach1

  -- c2 can only reach itself (var "Y" is stuck)
  have heq2 : c3 = c2 := var_only_reaches_self hreach2

  -- But c1 ≠ c2, contradiction
  rw [heq1] at heq2
  have hneq_configs : c1 ≠ c2 := by
    intro heq
    have hg : c1.globalType = c2.globalType := by rw [heq]
    simp [c1, c2] at hg
  exact hneq_configs heq2

/-! ## Diamond Property for Independent Actions

For independent actions (different sender-receiver pairs), we do have
a diamond property: they commute.
-/

/-- Two actions are independent if they involve disjoint role pairs. -/
def IndependentActions (act₁ act₂ : GlobalActionR) : Prop :=
  act₁.sender ≠ act₂.sender ∧
  act₁.sender ≠ act₂.receiver ∧
  act₁.receiver ≠ act₂.sender ∧
  act₁.receiver ≠ act₂.receiver

/-- Independent actions can't both be comm_head for the same communication.
    If act₁ = {s, r, l₁} and act₂ = {s, r, l₂}, then sender₁ = sender₂, violating independence. -/
theorem independent_not_both_head {act₁ act₂ : GlobalActionR} {s r : String}
    (hind : IndependentActions act₁ act₂)
    (h₁ : act₁.sender = s ∧ act₁.receiver = r)
    (h₂ : act₂.sender = s ∧ act₂.receiver = r) : False := by
  have hs : act₁.sender = act₂.sender := h₁.1.trans h₂.1.symm
  exact hind.1 hs

/-- IndependentActions is symmetric. -/
theorem IndependentActions.symm {act₁ act₂ : GlobalActionR}
    (h : IndependentActions act₁ act₂) : IndependentActions act₂ act₁ :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

/-- The diamond property result is symmetric in act₁/act₂.
    This allows us to prove only one direction of asymmetric cases. -/
theorem step_diamond_symm {g g₁ g₂ g₃ : GlobalType} {act₁ act₂ : GlobalActionR}
    (h : step g₁ act₂ g₃ ∧ step g₂ act₁ g₃) :
    step g₂ act₁ g₃ ∧ step g₁ act₂ g₃ :=
  ⟨h.2, h.1⟩

/-- BranchesStep preserves membership: if (l, g) ∈ bs and BranchesStep bs act bs',
    then there exists g' such that step g act g' and (l, g') ∈ bs'. -/
theorem BranchesStep_mem {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    {l : Label} {g : GlobalType}
    (hbs : BranchesStep step bs act bs')
    (hmem : (l, g) ∈ bs) :
    ∃ g', step g act g' ∧ (l, g') ∈ bs' := by
  induction hbs with
  | nil => cases hmem
  | cons label head head' rest rest' _ hhead hrest ih =>
      cases hmem with
      | head =>
          -- (l, g) is the head of the list, l = label, g = head
          exact ⟨head', hhead, .head _⟩
      | tail _ hmem' =>
          -- (l, g) is in the rest
          obtain ⟨g', hstep, hmem''⟩ := ih hmem'
          exact ⟨g', hstep, .tail _ hmem''⟩

/-- Inverse of BranchesStep_mem: if (l, g') ∈ bs' after BranchesStep bs act bs',
    then there exists g such that (l, g) ∈ bs and step g act g'. -/
theorem BranchesStep_mem_inv {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    {l : Label} {g' : GlobalType}
    (hbs : BranchesStep step bs act bs')
    (hmem : (l, g') ∈ bs') :
    ∃ g, step g act g' ∧ (l, g) ∈ bs := by
  induction hbs with
  | nil => cases hmem
  | cons label head head' rest rest' _ hhead hrest ih =>
      cases hmem with
      | head =>
          exact ⟨head, hhead, .head _⟩
      | tail _ hmem' =>
          obtain ⟨g, hstep, hmem''⟩ := ih hmem'
          exact ⟨g, hstep, .tail _ hmem''⟩

/-- BranchesStep matches the length and labels of the input list. -/
theorem BranchesStep_labels {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    (hbs : BranchesStep step bs act bs') :
    bs.map Prod.fst = bs'.map Prod.fst := by
  induction hbs with
  | nil => rfl
  | cons label _ _ _ _ _ _ _ ih =>
      simp only [List.map_cons]
      rw [ih]

/-- canStep for an action on a type requires the action to be enabled somewhere in the type. -/
theorem canStep_comm_head {s r : String} {branches : List (Label × GlobalType)}
    {l : Label} {cont : GlobalType}
    (hmem : (l, cont) ∈ branches) :
    canStep (.comm s r branches) { sender := s, receiver := r, label := l } := by
  exact canStep.comm_head s r branches l cont hmem


/-- uniqueBranchLabelsBranches implies each continuation has uniqueBranchLabels. -/
theorem uniqueBranchLabelsBranches_mem {branches : List (Label × GlobalType)} {lbl : Label} {g : GlobalType}
    (huniq : uniqueBranchLabelsBranches branches = true)
    (hmem : (lbl, g) ∈ branches) :
    g.uniqueBranchLabels = true := by
  induction branches with
  | nil => cases hmem
  | cons hd tl ih =>
      simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq
      cases hmem with
      | head => exact huniq.1
      | tail _ hmem' => exact ih huniq.2 hmem'

/-- BranchesStep preserves uniqueBranchLabelsBranches. -/
theorem BranchesStep_preserves_uniqueBranchLabelsBranches {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    (huniq : uniqueBranchLabelsBranches bs = true)
    (hbs : BranchesStep step bs act bs')
    (ih : ∀ g g', g.uniqueBranchLabels = true → step g act g' → g'.uniqueBranchLabels = true) :
    uniqueBranchLabelsBranches bs' = true := by
  induction hbs with
  | nil => rfl
  | cons lbl head head' rest rest' _ hhead hrest ih_rest =>
      simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq ⊢
      constructor
      · exact ih head head' huniq.1 hhead
      · exact ih_rest huniq.2 ih

/-- BranchesStep preserves branchLabels (the list of labels doesn't change). -/
theorem BranchesStep_preserves_branchLabels {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    (hbs : BranchesStep step bs act bs') :
    branchLabels bs' = branchLabels bs := by
  induction hbs with
  | nil => rfl
  | cons lbl _ _ _ _ _ _ _ ih =>
      unfold branchLabels at *
      simp only [List.map_cons]
      rw [ih]

/-- uniqueBranchLabels is preserved by step.
    This is needed for the diamond property to maintain well-formedness.

    **Note:** This proof uses @step.rec for the nested induction. The structure
    mirrors global_step_det but with uniqueBranchLabels preservation as the goal.
    The key insight is that:
    - comm_head: continuation inherits uniqueness from branch list
    - comm_async: BranchesStep preserves labels (so Nodup is preserved) and
                  each branch continuation preserves uniqueness by IH
    - mu: substitution preserves uniqueness, then apply IH
-/
theorem uniqueBranchLabels_preserved_by_step {g g' : GlobalType} {act : GlobalActionR}
    (huniq : g.uniqueBranchLabels = true)
    (hstep : step g act g') :
    g'.uniqueBranchLabels = true :=
  (@step.rec
    (motive_1 := fun g act g' _ => g.uniqueBranchLabels = true → g'.uniqueBranchLabels = true)
    (motive_2 := fun bs act bs' _ => uniqueBranchLabelsBranches bs = true →
                   uniqueBranchLabelsBranches bs' = true ∧ branchLabels bs' = branchLabels bs)
    -- Case 1: comm_head
    (fun sender receiver branches label cont hmem
        (huniq : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true) => by
      simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq
      exact uniqueBranchLabelsBranches_mem huniq.2 hmem)
    -- Case 2: comm_async
    (fun sender receiver branches branches' act' label cont hns hcond hmem hcan
        (_hbs : BranchesStep step branches act' branches')
        (ih_bs : uniqueBranchLabelsBranches branches = true →
                 uniqueBranchLabelsBranches branches' = true ∧ branchLabels branches' = branchLabels branches)
        (huniq : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true) => by
      simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq ⊢
      obtain ⟨huniq_bs', hlabels⟩ := ih_bs huniq.2
      constructor
      · rw [hlabels]; exact huniq.1
      · exact huniq_bs')
    -- Case 3: mu
    (fun t body act' g'' (_hstep : step (body.substitute t (.mu t body)) act' g'')
        (ih : (body.substitute t (.mu t body)).uniqueBranchLabels = true → g''.uniqueBranchLabels = true)
        (huniq : (GlobalType.mu t body).uniqueBranchLabels = true) => by
      simp only [GlobalType.uniqueBranchLabels] at huniq
      have huniq_sub : (body.substitute t (GlobalType.mu t body)).uniqueBranchLabels = true :=
        GlobalType.uniqueBranchLabels_substitute body t (.mu t body) huniq huniq
      exact ih huniq_sub)
    -- Case 4: BranchesStep.nil
    (fun act' (_huniq : uniqueBranchLabelsBranches [] = true) =>
      ⟨rfl, rfl⟩)
    -- Case 5: BranchesStep.cons
    (fun lbl gHead gHead' restTail restTail' act'
        (_hstep : step gHead act' gHead')
        (_hbstep : BranchesStep step restTail act' restTail')
        (ih_step : gHead.uniqueBranchLabels = true → gHead'.uniqueBranchLabels = true)
        (ih_bstep : uniqueBranchLabelsBranches restTail = true →
                    uniqueBranchLabelsBranches restTail' = true ∧ branchLabels restTail' = branchLabels restTail)
        (huniq : uniqueBranchLabelsBranches ((lbl, gHead) :: restTail) = true) => by
      simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq ⊢
      unfold branchLabels at *
      simp only [List.map_cons]
      obtain ⟨huniq_rest, hlabels_rest⟩ := ih_bstep huniq.2
      constructor
      · exact ⟨ih_step huniq.1, huniq_rest⟩
      · rw [hlabels_rest])
    (t := hstep)) huniq

/-- Every step corresponds to a canStep. -/
theorem step_implies_canStep {g g' : GlobalType} {act : GlobalActionR}
    (h : step g act g') : canStep g act :=
  match h with
  | .comm_head sender receiver branches label cont hmem =>
      canStep.comm_head sender receiver branches label cont hmem
  | .comm_async sender receiver branches branches' act' label cont hns hcond hmem hcan _ =>
      canStep.comm_async sender receiver branches act' label cont hns hcond hmem hcan
  | .mu t body act' g'' hstep' =>
      canStep.mu t body act' (step_implies_canStep hstep')

/-- Diamond property for global type step with independent actions.
    This is the core lemma: independent actions on global types commute.

    **Proof strategy:**
    - Case analysis on h₁ and h₂
    - comm_head + comm_head: impossible (violates independence)
    - comm_head + comm_async: use BranchesStep_mem
    - comm_async + comm_head: symmetric
    - comm_async + comm_async: use mutual IH via @step.rec
    - mu + mu: use IH on unfolded body
-/
theorem step_diamond_independent {g g₁ g₂ : GlobalType} {act₁ act₂ : GlobalActionR}
    (hind : IndependentActions act₁ act₂)
    (huniq : g.uniqueBranchLabels = true)
    (h₁ : step g act₁ g₁)
    (h₂ : step g act₂ g₂) :
    ∃ g₃, step g₁ act₂ g₃ ∧ step g₂ act₁ g₃ ∧ g₃.uniqueBranchLabels = true :=
  (@step.rec
    (motive_1 := fun g act₁ g₁ _ =>
      g.uniqueBranchLabels = true →
        IndependentActions act₁ act₂ →
        ∀ g₂, step g act₂ g₂ →
        ∃ g₃, step g₁ act₂ g₃ ∧ step g₂ act₁ g₃ ∧ g₃.uniqueBranchLabels = true)
    (motive_2 := fun bs act₁ bs₁ _ =>
      uniqueBranchLabelsBranches bs = true →
        IndependentActions act₁ act₂ →
        ∀ bs₂, BranchesStep step bs act₂ bs₂ →
        ∃ bs₃, BranchesStep step bs₁ act₂ bs₃ ∧
               BranchesStep step bs₂ act₁ bs₃ ∧
               uniqueBranchLabelsBranches bs₃ = true)
    -- Case 1: comm_head
    (fun sender receiver branches label₁ cont₁ hmem₁
        huniq' hind' g₂' h₂' => by
      cases h₂' with
      | comm_head _ _ _ label₂ cont₂ hmem₂ =>
          -- Both comm_head: violates independence (same sender/receiver)
          exact absurd rfl hind'.1
      | comm_async _ _ _ branches' _ label₂ cont₂ hns₂ hcond₂ hmem₂ hcan₂ hbs₂ =>
          -- comm_head + comm_async: use BranchesStep_mem
          obtain ⟨cont₁', hstep_cont, hmem₁'⟩ := BranchesStep_mem hbs₂ hmem₁
          simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq'
          exact ⟨cont₁', hstep_cont,
                 step.comm_head sender receiver branches' label₁ cont₁' hmem₁',
                 uniqueBranchLabels_preserved_by_step (uniqueBranchLabelsBranches_mem huniq'.2 hmem₁) hstep_cont⟩)
    -- Case 2: comm_async
    (fun sender receiver branches branches₁ act₁' label₁ cont₁ hns₁ hcond₁ hmem₁ hcan₁
        _hbs₁ ih_bs
        huniq' hind' g₂' h₂' => by
      cases h₂' with
      | comm_head _ _ _ label₂ cont₂ hmem₂ =>
          -- comm_async + comm_head: use BranchesStep_mem
          obtain ⟨cont₂', hstep_cont, hmem₂'⟩ := BranchesStep_mem _hbs₁ hmem₂
          simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq'
          exact ⟨cont₂',
                 step.comm_head sender receiver branches₁ label₂ cont₂' hmem₂',
                 hstep_cont,
                 uniqueBranchLabels_preserved_by_step (uniqueBranchLabelsBranches_mem huniq'.2 hmem₂) hstep_cont⟩
      | comm_async _ _ _ branches₂ _ label₂ cont₂ hns₂ hcond₂ hmem₂ hcan₂ hbs₂ =>
          -- comm_async + comm_async: use IH for BranchesStep
          simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq'
          obtain ⟨branches₃, hbs₁_to_3, hbs₂_to_3, huniq_bs₃⟩ := ih_bs huniq'.2 hind' branches₂ hbs₂
          -- Get membership for act₂'s witness in branches₁ (stepped by act₁ from hmem₂)
          obtain ⟨cont₂', hstep_cont₂, hmem₂_in_bs₁⟩ := BranchesStep_mem _hbs₁ hmem₂
          -- Get canStep from BranchesStep: since branches₁ steps with act₂ to branches₃,
          -- and (label₂, cont₂') ∈ branches₁, there's a step cont₂' act₂ _ which implies canStep
          obtain ⟨_, hstep_to_3_for_2, _⟩ := BranchesStep_mem hbs₁_to_3 hmem₂_in_bs₁
          have hcan₂' : canStep cont₂' act₂ := step_implies_canStep hstep_to_3_for_2
          -- Get membership for act₁'s witness in branches₂ (stepped by act₂ from hmem₁)
          obtain ⟨cont₁', hstep_cont₁, hmem₁_in_bs₂⟩ := BranchesStep_mem hbs₂ hmem₁
          -- Get canStep from BranchesStep symmetrically
          obtain ⟨_, hstep_to_3_for_1, _⟩ := BranchesStep_mem hbs₂_to_3 hmem₁_in_bs₂
          have hcan₁' : canStep cont₁' act₁' := step_implies_canStep hstep_to_3_for_1
          -- Construct the two comm_async steps to branches₃
          refine ⟨.comm sender receiver branches₃,
                  step.comm_async sender receiver branches₁ branches₃ act₂ label₂ cont₂' hns₂ hcond₂ hmem₂_in_bs₁ hcan₂' hbs₁_to_3,
                  step.comm_async sender receiver branches₂ branches₃ act₁' label₁ cont₁' hns₁ hcond₁ hmem₁_in_bs₂ hcan₁' hbs₂_to_3,
                  ?_⟩
          simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true]
          have hlabels₃ := BranchesStep_preserves_branchLabels hbs₁_to_3
          have hlabels₁ := BranchesStep_preserves_branchLabels _hbs₁
          rw [hlabels₃, hlabels₁]
          exact ⟨huniq'.1, huniq_bs₃⟩)
    -- Case 3: mu
    (fun t body act₁' g₁' _hstep₁ ih_step
        huniq' hind' g₂' h₂' => by
      cases h₂' with
      | mu _ _ _ g₂'' hstep₂ =>
          simp only [GlobalType.uniqueBranchLabels] at huniq'
          have huniq_sub := GlobalType.uniqueBranchLabels_substitute body t (.mu t body) huniq' huniq'
          exact ih_step huniq_sub hind' _ hstep₂)
    -- Case 4: BranchesStep.nil
    (fun act₁' huniq' hind' bs₂ hbs₂ => by
      cases hbs₂ with
      | nil => exact ⟨[], .nil act₂, .nil act₁', rfl⟩)
    -- Case 5: BranchesStep.cons
    (fun label head head₁ rest rest₁ act₁'
        (_hstep : step head act₁' head₁)
        (_hbs : BranchesStep step rest act₁' rest₁)
        (ih_step : head.uniqueBranchLabels = true → IndependentActions act₁' act₂ →
                   ∀ g₂, step head act₂ g₂ →
                   ∃ g₃, step head₁ act₂ g₃ ∧ step g₂ act₁' g₃ ∧ g₃.uniqueBranchLabels = true)
        (ih_bs : uniqueBranchLabelsBranches rest = true → IndependentActions act₁' act₂ →
                 ∀ bs₂, BranchesStep step rest act₂ bs₂ →
                 ∃ bs₃, BranchesStep step rest₁ act₂ bs₃ ∧
                        BranchesStep step bs₂ act₁' bs₃ ∧
                        uniqueBranchLabelsBranches bs₃ = true)
        huniq' hind' bs₂ hbs₂ => by
      cases hbs₂ with
      | cons _ _ head₂ _ rest₂ _ hhead₂ hrest₂ =>
          simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq'
          obtain ⟨head₃, hh₁_to_h₃, hh₂_to_h₃, huniq_h₃⟩ := ih_step huniq'.1 hind' head₂ hhead₂
          obtain ⟨rest₃, hr₁_to_r₃, hr₂_to_r₃, huniq_r₃⟩ := ih_bs huniq'.2 hind' rest₂ hrest₂
          refine ⟨(label, head₃) :: rest₃,
                  .cons label head₁ head₃ rest₁ rest₃ act₂ hh₁_to_h₃ hr₁_to_r₃,
                  .cons label head₂ head₃ rest₂ rest₃ act₁' hh₂_to_h₃ hr₂_to_r₃,
                  ?_⟩
          simp only [uniqueBranchLabelsBranches, Bool.and_eq_true]
          exact ⟨huniq_h₃, huniq_r₃⟩)
    (t := h₁)) huniq hind g₂ h₂

/-- Diamond property for independent actions.

If two independent actions are both enabled, they commute:
taking them in either order reaches the same final configuration.

**Proof strategy:**
1. Use step_diamond_independent to get the common global type g₃
2. Construct c₃ with global type g₃ and environment c.env
3. Show both step paths work with uniqueBranchLabels preserved
-/
theorem diamond_independent {c c₁ c₂ : Configuration} {act₁ act₂ : GlobalActionR}
    (hind : IndependentActions act₁ act₂)
    (h₁ : ConfigStep c c₁ act₁)
    (h₂ : ConfigStep c c₂ act₂) :
    ∃ c₃, ConfigStep c₁ c₃ act₂ ∧ ConfigStep c₂ c₃ act₁ := by
  obtain ⟨huniq₁, hstep₁, henv₁⟩ := h₁
  obtain ⟨_huniq₂, hstep₂, henv₂⟩ := h₂
  -- Use the global-level diamond lemma
  obtain ⟨g₃, hg₁_to_g₃, hg₂_to_g₃, huniq₃⟩ := step_diamond_independent hind huniq₁ hstep₁ hstep₂
  -- Get uniqueBranchLabels for intermediate states
  have huniq_g₁ := uniqueBranchLabels_preserved_by_step huniq₁ hstep₁
  have huniq_g₂ := uniqueBranchLabels_preserved_by_step huniq₁ hstep₂
  -- Construct the common configuration
  let c₃ : Configuration := ⟨g₃, c.env⟩
  use c₃
  constructor
  · -- ConfigStep c₁ c₃ act₂
    exact ⟨huniq_g₁, hg₁_to_g₃, henv₁.symm⟩
  · -- ConfigStep c₂ c₃ act₁
    exact ⟨huniq_g₂, hg₂_to_g₃, henv₂.symm⟩

/-! ## Claims Bundle -/

/-- Claims bundle for determinism. -/
structure Claims where
  /-- Global step determinism (requires uniqueBranchLabels). -/
  global_step_det : ∀ {g g₁ g₂ : GlobalType} {act : GlobalActionR},
      g.uniqueBranchLabels = true → step g act g₁ → step g act g₂ → g₁ = g₂
  /-- Environment step determinism. -/
  env_step_det : ∀ {env env₁ env₂ : EnvConfig} {act : EnvAction},
      EnvConfigStep env act env₁ → EnvConfigStep env act env₂ → env₁ = env₂
  /-- Configuration step determinism. -/
  config_step_det : ∀ {c c₁ c₂ : Configuration} {act : GlobalActionR},
      ConfigStep c c₁ act → ConfigStep c c₂ act → c₁ = c₂
  /-- Diamond property for independent actions. -/
  diamond_independent : ∀ {c c₁ c₂ : Configuration} {act₁ act₂ : GlobalActionR},
      IndependentActions act₁ act₂ →
      ConfigStep c c₁ act₁ → ConfigStep c c₂ act₂ →
      ∃ c₃, ConfigStep c₁ c₃ act₂ ∧ ConfigStep c₂ c₃ act₁

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  global_step_det := global_step_det
  env_step_det := env_step_det
  config_step_det := config_step_det
  diamond_independent := diamond_independent

end RumpsteakV2.Proofs.Safety.Determinism
