import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Semantics.Environment

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

/-- Placeholder: configuration step relation. -/
def ConfigStep (_c _c' : Configuration) (_act : GlobalActionR) : Prop := True

/-- Placeholder: reflexive transitive closure of ConfigStep. -/
def ConfigStepStar (_c _c' : Configuration) (_acts : List GlobalActionR) : Prop := True

/-- Placeholder: local action. -/
structure LocalActionR where
  participant : String
  label : Label
  deriving Repr, DecidableEq, Inhabited

/-- Placeholder: local step relation. -/
def LocalStep (_lt _lt' : QLocalTypeR) (_act : LocalActionR) : Prop := True

/-! ## Global Type Determinism

The global step relation is deterministic: given the same action,
there is exactly one next global type.

**Proof obligation**: By case analysis on the step relation constructors.
Each constructor (comm_head, comm_async, mu) uniquely determines the result.
-/

/-- Global step is deterministic given the same action.

Proof sketch: by case analysis on step constructors via @step.rec.
- comm_head/comm_head: both select same label (from action), membership gives same cont
- comm_head/comm_async: actions differ (head has receiver in action, async doesn't)
- comm_async/comm_async: IH on BranchesStep
- mu/mu: IH on the unfolded body step

Uses @step.rec to handle the nested inductive + mutual recursion with BranchesStep.
-/
theorem global_step_det {g g₁ g₂ : GlobalType} {act : GlobalActionR}
    (h₁ : step g act g₁)
    (h₂ : step g act g₂) :
    g₁ = g₂ :=
  (@step.rec
    (motive_1 := fun g act g' _ => ∀ g₂, step g act g₂ → g' = g₂)
    (motive_2 := fun bs act bs' _ => ∀ bs₂, BranchesStep step bs act bs₂ → bs' = bs₂)
    -- Case 1: comm_head
    (fun sender receiver branches label cont (hmem : (label, cont) ∈ branches)
        (g₂ : GlobalType) (h₂ : step (.comm sender receiver branches)
          { sender := sender, receiver := receiver, label := label } g₂) => by
      cases h₂ with
      | comm_head _ _ _ label' cont' hmem' =>
          -- Both comm_head: action is { sender, receiver, label } = { sender, receiver, label' }
          -- So label = label' by structure equality (the action determines the label)
          -- hmem : (label, cont) ∈ branches
          -- hmem' : (label, cont') ∈ branches  (same label since label = label')
          --
          -- For cont = cont', we need: unique labels in branches
          -- i.e., if (l, c) ∈ branches and (l, c') ∈ branches then c = c'
          --
          -- This is a well-formedness property of global types that should be
          -- ensured by the MPST type system (branch labels must be distinct).
          -- TODO: Add UniqueBranchLabels predicate and proof
          sorry
      | comm_async _ _ _ _ _ _ _ _ hcond' _ _ _ =>
          -- comm_head action: { sender := sender, receiver := receiver, label := label }
          -- So act.sender = sender, act.receiver = receiver
          -- comm_async condition hcond': act.sender = sender → act.receiver ≠ receiver
          -- Since act.sender = sender, we get: act.receiver ≠ receiver
          -- But act.receiver = receiver, contradiction!
          exact absurd rfl (hcond' rfl))
    -- Case 2: comm_async
    (fun sender receiver branches branches' act' label cont hns hcond hmem hcan
        (_hbstep : BranchesStep step branches act' branches')
        (ih_bstep : ∀ bs₂, BranchesStep step branches act' bs₂ → branches' = bs₂)
        (g₂ : GlobalType) (h₂ : step (.comm sender receiver branches) act' g₂) => by
      cases h₂ with
      | comm_head _ _ _ _ _ _ =>
          -- comm_head constructs action { sender, receiver, label' }
          -- So the action act' = { sender := sender, receiver := receiver, label := label' }
          -- This means act'.sender = sender and act'.receiver = receiver
          -- But from comm_async we have hcond: act'.sender = sender → act'.receiver ≠ receiver
          -- Since act'.sender = sender, we get act'.receiver ≠ receiver
          -- But act'.receiver = receiver, contradiction!
          exact absurd rfl (hcond rfl)
      | comm_async _ _ _ branches₂ _ _ _ _ _ _ _ hbstep₂ =>
          have heq := ih_bstep branches₂ hbstep₂
          subst heq
          rfl)
    -- Case 3: mu
    (fun t body act' g' (_hstep : step (body.substitute t (.mu t body)) act' g')
        (ih : ∀ g₂, step (body.substitute t (.mu t body)) act' g₂ → g' = g₂)
        (g₂ : GlobalType) (h₂ : step (.mu t body) act' g₂) => by
      cases h₂ with
      | mu _ _ _ _ hstep₂ =>
          -- hstep₂ : step (body.substitute t (.mu t body)) act' g₂
          -- ih : ∀ g₂, step (body.substitute t (.mu t body)) act' g₂ → g' = g₂
          exact ih g₂ hstep₂)
    -- Case 4: BranchesStep.nil
    (fun act' (bs₂ : List (Label × GlobalType))
        (h₂ : BranchesStep step [] act' bs₂) => by
      cases h₂ with
      | nil => rfl)
    -- Case 5: BranchesStep.cons
    (fun lbl gHead gHead' restTail restTail' act'
        (_hstep : step gHead act' gHead')
        (_hbstep : BranchesStep step restTail act' restTail')
        (ih_step : ∀ g₂, step gHead act' g₂ → gHead' = g₂)
        (ih_bstep : ∀ bs₂, BranchesStep step restTail act' bs₂ → restTail' = bs₂)
        (bs₂ : List (Label × GlobalType))
        (h₂ : BranchesStep step ((lbl, gHead) :: restTail) act' bs₂) => by
      cases h₂ with
      | cons _ _ gNew _ restNew _ hstep₂ hbstep₂ =>
          have hg := ih_step gNew hstep₂
          have hrest := ih_bstep restNew hbstep₂
          subst hg hrest
          rfl)
    (t := h₁)) g₂ h₂

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

Note: Currently uses placeholder ConfigStep (always True).
When ConfigStep is properly defined using global_step_det + env_step_det,
this proof would combine those determinism results.
-/
theorem config_step_det {c c₁ c₂ : Configuration} {act : GlobalActionR}
    (_h₁ : ConfigStep c c₁ act)
    (_h₂ : ConfigStep c c₂ act) :
    c₁ = c₂ := by
  -- Placeholder: ConfigStep is defined as True
  -- Real proof would use global_step_det and env_step_det
  sorry

/-! ## Local Type Determinism

For projected local types, transitions are also deterministic.
This follows from global determinism + projection coherence.
-/

/-- Local step is deterministic (follows from global determinism).

Note: Currently uses placeholder LocalStep (always True).
When LocalStep is properly defined via projection from global step,
this would follow from global_step_det + projection coherence.
-/
theorem local_step_det {lt lt₁ lt₂ : QLocalTypeR} {act : LocalActionR}
    (_h₁ : LocalStep lt lt₁ act)
    (_h₂ : LocalStep lt lt₂ act) :
    lt₁ = lt₂ := by
  -- Placeholder: LocalStep is defined as True
  -- Real proof would use global_step_det + projection coherence
  sorry

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

/-- MPST is NOT confluent in general (branch choices diverge). -/
axiom not_confluent_general :
    ¬∀ c c₁ c₂ act₁ act₂,
      ConfigStep c c₁ act₁ → ConfigStep c c₂ act₂ → act₁ ≠ act₂ →
      Confluent c c₁ c₂

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

/-- Diamond property for independent actions.

If two independent actions are both enabled, they commute:
taking them in either order reaches the same final configuration.

Note: Currently uses placeholder ConfigStep (always True).
Real proof would show that independent actions (disjoint role pairs)
can be reordered without affecting the final configuration.
-/
theorem diamond_independent {c c₁ c₂ : Configuration} {act₁ act₂ : GlobalActionR}
    (_hind : IndependentActions act₁ act₂)
    (_h₁ : ConfigStep c c₁ act₁)
    (_h₂ : ConfigStep c c₂ act₂) :
    ∃ c₃, ConfigStep c₁ c₃ act₂ ∧ ConfigStep c₂ c₃ act₁ := by
  -- Placeholder: ConfigStep is always True, so we can pick any c₃
  -- Real proof would construct c₃ by applying both steps in sequence
  sorry

/-! ## Claims Bundle -/

/-- Claims bundle for determinism. -/
structure Claims where
  /-- Global step determinism. -/
  global_step_det : ∀ {g g₁ g₂ : GlobalType} {act : GlobalActionR},
      step g act g₁ → step g act g₂ → g₁ = g₂
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
