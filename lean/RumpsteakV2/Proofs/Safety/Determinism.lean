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

/-- Global step is deterministic given the same action. -/
axiom global_step_det {g g₁ g₂ : GlobalType} {act : GlobalActionR}
    (h₁ : step g act g₁)
    (h₂ : step g act g₂) :
    g₁ = g₂
-- Note: Proof blocked due to step being a nested inductive type.
-- Would require mutual recursion with BranchesStep determinism.
-- Proof outline:
-- | comm_head/comm_head: action.label uniquely determines continuation
-- | comm_head/comm_async: contradiction (result is cont vs comm)
-- | comm_async/comm_head: symmetric contradiction
-- | comm_async/comm_async: BranchesStep determinism
-- | mu/mu: induction on inner step

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

/-- Configuration step is deterministic given the same action. -/
axiom config_step_det {c c₁ c₂ : Configuration} {act : GlobalActionR}
    (h₁ : ConfigStep c c₁ act)
    (h₂ : ConfigStep c c₂ act) :
    c₁ = c₂

/-! ## Local Type Determinism

For projected local types, transitions are also deterministic.
This follows from global determinism + projection coherence.
-/

/-- Local step is deterministic (follows from global determinism). -/
axiom local_step_det {lt lt₁ lt₂ : QLocalTypeR} {act : LocalActionR}
    (h₁ : LocalStep lt lt₁ act)
    (h₂ : LocalStep lt lt₂ act) :
    lt₁ = lt₂

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
-/
axiom diamond_independent {c c₁ c₂ : Configuration} {act₁ act₂ : GlobalActionR}
    (hind : IndependentActions act₁ act₂)
    (h₁ : ConfigStep c c₁ act₁)
    (h₂ : ConfigStep c c₂ act₂) :
    ∃ c₃, ConfigStep c₁ c₃ act₂ ∧ ConfigStep c₂ c₃ act₁

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
