import Semantics.Determinism.Core.GlobalDeterminism

/-! # Remaining Determinism Proofs

Environment transition determinism: queue operations (deliver, drop,
timeout) are uniquely determined by the action label. -/

/-
The Problem. Global determinism depends on environment determinism:
given the same action, the environment transition is unique. We need
to prove each environment action (deliver, drop, timeout) yields a
unique successor.

Solution Structure. Prove `env_step_det_deliver`, `env_step_det_drop`,
`env_step_det_timeout` by showing queue head determines the tail and
the update function is determined by the action.
-/

open SessionCoTypes.EQ2
open SessionCoTypes.Quotient

namespace Semantics.Determinism

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Semantics.Environment

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
          obtain ⟨vt₁, hmem₁'⟩ := hmem₁
          obtain ⟨vt₂, hmem₂'⟩ := hmem₂
          have := mem_branchL_unique_label huniq₁ hmem₁' hmem₂'
          exact congrArg Prod.snd this
  | recv huniq₁ hp₁ hmem₁ =>
      cases h₂ with
      | recv huniq₂ hp₂ hmem₂ =>
          obtain ⟨vt₁, hmem₁'⟩ := hmem₁
          obtain ⟨vt₂, hmem₂'⟩ := hmem₂
          have := mem_branchL_unique_label huniq₁ hmem₁' hmem₂'
          exact congrArg Prod.snd this
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

/-! ### Stuck-var lemmas -/

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

/-! ### Non-confluence counterexample construction -/

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
  · decide
  constructor
  · simpa [counter_c0, counter_c1, counter_protocol, counter_act1] using
      (step.comm_head "A" "B" counter_branches counter_label1 (.var "X") counter_mem1)
  · rfl

private theorem counter_step2 : ConfigStep counter_c0 counter_c2 counter_act2 := by
  -- Step selecting label2.
  constructor
  · decide
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

/-! ### Counterexample theorem -/

/-- A concrete counterexample: global confluence does not hold for all configurations. -/ theorem not_confluent_general :
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

end Semantics.Determinism
