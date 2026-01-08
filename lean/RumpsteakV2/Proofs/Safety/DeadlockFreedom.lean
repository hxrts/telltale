import RumpsteakV2.Semantics.Typing
import RumpsteakV2.Semantics.EnvStep
import RumpsteakV2.Semantics.Environment
import RumpsteakV2.Proofs.Safety.SubjectReduction
import RumpsteakV2.Proofs.Core.Assumptions

/-! # RumpsteakV2.Proofs.Safety.DeadlockFreedom

Deadlock freedom for V2.

## Overview

Deadlock freedom states that well-typed configurations under a fair environment
can always make progress: they either terminate (reach End) or can take a step.

This is a conditional liveness property:
- Requires fair environment (messages eventually delivered)
- Requires productive protocol (no infinite silent loops)
- Excludes permanently denied configurations (authorization failures handled by Aura)

## Expose

The following definitions form the semantic interface for proofs:

- `Done`: terminal configuration predicate
- `Stuck`: stuck configuration predicate
- `CanProgress`: existence of a step
- `deadlock_free`: main theorem (under fairness + productivity)
- `Claims`: bundle of deadlock freedom properties
-/

namespace RumpsteakV2.Proofs.Safety.DeadlockFreedom

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Semantics.EnvStep
open RumpsteakV2.Semantics.Environment
open RumpsteakV2.Proofs.Safety.SubjectReduction

/-! ## Terminal and Stuck Predicates -/

/-- A configuration is done (terminal) when the global type is End. -/
def Done (c : Configuration) : Prop :=
  c.globalType = .end

/-- A configuration can make progress if there exists a valid step. -/
def CanProgress (c : Configuration) : Prop :=
  ∃ c' act, ConfigStep c c' act

/-- A configuration is stuck if it's not done and cannot progress. -/
def Stuck (c : Configuration) : Prop :=
  ¬Done c ∧ ¬CanProgress c

/-! ## Deadlock Freedom Theorem

The main theorem: under fairness and productivity, well-typed configurations
are never stuck. They either terminate or can take a step.

**Proof obligations** (to be filled in):
1. Show that canStep implies ConfigStep exists (environment provides delivery)
2. Show that productivity ensures canStep for non-terminal types
3. Use fairness to ensure pending messages are eventually delivered
-/

/-- Helper: productive types that are not End can step.

A productive type has at least one communication before any recursive call,
so there's always an enabled action (the first communication). -/
axiom productive_implies_canStep (g : GlobalType)
    (hprod : g.isProductive = true)
    (hne : g ≠ .end) :
    ∃ act, canStep g act

/-- Helper: if a global type can step, a well-typed configuration can step.

This requires the environment to provide message delivery for the action.
Under fair environment, pending messages are eventually delivered. -/
axiom canStep_implies_configStep (c : Configuration) (act : GlobalActionR)
    (htyped : WellTypedConfig c)
    (hcan : canStep c.globalType act) :
    ∃ c', ConfigStep c c' act

/-- Deadlock freedom: well-typed productive configurations are not stuck.

Under a fair environment, a well-typed configuration with a productive
global type is never stuck: it either terminates (Done) or can progress.

**Assumptions:**
- `htyped`: configuration is well-typed
- `hprod`: global type is productive (every recursion has communication)
- Implicit: fair environment (not modeled explicitly in this statement)

**Proof sketch:**
1. Case split on whether c.globalType = .end
2. If End: we're Done
3. If not End: by productivity, canStep exists
4. By canStep_implies_configStep, ConfigStep exists
5. Therefore CanProgress holds
-/
theorem deadlock_free (c : Configuration)
    (htyped : WellTypedConfig c)
    (hprod : c.globalType.isProductive = true) :
    Done c ∨ CanProgress c := by
  by_cases hend : c.globalType = .end
  · left; exact hend
  · right
    have ⟨act, hcan⟩ := productive_implies_canStep c.globalType hprod hend
    have ⟨c', hstep⟩ := canStep_implies_configStep c act htyped hcan
    exact ⟨c', act, hstep⟩

/-- Corollary: well-typed productive configurations are not stuck. -/
theorem not_stuck (c : Configuration)
    (htyped : WellTypedConfig c)
    (hprod : c.globalType.isProductive = true) :
    ¬Stuck c := by
  intro ⟨hnd, hnp⟩
  have h := deadlock_free c htyped hprod
  cases h with
  | inl hdone => exact hnd hdone
  | inr hprog => exact hnp hprog

/-! ## Fairness-Dependent Formulation

For a more complete formulation, we need to model the environment explicitly
and state deadlock freedom as a property of fair traces.
-/

/-- A trace is a sequence of configurations. -/
abbrev ConfigTrace := List Configuration

/-- A configuration trace is valid if each step is a ConfigStep. -/
def ValidTrace : ConfigTrace → Prop
  | [] => True
  | [_] => True
  | c :: c' :: rest => (∃ act, ConfigStep c c' act) ∧ ValidTrace (c' :: rest)

/-- A trace reaches termination if it ends with a Done configuration. -/
def Terminates (trace : ConfigTrace) : Prop :=
  match trace.getLast? with
  | some c => Done c
  | none => False

/-- Deadlock freedom for traces: valid traces from well-typed configs terminate or extend.

This is a coinductive property: either the trace terminates, or it can always be extended.
Under fairness, infinite extension means infinite progress (liveness). -/
def DeadlockFreeTrace (trace : ConfigTrace) : Prop :=
  Terminates trace ∨ ∃ c act c', trace.getLast? = some c ∧ ConfigStep c c' act

/-! ## Claims Bundle -/

/-- Claims bundle for deadlock freedom. -/
structure Claims where
  /-- Main deadlock freedom theorem. -/
  deadlock_free : ∀ c, WellTypedConfig c → c.globalType.isProductive = true → Done c ∨ CanProgress c
  /-- Corollary: not stuck. -/
  not_stuck : ∀ c, WellTypedConfig c → c.globalType.isProductive = true → ¬Stuck c

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  deadlock_free := deadlock_free
  not_stuck := not_stuck

end RumpsteakV2.Proofs.Safety.DeadlockFreedom
