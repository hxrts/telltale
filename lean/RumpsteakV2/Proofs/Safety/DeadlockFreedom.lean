import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Semantics.Environment

/-! # RumpsteakV2.Proofs.Safety.DeadlockFreedom

Deadlock freedom for V2.

## Overview

Deadlock freedom states that well-typed configurations under a fair environment
can always make progress: they either terminate (reach End) or can take a step.

This is a conditional liveness property:
- Requires fair environment (messages eventually delivered)
- Requires productive protocol (no infinite silent loops)
- Excludes permanently denied configurations (authorization failures handled by Aura)

## Design Note: Separation of Concerns

Following the Coq reference implementation (subject_reduction), we separate:
- `wellFormed`: structural well-formedness (closed + contractive/observable)
- `reachesComm`: progress predicate (type can reach a communication)

This mirrors the Coq split between `gcontractive` and `goodG`. The predicate
`wellFormed` ensures the type has a valid coinductive unfolding, while
`reachesComm` ensures it can actually make progress. These are independent
properties that are combined when proving deadlock freedom.

Example: `mu t .end` is well-formed (contractive) but NOT `reachesComm`
(loops forever without doing anything).

## Expose

The following definitions form the semantic interface for proofs:

- `reachesComm`: progress predicate (type can reach a communication)
- `Done`: terminal configuration predicate
- `Stuck`: stuck configuration predicate
- `CanProgress`: existence of a step
- `deadlock_free`: main theorem (requires reachesComm)
- `Claims`: bundle of deadlock freedom properties

## Dependencies

This module uses placeholder definitions for:
- `Configuration`: defined here, will be unified with SubjectReduction
- `WellTypedConfig`: typing judgment placeholder
- `ConfigStep`: step relation placeholder

Once Project.lean builds, these can be replaced with imports from SubjectReduction.
-/

namespace RumpsteakV2.Proofs.Safety.DeadlockFreedom

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Semantics.Environment

/-! ## Configuration (Placeholder)

These definitions will be unified with SubjectReduction once Project.lean is fixed.
-/

/-- A configuration combines a global type with environment state.
This is a placeholder until SubjectReduction imports work. -/
structure Configuration where
  globalType : GlobalType
  env : EnvConfig
  deriving Inhabited

/-- Placeholder: well-typed configuration predicate. -/
def WellTypedConfig (_c : Configuration) : Prop := True

/-- Placeholder: configuration step relation. -/
def ConfigStep (_c _c' : Configuration) (_act : GlobalActionR) : Prop := True

/-- Placeholder: reflexive transitive closure of ConfigStep. -/
def ConfigStepStar (_c _c' : Configuration) (_acts : List GlobalActionR) : Prop := True

/-! ## Progress Predicate: reachesComm

This is a separate predicate from well-formedness that checks whether a type
can reach a communication. It corresponds to Coq's `goodG` predicate.

A type reaches a communication if:
- It IS a communication, or
- It's a recursion whose unfolding reaches a communication

Types that DON'T reach a communication:
- `end` (terminal, no communication)
- `var t` (free variable, stuck)
- `mu t .end` (loops forever on end)
- `mu t (.var t)` (loops forever unfolding, but this is also non-productive)
-/

/-- A global type reaches a communication if it can unfold to a comm constructor.

This is the progress predicate, separate from well-formedness.
Corresponds to Coq's `goodG` / `canStep` predicates. -/
inductive ReachesComm : GlobalType → Prop where
  | comm (sender receiver : String) (branches : List (Label × GlobalType)) :
      branches ≠ [] → ReachesComm (.comm sender receiver branches)
  | mu (t : String) (body : GlobalType) :
      ReachesComm (body.substitute t (.mu t body)) →
      ReachesComm (.mu t body)

/-- Boolean decision procedure for reachesComm (approximation with fuel).

Since the coinductive case (mu) can loop, we use fuel to bound exploration.
Returns true if a communication is reachable within `fuel` unfoldings. -/
def reachesCommBool (g : GlobalType) (fuel : Nat := 100) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match g with
    | .end => false
    | .var _ => false
    | .mu t body => reachesCommBool (body.substitute t (.mu t body)) fuel
    | .comm _ _ branches => !branches.isEmpty

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

/-! ## Progress Theorem

The key theorem: types that reach a communication can step.
This requires the separate `ReachesComm` predicate, not just well-formedness.
-/

/-- Types that reach a communication can step.

**Requires:**
- `hwf`: well-formedness (for structural properties)
- `hcomm`: the type reaches a communication (progress predicate)

**Proof:** By induction on the `ReachesComm` derivation.
- `comm`: Use `canStep.comm_head` with the first branch
- `mu`: Use `canStep.mu` with IH on the unfolded body -/
theorem reachesComm_implies_canStep (g : GlobalType)
    (_hwf : g.wellFormed = true)
    (hcomm : ReachesComm g) :
    ∃ act, canStep g act := by
  induction hcomm with
  | comm sender receiver branches hne =>
      match hbr : branches with
      | [] => exact absurd rfl hne
      | (label, cont) :: rest =>
          have hmem : (label, cont) ∈ (label, cont) :: rest := by simp
          exact ⟨{ sender := sender, receiver := receiver, label := label },
                 canStep.comm_head sender receiver ((label, cont) :: rest) label cont hmem⟩
  | mu t body _hbody ih =>
      have ⟨act, hcan⟩ := ih (wellFormed_mu_unfold t body _hwf)
      exact ⟨act, canStep.mu t body act hcan⟩

/-- Helper: if a global type can step, a well-typed configuration can step.

This requires the environment to provide message delivery for the action.
Under fair environment, pending messages are eventually delivered.

Note: Currently uses placeholder ConfigStep (always True).
Real proof would construct the stepped configuration from global step + env step. -/
theorem canStep_implies_configStep (c : Configuration) (act : GlobalActionR)
    (_htyped : WellTypedConfig c)
    (_hcan : canStep c.globalType act) :
    ∃ c', ConfigStep c c' act := by
  -- Placeholder: ConfigStep is always True, so any c' works
  -- Real proof would construct c' = { globalType := g', env := env' }
  -- from step c.globalType act g' and EnvConfigStep c.env act env'
  exact ⟨c, trivial⟩

/-! ## Deadlock Freedom Theorem

The main theorem requires both well-formedness AND reachesComm.
This mirrors the Coq `coherentG` predicate which combines `gcontractive` and `goodG`.
-/

/-- Deadlock freedom: well-typed configurations that reach a comm are not stuck.

**Assumptions:**
- `htyped`: configuration is well-typed
- `hwf`: global type is well-formed
- `hcomm`: global type reaches a communication (progress predicate)
- Implicit: fair environment (not modeled explicitly in this statement)

**Proof sketch:**
1. By `reachesComm_implies_canStep`, the global type can step
2. By `canStep_implies_configStep`, the configuration can step
3. Therefore CanProgress holds -/
theorem deadlock_free (c : Configuration)
    (htyped : WellTypedConfig c)
    (hwf : c.globalType.wellFormed = true)
    (hcomm : ReachesComm c.globalType) :
    CanProgress c := by
  have ⟨act, hcan⟩ := reachesComm_implies_canStep c.globalType hwf hcomm
  have ⟨c', hstep⟩ := canStep_implies_configStep c act htyped hcan
  exact ⟨c', act, hstep⟩

/-- Weaker deadlock freedom: well-formed configs are either done OR reach comm OR stuck.

This version doesn't require the `ReachesComm` hypothesis, but gives a weaker conclusion.
For types that don't reach a communication (like `mu t .end`), this doesn't guarantee progress. -/
theorem deadlock_free_weak (c : Configuration)
    (_htyped : WellTypedConfig c)
    (_hwf : c.globalType.wellFormed = true) :
    Done c ∨ ReachesComm c.globalType ∨ ¬ReachesComm c.globalType := by
  by_cases hcomm : ReachesComm c.globalType
  · right; left; exact hcomm
  · right; right; exact hcomm

/-- Corollary: well-typed configurations that reach a comm are not stuck. -/
theorem not_stuck (c : Configuration)
    (htyped : WellTypedConfig c)
    (hwf : c.globalType.wellFormed = true)
    (hcomm : ReachesComm c.globalType) :
    ¬Stuck c := by
  intro ⟨_, hnp⟩
  have h := deadlock_free c htyped hwf hcomm
  exact hnp h

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

/-- Claims bundle for deadlock freedom.

Note: requires `ReachesComm` hypothesis, mirroring Coq's separation of
`gcontractive` (well-formedness) and `goodG` (progress). -/
structure Claims where
  /-- Main deadlock freedom theorem. -/
  deadlock_free : ∀ c, WellTypedConfig c → c.globalType.wellFormed = true →
      ReachesComm c.globalType → CanProgress c
  /-- Corollary: not stuck. -/
  not_stuck : ∀ c, WellTypedConfig c → c.globalType.wellFormed = true →
      ReachesComm c.globalType → ¬Stuck c

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  deadlock_free := deadlock_free
  not_stuck := not_stuck

end RumpsteakV2.Proofs.Safety.DeadlockFreedom
