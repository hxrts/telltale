import Telltale.Protocol.GlobalType
import Telltale.Proofs.Safety.SubjectReduction

/-
The Problem. Show that well-typed configurations can make progress:
they either terminate (reach End) or can take a step.

The difficulty is that well-formedness alone does not guarantee progress.
A type like `mu t .end` is well-formed (contractive) but loops forever
without communication. We need a separate predicate `ReachesComm` that
says the type can reach a communication constructor.

Solution Structure. The proof separates two concerns:
1. `reachesComm_implies_canStep`: types that reach a comm can step (global level)
2. `canStep_implies_configStep`: configs with steppable global types can step
3. `deadlock_free`: combines (1) and (2) for the main result

This mirrors the Coq split between `gcontractive` (well-formedness) and
`goodG` (progress predicate) in subject_reduction/theories/Process/Congruence.v.
-/

/-! # Telltale.Proofs.Safety.DeadlockFreedom

Deadlock freedom for V2.

## Overview

Deadlock freedom states that well-typed configurations under a fair environment
can always make progress: they either terminate (reach End) or can take a step.

This is a conditional liveness property:
- Requires fair environment (messages eventually delivered)
- Requires productive protocol (no infinite silent loops)
- Uses the `ReachesComm` predicate from Coq's `goodG`

## Expose

The following definitions form the semantic interface for proofs:

- `ReachesComm`: progress predicate (type can reach a communication)
- `Done`: terminal configuration predicate
- `Stuck`: stuck configuration predicate
- `CanProgress`: existence of a step
- `deadlock_free`: main theorem (requires ReachesComm)
- `Claims`: bundle of deadlock freedom properties
-/

namespace Telltale.Proofs.Safety.DeadlockFreedom

open Telltale.Protocol.GlobalType
open Telltale.Protocol.CoTypes.Quotient
open Telltale.Protocol.Projection.Trans
open Telltale.Proofs.Safety.SubjectReduction

/-! ## Progress Predicate: ReachesComm

This predicate checks whether a type can reach a communication.
It corresponds to Coq's `goodG` / `canStep` predicates. -/

/-- A global type reaches a communication if it can unfold to a comm constructor.

This is the progress predicate, separate from well-formedness.
Example: `mu t .end` is well-formed but does NOT satisfy `ReachesComm`. -/
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

/-! ## Global Type Progress

The key theorem: types that reach a communication can step. -/

/-- Helper: extract first branch from non-empty branches. -/
private theorem first_branch_mem {branches : List (Label × GlobalType)}
    (hne : branches ≠ []) :
    ∃ label cont, (label, cont) ∈ branches := by
  -- Non-empty list has a head element.
  match branches with
  | [] => exact absurd rfl hne
  | (l, c) :: _ => exact ⟨l, c, by simp⟩

/-- Types that reach a communication have a synchronous canStep.

This produces `SyncCanStep` derivations which can be stepped without async machinery.
The derivation is always comm_head at the base, wrapped by mu unfoldings. -/
theorem reachesComm_implies_syncCanStep (g : GlobalType)
    (_hwf : g.wellFormed = true)
    (hcomm : ReachesComm g) :
    ∃ act, SyncCanStep g act := by
  induction hcomm with
  | comm sender receiver branches hne =>
      -- Non-empty branches: extract first branch and construct action.
      obtain ⟨label, cont, hmem⟩ := first_branch_mem hne
      exact ⟨{ sender := sender, receiver := receiver, label := label },
             SyncCanStep.comm_head sender receiver branches label cont hmem⟩
  | mu t body _hbody ih =>
      -- Mu case: unfold and use IH.
      have ⟨act, hcan⟩ := ih (wellFormed_mu_unfold t body _hwf)
      exact ⟨act, SyncCanStep.mu t body act hcan⟩

/-- Types that reach a communication can step.

**Requires:**
- `hwf`: well-formedness (for structural properties)
- `hcomm`: the type reaches a communication (progress predicate)

**Proof:** By induction on the `ReachesComm` derivation.
- `comm`: Use `canStep.comm_head` with the first branch
- `mu`: Use `canStep.mu` with IH on the unfolded body -/
theorem reachesComm_implies_canStep (g : GlobalType)
    (hwf : g.wellFormed = true)
    (hcomm : ReachesComm g) :
    ∃ act, canStep g act := by
  -- Get SyncCanStep, then convert to canStep.
  have ⟨act, hsync⟩ := reachesComm_implies_syncCanStep g hwf hcomm
  exact ⟨act, hsync.toCanStep⟩

/-! ## Configuration Progress

Lift global type steps to configuration steps. -/

/-- Helper: build the stepped configuration from global step.

Given a global type step `g → g'`, construct the stepped configuration
with updated process projections. -/
private def buildSteppedConfig (c : Configuration) (g' : GlobalType) : Configuration where
  globalType := g'
  processes := c.processes.map fun p => { p with
    localType := QLocalTypeR.ofLocal (trans g' p.role)
  }

/-- Helper: the built configuration preserves roles (in ConfigStep order). -/
private theorem buildSteppedConfig_roles (c : Configuration) (g' : GlobalType) :
    c.processes.map Process.role = (buildSteppedConfig c g').processes.map Process.role := by
  -- Mapping preserves roles since we only update localType.
  simp only [buildSteppedConfig, List.map_map]
  -- The composed function extracts role, which is unchanged.
  rfl

/-- Helper: the built configuration has correct projections. -/
private theorem buildSteppedConfig_projections (c : Configuration) (g' : GlobalType) :
    ∀ p' ∈ (buildSteppedConfig c g').processes,
      p'.localType = QLocalTypeR.ofLocal (trans g' p'.role) := by
  -- Each process has its localType set to the projection.
  intro p' hp'
  simp only [buildSteppedConfig, List.mem_map] at hp'
  obtain ⟨p, _, rfl⟩ := hp'
  rfl

/-- If a global type has SyncCanStep, a well-typed configuration can step.

This version uses SyncCanStep which has a complete proof without async machinery. -/
theorem syncCanStep_implies_configStep (c : Configuration) (act : GlobalActionR)
    (_htyped : WellTypedConfig c)
    (hcan : SyncCanStep c.globalType act) :
    ∃ c', ConfigStep c c' act := by
  -- From SyncCanStep, we know there exists g' with step c.globalType act g'.
  have ⟨g', hstep⟩ := syncCanStep_implies_step c.globalType act hcan
  -- Build the stepped configuration.
  let c' := buildSteppedConfig c g'
  refine ⟨c', ?_⟩
  constructor
  · exact hstep
  · exact buildSteppedConfig_roles c g'
  · exact buildSteppedConfig_projections c g'

/-- If a global type can step, a well-typed configuration can step.

This requires the environment to provide message delivery for the action.
Under fair environment, pending messages are eventually delivered. -/
theorem canStep_implies_configStep (c : Configuration) (act : GlobalActionR)
    (_htyped : WellTypedConfig c)
    (hcan : canStep c.globalType act) :
    ∃ c', ConfigStep c c' act := by
  -- From canStep, we know there exists g' with step c.globalType act g'.
  have ⟨g', hstep⟩ := canStep_implies_step c.globalType act hcan
  -- Build the stepped configuration.
  let c' := buildSteppedConfig c g'
  refine ⟨c', ?_⟩
  constructor
  · exact hstep
  · exact buildSteppedConfig_roles c g'
  · exact buildSteppedConfig_projections c g'

/-! ## Deadlock Freedom Theorem

The main theorem requires both well-formedness AND reachesComm.
This mirrors Coq's `coherentG` which combines `gcontractive` and `goodG`. -/

/-- Deadlock freedom: well-typed configurations that reach a comm can progress.

**Assumptions:**
- `htyped`: configuration is well-typed
- `hwf`: global type is well-formed
- `hcomm`: global type reaches a communication (progress predicate)
- Implicit: fair environment (not modeled explicitly)

**Proof sketch:**
1. By `reachesComm_implies_syncCanStep`, the global type has a sync step
2. By `syncCanStep_implies_configStep`, the configuration can step
3. Therefore CanProgress holds

Note: Uses SyncCanStep for a complete proof without async machinery. -/
theorem deadlock_free (c : Configuration)
    (htyped : WellTypedConfig c)
    (hwf : c.globalType.wellFormed = true)
    (hcomm : ReachesComm c.globalType) :
    CanProgress c := by
  -- Step 1: global type has sync canStep (from ReachesComm).
  have ⟨act, hsync⟩ := reachesComm_implies_syncCanStep c.globalType hwf hcomm
  -- Step 2: configuration can step (using sync version for complete proof).
  have ⟨c', hstep⟩ := syncCanStep_implies_configStep c act htyped hsync
  -- Step 3: conclude CanProgress.
  exact ⟨c', act, hstep⟩

/-- Corollary: well-typed configurations that reach a comm are not stuck. -/
theorem not_stuck (c : Configuration)
    (htyped : WellTypedConfig c)
    (hwf : c.globalType.wellFormed = true)
    (hcomm : ReachesComm c.globalType) :
    ¬Stuck c := by
  -- Stuck means not done AND not can progress.
  intro ⟨_, hnp⟩
  -- But we have CanProgress.
  have hp := deadlock_free c htyped hwf hcomm
  exact hnp hp

/-! ## Weaker Formulations -/

/-- Weaker deadlock freedom: well-formed configs are done, reach comm, or neither.

This version doesn't require the `ReachesComm` hypothesis, but gives a weaker
conclusion. For types that don't reach a communication (like `mu t .end`),
this doesn't guarantee progress. -/
theorem deadlock_free_trichotomy (c : Configuration)
    (_htyped : WellTypedConfig c)
    (_hwf : c.globalType.wellFormed = true) :
    Done c ∨ ReachesComm c.globalType ∨ ¬ReachesComm c.globalType := by
  -- Law of excluded middle on ReachesComm.
  by_cases hcomm : ReachesComm c.globalType
  · right; left; exact hcomm
  · right; right; exact hcomm

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

end Telltale.Proofs.Safety.DeadlockFreedom
