import SessionTypes.GlobalType
import Semantics.SubjectReduction

/-
The Problem. Show that well-typed configurations can make progress:
they either terminate (reach End) or can take a step.

The difficulty is that well-formedness alone does not guarantee progress.
A type like `mu t .end` is well-formed (contractive) but loops forever
without communication. We need a separate predicate `ReachesComm` that
says the type can reach a communication constructor.

Solution Structure.
1. `wf_trichotomy`: from well-formedness (closed, non-empty comms, productive),
   a global type unfolds to `end`, to a delegation, or reaches a communication
   (by well-founded recursion on the number of leading `mu` binders).
2. `wf_global_progress` / `deadlock_free_trichotomy`: global-level progress.
3. `deadlock_free`: communication-headed well-typed configurations step (via the
   honest `ConfigStep`) to well-typed configurations.
-/

/-! # Semantics.DeadlockFreedom

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
- `wf_trichotomy`, `deadlock_free_trichotomy`: progress derived from well-formedness
- `deadlock_free`: configuration-level progress for communication heads
- `Claims`: bundle of deadlock freedom properties
-/

namespace Semantics.DeadlockFreedom

open SessionTypes.GlobalType
open Choreography.Projection.Project
open Semantics.SubjectReduction

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
    | .delegate _ _ _ _ _ => false

/-- Soundness of the fuel-bounded check: a `true` answer witnesses `ReachesComm`. -/
theorem reachesCommBool_sound : ∀ (fuel : Nat) (g : GlobalType),
    reachesCommBool g fuel = true → ReachesComm g
  | 0, _, h => by simp [reachesCommBool] at h
  | n + 1, g, h => by
      cases g with
      | «end» => simp [reachesCommBool] at h
      | var _ => simp [reachesCommBool] at h
      | delegate _ _ _ _ _ => simp [reachesCommBool] at h
      | mu t body => exact .mu t body (reachesCommBool_sound n _ (by simpa [reachesCommBool] using h))
      | comm s r bs =>
          refine .comm s r bs ?_
          simpa [reachesCommBool] using h

/-! ## Terminal Shapes -/

/-- A global type unfolds (through `mu`) to `end`. -/
inductive UnfoldsToEnd : GlobalType → Prop where
  | done : UnfoldsToEnd .end
  | mu (t : String) (body : GlobalType) :
      UnfoldsToEnd (body.substitute t (.mu t body)) → UnfoldsToEnd (.mu t body)

/-- A global type unfolds (through `mu`) to a delegation, which `step` does not model. -/
inductive UnfoldsToDelegate : GlobalType → Prop where
  | delegate {p q : String} {sid r} {cont : GlobalType} :
      UnfoldsToDelegate (.delegate p q sid r cont)
  | mu (t : String) (body : GlobalType) :
      UnfoldsToDelegate (body.substitute t (.mu t body)) → UnfoldsToDelegate (.mu t body)

/-- Number of leading `mu` binders. -/
def muHeight : GlobalType → Nat
  | .mu _ body => muHeight body + 1
  | _ => 0

/-- Substituting a variable that is unguarded-productive does not change the
number of leading binders (the variable cannot occur in head position). -/
theorem muHeight_substitute (t : String) (repl : GlobalType) :
    ∀ (g : GlobalType) (U : List String), g.isProductive (t :: U) = true →
      muHeight (g.substitute t repl) = muHeight g
  | .end, _, _ => by simp [GlobalType.substitute, muHeight]
  | .comm _ _ _, _, _ => by simp [GlobalType.substitute, muHeight]
  | .delegate _ _ _ _ _, _, _ => by simp [GlobalType.substitute, muHeight]
  | .var x, U, h => by
      have hx : x ≠ t := by
        intro hx; subst hx; simp [GlobalType.isProductive] at h
      simp [GlobalType.substitute, hx]
  | .mu s inner, U, h => by
      by_cases hs : s = t
      · simp [GlobalType.substitute, hs]
      · have h' : inner.isProductive (t :: s :: U) = true :=
          is_productive_swap inner s t U (by simpa [GlobalType.isProductive] using h)
        simp [GlobalType.substitute, hs, muHeight, muHeight_substitute t repl inner (s :: U) h']

/-- One `mu`-unfolding of a well-formed type strictly lowers `muHeight`. -/
theorem muHeight_unfold_lt (t : String) (body : GlobalType)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    muHeight (body.substitute t (.mu t body)) < muHeight (.mu t body) := by
  have hprod : body.isProductive [t] = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    simpa [GlobalType.isProductive] using hwf.2
  rw [muHeight_substitute t _ body [] hprod]
  simp [muHeight]

/-- Progress trichotomy for well-formed global types, derived from closedness,
non-empty communications and productivity (no `ReachesComm` assumption):
a well-formed type unfolds to `end`, to a delegation, or reaches a communication. -/
theorem wf_trichotomy (g : GlobalType) (hwf : g.wellFormed = true) :
    UnfoldsToEnd g ∨ UnfoldsToDelegate g ∨ ReachesComm g :=
  match g with
  | .end => Or.inl .done
  | .delegate _ _ _ _ _ => Or.inr (Or.inl .delegate)
  | .var _ => by simp [GlobalType.wellFormed, GlobalType.allVarsBound] at hwf
  | .comm s r bs => by
      refine Or.inr (Or.inr (.comm s r bs ?_))
      intro hnil; subst hnil
      simp [GlobalType.wellFormed, GlobalType.allCommsNonEmpty] at hwf
  | .mu t body =>
      have _hlt := muHeight_unfold_lt t body hwf
      match wf_trichotomy _ (well_formed_mu_unfold t body hwf) with
      | .inl h => .inl (.mu t body h)
      | .inr (.inl h) => .inr (.inl (.mu t body h))
      | .inr (.inr h) => .inr (.inr (.mu t body h))
termination_by muHeight g

/-! ## Terminal and Stuck Predicates -/

/-- A configuration is done (terminal) when its global type unfolds to `end`. -/
def Done (c : Configuration) : Prop :=
  UnfoldsToEnd c.globalType

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
theorem reaches_comm_implies_sync_can_step (g : GlobalType)
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
      have ⟨act, hcan⟩ := ih (well_formed_mu_unfold t body _hwf)
      exact ⟨act, SyncCanStep.mu t body act hcan⟩

/-- Types that reach a communication can step.

**Requires:**
- `hwf`: well-formedness (for structural properties)
- `hcomm`: the type reaches a communication (progress predicate)

**Proof:** By induction on the `ReachesComm` derivation.
- `comm`: Use `canStep.comm_head` with the first branch
- `mu`: Use `canStep.mu` with IH on the unfolded body -/
theorem reaches_comm_implies_can_step (g : GlobalType)
    (hwf : g.wellFormed = true)
    (hcomm : ReachesComm g) :
    ∃ act, canStep g act := by
  -- Get SyncCanStep, then convert to canStep.
  have ⟨act, hsync⟩ := reaches_comm_implies_sync_can_step g hwf hcomm
  exact ⟨act, hsync.to_can_step⟩

/-- Global progress: a well-formed global type that is neither finished nor a
(unmodeled) delegation can take a step. Reaching a communication is derived
from well-formedness, not assumed. -/
theorem wf_global_progress (g : GlobalType) (hwf : g.wellFormed = true)
    (hend : ¬UnfoldsToEnd g) (hdel : ¬UnfoldsToDelegate g) :
    ∃ act g', step g act g' := by
  rcases wf_trichotomy g hwf with h | h | h
  · exact absurd h hend
  · exact absurd h hdel
  · obtain ⟨act, hs⟩ := reaches_comm_implies_sync_can_step g hwf h
    obtain ⟨g', hst⟩ := sync_can_step_implies_step g act hs
    exact ⟨act, g', hst⟩

/-- Trichotomy for configurations of a well-formed global type: done, blocked
on an unmodeled delegation, or the global type can step. -/
theorem deadlock_free_trichotomy (c : Configuration) (hwf : c.globalType.wellFormed = true) :
    Done c ∨ UnfoldsToDelegate c.globalType ∨ ∃ act g', step c.globalType act g' := by
  by_cases hend : Done c
  · exact Or.inl hend
  by_cases hdel : UnfoldsToDelegate c.globalType
  · exact Or.inr (Or.inl hdel)
  exact Or.inr (Or.inr (wf_global_progress _ hwf hend hdel))

/-! ## Configuration Progress (Head Communications) -/

/-- Advance one process for the head step taking continuation `g'`. -/
def advanceProcess (g' : GlobalType) (act : GlobalActionR) (p : Process) : Process :=
  if Participant act p.role then { p with localType := trans g' p.role }
  else p

/-- `advanceProcess` realizes `ProcessAdvance` for a head communication step. -/
theorem advanceProcess_spec {bs : List (Label × GlobalType)} {g' : GlobalType}
    {act : GlobalActionR} (hmem : (act.label, g') ∈ bs) (p : Process) :
    ProcessAdvance (.comm act.sender act.receiver bs) act p (advanceProcess g' act p) where
  role_eq := by unfold advanceProcess; split <;> rfl
  advance := by
    intro hp
    refine ⟨trans g' p.role, ?_, by simp [advanceProcess, hp]⟩
    have hb : ∃ vt, (act.label, vt, trans g' p.role) ∈ transBranches bs p.role :=
      ⟨none, Choreography.Harmony.mem_trans_branches_of_mem bs act.label g' p.role hmem⟩
    by_cases hs : p.role = act.sender
    · rw [trans_comm_sender _ _ _ bs hs]; exact .send hs hb
    · have hr := hp.resolve_left hs
      rw [trans_comm_receiver _ _ _ bs hr hs]; exact .recv hr hs hb
  frame := by intro hp; simp [advanceProcess, hp]

/-- Pointwise advancement along a mapped list. -/
theorem forall2_map_advance {bs : List (Label × GlobalType)} {g' : GlobalType}
    {act : GlobalActionR} (hmem : (act.label, g') ∈ bs) :
    ∀ ps : List Process, List.Forall₂ (ProcessAdvance (.comm act.sender act.receiver bs) act)
      ps (ps.map (advanceProcess g' act))
  | [] => .nil
  | p :: ps => .cons (advanceProcess_spec hmem p) (forall2_map_advance hmem ps)

/-- A configuration headed by a communication steps along any of its branches. -/
theorem head_config_step (c : Configuration) {s r : String} {bs : List (Label × GlobalType)}
    {label : Label} {cont : GlobalType} (hg : c.globalType = .comm s r bs)
    (hmem : (label, cont) ∈ bs) :
    ConfigStep c ⟨cont, c.processes.map (advanceProcess cont ⟨s, r, label⟩)⟩ ⟨s, r, label⟩ where
  global_step := by rw [hg]; exact step.comm_head s r bs label cont hmem
  processes_advance := by
    rw [hg]; exact forall2_map_advance (act := ⟨s, r, label⟩) hmem c.processes

/-! ## Deadlock Freedom Theorem -/

/-- Deadlock freedom for communication-headed configurations: a well-typed
configuration whose (closed, well-formed, blind, label-unique) global type is a
communication can step, and the result is again well-typed. Non-emptiness of
the branches is derived from well-formedness.

`mu`-headed configurations are not covered at the configuration level (see
`deadlock_free_trichotomy` for the global-level statement). -/
theorem deadlock_free (c : Configuration) {s r : String} {bs : List (Label × GlobalType)}
    (htyped : WellTypedConfig c) (hg : c.globalType = .comm s r bs)
    (huniq : c.globalType.uniqueBranchLabels = true) (hclosed : c.globalType.isClosed = true)
    (hwf : c.globalType.wellFormed = true)
    (hblind : Choreography.Projection.Blind.isBlind c.globalType = true) :
    ∃ c' act, ConfigStep c c' act ∧ WellTypedConfig c' := by
  have hcomm : ReachesComm c.globalType := by
    rcases wf_trichotomy _ hwf with h | h | h <;> rw [hg] at h
    · cases h
    · cases h
    · exact hg ▸ h
  rw [hg] at hcomm
  cases hcomm with
  | comm _ _ _ hne =>
    obtain ⟨label, cont, hmem⟩ := first_branch_mem hne
    have hstep := head_config_step c hg hmem
    exact ⟨_, _, hstep, step_preserves_typing htyped ⟨⟨bs, hg⟩, huniq, hclosed, hwf, hblind⟩ hstep⟩

/-- Corollary: such configurations are not stuck. -/
theorem not_stuck (c : Configuration) {s r : String} {bs : List (Label × GlobalType)}
    (htyped : WellTypedConfig c) (hg : c.globalType = .comm s r bs)
    (huniq : c.globalType.uniqueBranchLabels = true) (hclosed : c.globalType.isClosed = true)
    (hwf : c.globalType.wellFormed = true)
    (hblind : Choreography.Projection.Blind.isBlind c.globalType = true) :
    ¬Stuck c := by
  intro ⟨_, hnp⟩
  obtain ⟨c', act, hstep, _⟩ := deadlock_free c htyped hg huniq hclosed hwf hblind
  exact hnp ⟨c', act, hstep⟩

/-! ## Claims Bundle -/

/-- Claims bundle for deadlock freedom. -/
structure Claims where
  /-- Global progress trichotomy for well-formed types. -/
  trichotomy : ∀ c, c.globalType.wellFormed = true →
      Done c ∨ UnfoldsToDelegate c.globalType ∨ ∃ act g', step c.globalType act g'
  /-- Communication-headed configurations step to well-typed configurations. -/
  deadlock_free : ∀ c s r bs, WellTypedConfig c → c.globalType = .comm s r bs →
      c.globalType.uniqueBranchLabels = true → c.globalType.isClosed = true →
      c.globalType.wellFormed = true →
      Choreography.Projection.Blind.isBlind c.globalType = true →
      ∃ c' act, ConfigStep c c' act ∧ WellTypedConfig c'

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  trichotomy := deadlock_free_trichotomy
  deadlock_free := fun c _ _ _ h1 h2 h3 h4 h5 h6 => deadlock_free c h1 h2 h3 h4 h5 h6

end Semantics.DeadlockFreedom
