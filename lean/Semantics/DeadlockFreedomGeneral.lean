import Semantics.DeadlockFreedom
import Semantics.SubjectReductionGeneral

/-
The Problem. `deadlock_free` requires the global type to be literally a
communication. A well-typed configuration whose global type is `mu`-headed
must also make progress.

Solution Structure. `wf_trichotomy` yields `ReachesComm` for a non-finished,
non-delegating well-formed type; `reaches_comm_implies_sync_can_step` gives a
synchronous step (a head communication under `mu` layers). Each process is
advanced by `advanceProcess`, justified by induction on `SyncCanStep`, transporting
typing through `mu`-unfoldings with `wellTyped_mu_unfold`.
-/

/-! # Semantics.DeadlockFreedomGeneral

Configuration-level deadlock freedom with no head-shape premise.

## Main Results

- `advanceProcess_sync_spec`: typed processes advance along a synchronous step.
- `deadlock_free_general`: `¬ Done c → CanProgress c` (plus well-typedness of
  the successor) for well-typed configurations of closed, well-formed, blind,
  label-unique global types that do not unfold to a delegation.
- `Claims`, `claims`
-/

namespace Semantics.DeadlockFreedom

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Semantics.SubjectReduction

/-- Along a synchronous enabling (`SyncCanStep`) of a well-formed global type,
every typed process advances by `advanceProcess`. -/
theorem advanceProcess_sync_spec {g : GlobalType} {act : GlobalActionR}
    (hsync : SyncCanStep g act) (hwf : g.wellFormed = true) :
    ∀ p : Process, p.wellTyped g → ProcessAdvance act p (advanceProcess act p) := by
  induction hsync with
  | comm_head s r bs label cont hmem =>
      intro p ht
      exact advanceProcess_spec (act := ⟨s, r, label⟩) hmem ht
        (trans_well_formed_of_well_formed _ _ hwf)
  | mu t body act _ ih =>
      intro p ht
      exact ih (well_formed_mu_unfold t body hwf) p
        ⟨ht.1, wellTyped_mu_unfold hwf ht.1 ht.2⟩

/-- Pointwise advancement of a typed process list along a synchronous enabling. -/
theorem forall2_map_advance_sync {g : GlobalType} {act : GlobalActionR}
    (hsync : SyncCanStep g act) (hwf : g.wellFormed = true) :
    ∀ ps : List Process, (∀ p ∈ ps, p.wellTyped g) →
      List.Forall₂ (ProcessAdvance act) ps (ps.map (advanceProcess act))
  | [], _ => .nil
  | p :: ps, ht =>
      .cons (advanceProcess_sync_spec hsync hwf p (ht p List.mem_cons_self))
        (forall2_map_advance_sync hsync hwf ps (fun q hq => ht q (List.mem_cons_of_mem _ hq)))

/-- A well-typed configuration of a well-formed global type that is neither done
nor blocked on an (unmodeled) delegation has a configuration step. -/
theorem can_progress_general (c : Configuration) (htyped : WellTypedConfig c)
    (hwf : c.globalType.wellFormed = true) (hdel : ¬ UnfoldsToDelegate c.globalType)
    (hdone : ¬ Done c) : CanProgress c := by
  have hcomm : ReachesComm c.globalType := by
    rcases wf_trichotomy _ hwf with h | h | h
    · exact absurd h hdone
    · exact absurd h hdel
    · exact h
  obtain ⟨act, hsync⟩ := reaches_comm_implies_sync_can_step _ hwf hcomm
  obtain ⟨g', hst⟩ := sync_can_step_implies_step _ act hsync
  exact ⟨⟨g', c.processes.map (advanceProcess act)⟩, act, hst,
    forall2_map_advance_sync hsync hwf c.processes htyped.processes_typed⟩

/-- Deadlock freedom without a head-shape premise: a well-typed configuration
whose global type is closed, well-formed, blind, label-unique and does not
unfold to a delegation is either done or steps to a well-typed configuration. -/
theorem deadlock_free_general (c : Configuration) (htyped : WellTypedConfig c)
    (hh : StepHyps c) (hdel : ¬ UnfoldsToDelegate c.globalType) (hdone : ¬ Done c) :
    ∃ c' act, ConfigStep c c' act ∧ WellTypedConfig c' := by
  obtain ⟨c', act, hstep⟩ := can_progress_general c htyped hh.wf hdel hdone
  exact ⟨c', act, hstep, step_preserves_typing_general htyped hh hstep⟩

/-- Corollary: such configurations are not stuck. -/
theorem not_stuck_general (c : Configuration) (htyped : WellTypedConfig c)
    (hwf : c.globalType.wellFormed = true) (hdel : ¬ UnfoldsToDelegate c.globalType) :
    ¬ Stuck c :=
  fun ⟨hdone, hnp⟩ => hnp (can_progress_general c htyped hwf hdel hdone)

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
  /-- Configuration progress for any well-formed, non-delegating global type. -/
  can_progress : ∀ c, WellTypedConfig c → c.globalType.wellFormed = true →
      ¬ UnfoldsToDelegate c.globalType → ¬ Done c → CanProgress c
  /-- General deadlock freedom with preservation of typing. -/
  deadlock_free_general : ∀ c, WellTypedConfig c → StepHyps c →
      ¬ UnfoldsToDelegate c.globalType → ¬ Done c →
      ∃ c' act, ConfigStep c c' act ∧ WellTypedConfig c'

/-- Build the claims bundle from proven theorems. -/
def claims : Semantics.DeadlockFreedom.Claims where
  trichotomy := deadlock_free_trichotomy
  deadlock_free := fun c _ _ _ h1 h2 h3 h4 h5 h6 => deadlock_free c h1 h2 h3 h4 h5 h6
  can_progress := can_progress_general
  deadlock_free_general := deadlock_free_general

end Semantics.DeadlockFreedom
