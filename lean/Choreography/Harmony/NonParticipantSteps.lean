import Choreography.Harmony.NonParticipantHelpers

/-! # Choreography.Harmony.NonParticipantSteps

Non-participant step preservation proof and Claims bundle.
-/

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.

Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis
over the operational/projection relation.
-/

namespace Choreography.Harmony
/-! ## Non-participant Step Preservation

We prove by mutual induction on `step` and `BranchesStep`. The comm_head/comm_async cases
use branch coherence and trans_comm_other, and the mu case uses trans_substitute_unfold. -/

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
open Choreography.Projection.Project
  (ProjectableClosedWellFormed ProjectableClosedWellFormedBlind
   ProjectableClosedWellFormedBlind_implies_ProjectableClosedWellFormed)
open Choreography.Projection.Blind (isBlind isBlind_comm_branches)
open Semantics.EnvStep

/-- Core recursion for proj_trans_other_step (case split on step/BranchesStep). -/
private theorem proj_trans_other_step_core (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g') (hclosed : g.isClosed = true) (hwf : g.wellFormed = true)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver)
    (hblind : isBlind g = true) :
    EQ2 (projTrans g' role) (projTrans g role) := by
  -- Apply the step recursor with case-specific helper lemmas.
  refine
    @step.rec
      (motive_1 := StepMotive)
      (motive_2 := BranchMotive)
      (fun sender receiver branches label cont hmem hclosed hwf hblind role hns hnr =>
        have hproj_comm : ProjectableClosedWellFormed (GlobalType.comm sender receiver branches) :=
          ProjectableClosedWellFormedBlind_implies_ProjectableClosedWellFormed ⟨hclosed, hwf, hblind⟩
        proj_trans_other_step_comm_head sender receiver branches label cont role hmem hclosed hwf hns hnr
          hproj_comm)
      (fun sender receiver branches branches' act _label _cont _hns_cond _hcond _hmem _hcan hbstep
          ih_bstep hclosed hwf hblind role hns hnr =>
        have hblind_branches : ∀ p ∈ branches, isBlind p.2 = true :=
          isBlind_comm_branches hblind
        proj_trans_other_step_comm_async sender receiver branches branches' act hbstep
          (fun hc hw role hns hnr => ih_bstep hc hw hblind_branches role hns hnr)
          hclosed hwf role hns hnr)
      (fun t body act g' hstep_sub ih_step hclosed hwf hblind role hns hnr =>
        proj_trans_other_step_mu t body act g' hstep_sub ih_step hclosed hwf hblind role hns hnr)
      (fun act _hclosed _hwf _hblind role hns hnr =>
        proj_trans_other_step_branches_nil act role hns hnr)
      (fun label g g' rest rest' act _hstep_g _hbstep_rest ih_step ih_bstep hclosed hwf hblind role hns hnr =>
        proj_trans_other_step_branches_cons label g g' rest rest' act ih_step ih_bstep
          hclosed hwf hblind role hns hnr)
      g act g' hstep hclosed hwf hblind role hns hnr

/-- Non-participating roles have unchanged projections through a step. -/


theorem proj_trans_other_step (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g')
    (hclosed : g.isClosed = true)
    (hwf : g.wellFormed = true)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver)
    (hblind : isBlind g = true) :
    EQ2 (projTrans g' role) (projTrans g role) := by
  -- Delegate to the step-recursion core.
  exact proj_trans_other_step_core g g' act role hstep hclosed hwf hns hnr hblind

/- BranchesStep preserves projTransBranches up to branch-wise EQ2 for non-participants.

When branches step to branches' via BranchesStep, the projTransBranches are related
by BranchesRel EQ2 for any role not involved in the action.

This captures the semantic property that stepping inside branches doesn't affect
non-participant projections: each branch steps, and projection commutes with stepping.

Proven by induction on BranchesStep, using proj_trans_other_step for each branch.

**Note:** Requires all branch continuations to be closed, wellFormed, and blind. -/
/-- Helper: BranchesStep.cons case for non-participant preservation. -/
private theorem branches_step_preserves_trans_cons
    (label : Label) (g g' : GlobalType) (rest rest' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hstep_g : step g act g')
    (ih : (∀ p ∈ rest, p.2.isClosed = true) →
      (∀ p ∈ rest, p.2.wellFormed = true) →
      (∀ p ∈ rest, isBlind p.2 = true) →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        BranchesRel EQ2 (projTransBranches rest' role) (projTransBranches rest role))
    (hclosed : ∀ p ∈ ((label, g) :: rest), p.2.isClosed = true)
    (hwf : ∀ p ∈ ((label, g) :: rest), p.2.wellFormed = true)
    (hblind_branches : ∀ p ∈ ((label, g) :: rest), isBlind p.2 = true)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (projTransBranches ((label, g') :: rest') role)
      (projTransBranches ((label, g) :: rest) role) := by
  -- Build the cons case from the head step and the tail IH.
  refine proj_trans_other_step_branches_cons label g g' rest rest' act
    (fun hg_closed hg_wf hg_blind role hns hnr => by
      exact proj_trans_other_step g g' act role hstep_g hg_closed hg_wf hns hnr hg_blind)
    (fun hrest_closed hrest_wf hrest_blind role hns hnr => by
      exact ih hrest_closed hrest_wf hrest_blind role hns hnr)
    hclosed hwf hblind_branches role hns hnr

/-- Branch-level steps preserve trans projection for non-participant roles. -/


theorem branches_step_preserves_trans (branches branches' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hstep : BranchesStep step branches act branches')
    (hclosed : ∀ p ∈ branches, p.2.isClosed = true)
    (hwf : ∀ p ∈ branches, p.2.wellFormed = true)
    (hblind : ∀ p ∈ branches, isBlind p.2 = true)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (projTransBranches branches' role) (projTransBranches branches role) := by
  -- Induct over the branch-step derivation.
  revert role hns hnr
  induction hstep with
  | nil act =>
      intro role hns hnr
      simpa using (proj_trans_other_step_branches_nil (act := act) (role := role) hns hnr)
  | cons label g g' rest rest' act hstep_g _hbstep_rest ih =>
      intro role hns hnr
      exact branches_step_preserves_trans_cons label g g' rest rest' act role hstep_g
        ih
        hclosed hwf hblind hns hnr

/-! ## Claims Bundle -/

/-- Domain containment for EnvStep: post-step domain is subset of pre-step domain.

Note: EnvStep does NOT preserve domain equality because global steps can shrink
the role set (step_roles_subset). Instead, we have containment.

For domain equality, use EnvStepOnto which projects onto a fixed role set. -/


theorem envstep_dom_subset {env env' : ProjectedEnv} {act : GlobalActionR}
    (h : EnvStep env act env') :
    ∀ p, p ∈ env'.map Prod.fst → p ∈ env.map Prod.fst := by
  -- Reduce to the global step case and apply step_roles_subset.
  cases h with
  | of_global g g' _ hstep =>
      intro p hp
      simp only [projEnv_dom] at hp ⊢
      exact step_roles_subset g g' _ hstep p hp

/-- Build the claims bundle from proven theorems. -/


def claims : Claims where
  -- Package the main harmony theorems.
  harmony := step_harmony
  dom_subset := fun _ _ _ h => envstep_dom_subset h

end Choreography.Harmony
