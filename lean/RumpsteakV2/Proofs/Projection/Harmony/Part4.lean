import RumpsteakV2.Proofs.Projection.Harmony.Part3

namespace RumpsteakV2.Proofs.Projection.Harmony
/-! ### Non-participant Step Preservation

We prove by mutual induction on `step` and `BranchesStep`. The comm_head/comm_async cases
use branch coherence and trans_comm_other, and the mu case uses trans_substitute_unfold. -/
/-- Core recursion for proj_trans_other_step (case split on step/BranchesStep). -/
private theorem proj_trans_other_step_core (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g') (hclosed : g.isClosed = true) (hwf : g.wellFormed = true)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) (hproj : ProjectableClosedWellFormed) :
    EQ2 (projTrans g' role) (projTrans g role) := by
  -- Apply the step recursor with case-specific helper lemmas.
  refine
    @step.rec
      (motive_1 := StepMotive)
      (motive_2 := BranchMotive)
      (fun sender receiver branches label cont hmem hclosed hwf role hns hnr =>
        proj_trans_other_step_comm_head sender receiver branches label cont role hmem hclosed hwf hns hnr hproj)
      (fun sender receiver branches branches' act _label _cont _hns_cond _hcond _hmem _hcan hbstep
          ih_bstep hclosed hwf role hns hnr =>
        proj_trans_other_step_comm_async sender receiver branches branches' act hbstep ih_bstep
          hclosed hwf role hns hnr)
      (fun t body act g' hstep_sub ih_step hclosed hwf role hns hnr =>
        proj_trans_other_step_mu t body act g' hstep_sub ih_step hclosed hwf role hns hnr)
      (fun act _hclosed _hwf role hns hnr =>
        proj_trans_other_step_branches_nil act role hns hnr)
      (fun label g g' rest rest' act _hstep_g _hbstep_rest ih_step ih_bstep hclosed hwf role hns hnr =>
        proj_trans_other_step_branches_cons label g g' rest rest' act ih_step ih_bstep
          hclosed hwf role hns hnr)
      g act g' hstep hclosed hwf role hns hnr

/-- Non-participating roles have unchanged projections through a step. -/
theorem proj_trans_other_step (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g')
    (hclosed : g.isClosed = true)
    (hwf : g.wellFormed = true)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver)
    (hproj : ProjectableClosedWellFormed) :
    EQ2 (projTrans g' role) (projTrans g role) := by
  -- Delegate to the step-recursion core.
  exact proj_trans_other_step_core g g' act role hstep hclosed hwf hns hnr hproj

/- BranchesStep preserves transBranches up to branch-wise EQ2 for non-participants.

When branches step to branches' via BranchesStep, the transBranches are related
by BranchesRel EQ2 for any role not involved in the action.

This captures the semantic property that stepping inside branches doesn't affect
non-participant projections: each branch steps, and projection commutes with stepping.

Proven by induction on BranchesStep, using proj_trans_other_step for each branch.

**Note:** Requires all branch continuations to be closed, wellFormed, and projectable. -/
/-- Helper: BranchesStep.cons case for non-participant preservation. -/
private theorem branches_step_preserves_trans_cons
    (label : Label) (g g' : GlobalType) (rest rest' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hstep_g : step g act g')
    (ih : (∀ p ∈ rest, p.2.isClosed = true) →
      (∀ p ∈ rest, p.2.wellFormed = true) →
      BranchesRel EQ2 (transBranches rest' role) (transBranches rest role))
    (hclosed : ∀ p ∈ ((label, g) :: rest), p.2.isClosed = true)
    (hwf : ∀ p ∈ ((label, g) :: rest), p.2.wellFormed = true)
    (hproj : ProjectableClosedWellFormed)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (transBranches ((label, g') :: rest') role)
      (transBranches ((label, g) :: rest) role) := by
  -- Build the cons case from the head step and the tail IH.
  simp only [transBranches]
  apply List.Forall₂.cons
  · constructor
    · rfl
    · have hg_closed : g.isClosed = true := hclosed (label, g) List.mem_cons_self
      have hg_wf : g.wellFormed = true := hwf (label, g) List.mem_cons_self
      exact proj_trans_other_step g g' act role hstep_g hg_closed hg_wf hns hnr hproj
  · have hrest_closed : ∀ p ∈ rest, p.2.isClosed = true := fun x hx =>
      hclosed x (List.mem_cons_of_mem (label, g) hx)
    have hrest_wf : ∀ p ∈ rest, p.2.wellFormed = true := fun x hx =>
      hwf x (List.mem_cons_of_mem (label, g) hx)
    exact ih hrest_closed hrest_wf

theorem branches_step_preserves_trans (branches branches' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hstep : BranchesStep step branches act branches')
    (hclosed : ∀ p ∈ branches, p.2.isClosed = true)
    (hwf : ∀ p ∈ branches, p.2.wellFormed = true)
    (hproj : ProjectableClosedWellFormed)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (transBranches branches' role) (transBranches branches role) := by
  -- Induct over the branch-step derivation.
  induction hstep with
  | nil =>
      simp only [transBranches]
      exact List.Forall₂.nil
  | cons label g g' rest rest' act hstep_g _hbstep_rest ih =>
      exact branches_step_preserves_trans_cons label g g' rest rest' act role hstep_g
        (fun hclosed' hwf' => ih hclosed' hwf' hns hnr)
        hclosed hwf hproj hns hnr

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

end RumpsteakV2.Proofs.Projection.Harmony
