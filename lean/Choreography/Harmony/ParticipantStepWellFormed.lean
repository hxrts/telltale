import Choreography.Harmony.Substitution

/-! # Choreography.Harmony.ParticipantStepWellFormed

Well-formedness preservation lemmas for global-step transitions.
-/

/-
The Problem. Show global operational steps preserve the well-formedness invariant.

Solution Structure. Factor branch-level well-formedness helpers, then apply the step recursor.
-/

namespace Choreography.Harmony
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
open Choreography.Projection.Project
  (trans_comm_sender trans_comm_receiver trans_comm_other trans_wellFormed_of_wellFormed)
open Choreography.Projection.Project (ProjectableClosedWellFormed)
open Choreography.Projection.Projectb (CProject)

/-! ## Well-formedness Preservation for Steps -/

private theorem allVarsBoundBranches_of_forall
    (branches : List (Label × GlobalType)) (bound : List String)
    (h : ∀ b ∈ branches, b.2.allVarsBound bound = true) :
    allVarsBoundBranches branches bound = true := by
  induction branches with
  | nil =>
      simp [allVarsBoundBranches]
  | cons head tail ih =>
      cases head with
      | mk label cont =>
          have hhead : cont.allVarsBound bound = true := h (label, cont) (by simp)
          have htail : ∀ b ∈ tail, b.2.allVarsBound bound = true := by
            intro b hb
            exact h b (by simp [hb])
          have htail' := ih htail
          simp [allVarsBoundBranches, hhead, htail']

private theorem allCommsNonEmptyBranches_of_forall
    (branches : List (Label × GlobalType))
    (h : ∀ b ∈ branches, b.2.allCommsNonEmpty = true) :
    allCommsNonEmptyBranches branches = true := by
  induction branches with
  | nil =>
      simp [allCommsNonEmptyBranches]
  | cons head tail ih =>
      cases head with
      | mk label cont =>
          have hhead : cont.allCommsNonEmpty = true := h (label, cont) (by simp)
          have htail : ∀ b ∈ tail, b.2.allCommsNonEmpty = true := by
            intro b hb
            exact h b (by simp [hb])
          have htail' := ih htail
          simp [allCommsNonEmptyBranches, hhead, htail']

private theorem noSelfCommBranches_of_forall
    (branches : List (Label × GlobalType))
    (h : ∀ b ∈ branches, b.2.noSelfComm = true) :
    noSelfCommBranches branches = true := by
  induction branches with
  | nil =>
      simp [noSelfCommBranches]
  | cons head tail ih =>
      cases head with
      | mk label cont =>
          have hhead : cont.noSelfComm = true := h (label, cont) (by simp)
          have htail : ∀ b ∈ tail, b.2.noSelfComm = true := by
            intro b hb
            exact h b (by simp [hb])
          have htail' := ih htail
          simp [noSelfCommBranches, hhead, htail']

private theorem isProductiveBranches_of_forall
    (branches : List (Label × GlobalType)) (unguarded : List String)
    (h : ∀ b ∈ branches, b.2.isProductive unguarded = true) :
    isProductiveBranches branches unguarded = true := by
  induction branches with
  | nil =>
      simp [isProductiveBranches]
  | cons head tail ih =>
      cases head with
      | mk label cont =>
          have hhead : cont.isProductive unguarded = true := h (label, cont) (by simp)
          have htail : ∀ b ∈ tail, b.2.isProductive unguarded = true := by
            intro b hb
            exact h b (by simp [hb])
          have htail' := ih htail
          simp [isProductiveBranches, hhead, htail']

/-! ## comm_wellFormed Helpers -/

private lemma branch_wf_parts {b : Label × GlobalType} (h : b.2.wellFormed = true) :
    b.2.allVarsBound = true ∧ b.2.allCommsNonEmpty = true ∧
      b.2.noSelfComm = true ∧ b.2.isProductive = true := by
  -- Split the wellFormed conjuncts for branch-level reuse.
  simpa [GlobalType.wellFormed, Bool.and_eq_true, and_assoc] using h

private lemma branches_wf_parts (branches : List (Label × GlobalType))
    (hbranches_wf : ∀ b ∈ branches, b.2.wellFormed = true) :
    (∀ b ∈ branches, b.2.allVarsBound = true) ∧
    (∀ b ∈ branches, b.2.allCommsNonEmpty = true) ∧
    (∀ b ∈ branches, b.2.noSelfComm = true) ∧
    (∀ b ∈ branches, b.2.isProductive = true) := by
  -- Aggregate the branch-level wellFormed projections.
  have hparts : ∀ b ∈ branches,
      b.2.allVarsBound = true ∧ b.2.allCommsNonEmpty = true ∧
        b.2.noSelfComm = true ∧ b.2.isProductive = true := by
    intro b hb; exact branch_wf_parts (hbranches_wf b hb)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb; exact (hparts b hb).1
  · intro b hb; exact (hparts b hb).2.1
  · intro b hb; exact (hparts b hb).2.2.1
  · intro b hb; exact (hparts b hb).2.2.2

private theorem comm_wellFormed_of_branches
    (sender receiver : String) (branches : List (Label × GlobalType))
    (hne : branches ≠ []) (hneq : sender ≠ receiver)
    (hbranches_wf : ∀ b ∈ branches, b.2.wellFormed = true) :
    (GlobalType.comm sender receiver branches).wellFormed = true := by
  -- Pull branch-level wellFormed parts once, then aggregate.
  obtain ⟨hvars_br, hallcomms_br, hnoself_br, hprod_br⟩ :=
    branches_wf_parts branches hbranches_wf
  have hvars : allVarsBoundBranches branches [] = true :=
    allVarsBoundBranches_of_forall branches [] hvars_br
  have hallcomms : allCommsNonEmptyBranches branches = true :=
    allCommsNonEmptyBranches_of_forall branches hallcomms_br
  have hnoself : noSelfCommBranches branches = true := noSelfCommBranches_of_forall branches hnoself_br
  have hprod : isProductiveBranches branches [] = true := isProductiveBranches_of_forall branches [] hprod_br
  have hne' : branches.isEmpty = false := by
    cases hbranches : branches with
    | nil =>
        exfalso
        apply hne
        simp [hbranches]
    | cons _ _ =>
        simp
  simp [GlobalType.wellFormed, GlobalType.allVarsBound, GlobalType.allCommsNonEmpty,
    GlobalType.noSelfComm, GlobalType.isProductive, hvars, hallcomms, hnoself, hprod, hne', hneq]

private lemma comm_sender_ne_receiver_of_wf {sender receiver : String} {branches : List (Label × GlobalType)}
    (hwf_comm : (GlobalType.comm sender receiver branches).wellFormed = true) : sender ≠ receiver := by
  -- noSelfComm rules out sender = receiver.
  have hnoself : (GlobalType.comm sender receiver branches).noSelfComm = true := by
    have hwf' := hwf_comm; simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf'; exact hwf'.1.2
  by_cases h : sender = receiver
  · subst h
    have : False := by
      simp [GlobalType.noSelfComm] at hnoself
    exact this.elim
  · exact h

private lemma comm_branches_nonempty_of_wf {sender receiver : String} {branches : List (Label × GlobalType)}
    (hwf_comm : (GlobalType.comm sender receiver branches).wellFormed = true) : branches ≠ [] := by
  -- allCommsNonEmpty implies branches are non-empty.
  have hallcomms : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true := by
    have hwf' := hwf_comm; simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf'; exact hwf'.1.1.2
  have hne' : branches.isEmpty = false := by
    simp [GlobalType.allCommsNonEmpty, Bool.and_eq_true] at hallcomms; simpa using hallcomms.1
  intro hnil; subst hnil; simp at hne'

private theorem branchesStep_nonempty
    {branches branches' : List (Label × GlobalType)} {act : GlobalActionR}
    (hstep : BranchesStep step branches act branches')
    (hne : branches ≠ []) : branches' ≠ [] := by
  cases hstep with
  | nil =>
      cases (hne rfl)
  | cons _ _ _ _ _ _ _ _ =>
      intro hnil
      cases hnil

private abbrev StepWFMotive (g : GlobalType) (act : GlobalActionR) (g' : GlobalType) (_ : step g act g') : Prop :=
  g.wellFormed = true → g'.wellFormed = true

private abbrev BranchWFMotive (bs : List (Label × GlobalType)) (act : GlobalActionR)
    (bs' : List (Label × GlobalType)) (_ : BranchesStep step bs act bs') : Prop :=
  (∀ p ∈ bs, p.2.wellFormed = true) → ∀ p ∈ bs', p.2.wellFormed = true

private theorem step_preserves_wf_comm_head
    (sender receiver : String) (branches : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (hmem : (label, cont) ∈ branches)
    (hwf_comm : (GlobalType.comm sender receiver branches).wellFormed = true) :
    cont.wellFormed = true := by
  -- Directly select a well-formed branch.
  exact GlobalType.wellFormed_comm_branches sender receiver branches hwf_comm (label, cont) hmem

private theorem step_preserves_wf_comm_async
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (act : GlobalActionR)
    (_label : Label) (_cont : GlobalType)
    (_hns_cond : act.sender ≠ receiver)
    (_hcond : act.sender = sender → act.receiver ≠ receiver)
    (_hmem : (_label, _cont) ∈ branches)
    (_hcan : canStep _cont act)
    (hbstep : BranchesStep step branches act branches')
    (ih_bstep : BranchWFMotive branches act branches' hbstep)
    (hwf_comm : (GlobalType.comm sender receiver branches).wellFormed = true) :
    (GlobalType.comm sender receiver branches').wellFormed = true := by
  -- Comm/async: lift branch wellFormed and rebuild the comm node.
  have hbranches_wf : ∀ p ∈ branches, p.2.wellFormed = true :=
    GlobalType.wellFormed_comm_branches sender receiver branches hwf_comm
  have hbranches'_wf : ∀ p ∈ branches', p.2.wellFormed = true := ih_bstep hbranches_wf
  have hneq : sender ≠ receiver := comm_sender_ne_receiver_of_wf hwf_comm
  have hne : branches ≠ [] := comm_branches_nonempty_of_wf hwf_comm
  have hne' : branches' ≠ [] := branchesStep_nonempty hbstep hne
  exact comm_wellFormed_of_branches sender receiver branches' hne' hneq hbranches'_wf

private theorem step_preserves_wf_mu
    (t : String) (body : GlobalType) (act : GlobalActionR) (g' : GlobalType)
    (hstep_sub : step (body.substitute t (.mu t body)) act g')
    (ih_step : StepWFMotive _ _ _ hstep_sub)
    (hwf_mu : (GlobalType.mu t body).wellFormed = true) : g'.wellFormed = true := by
  -- Push wellFormedness through mu-unfold then apply IH.
  have hsubst_wf : (body.substitute t (.mu t body)).wellFormed = true :=
    wellFormed_mu_unfold t body hwf_mu
  exact ih_step hsubst_wf

private theorem branches_wf_nil (_act : GlobalActionR)
    (_hwf_branches : ∀ p ∈ ([] : List (Label × GlobalType)), p.2.wellFormed = true) :
    ∀ p ∈ ([] : List (Label × GlobalType)), p.2.wellFormed = true := by
  intro p hp; cases hp

private theorem branches_wf_cons
    (label : Label) (g g' : GlobalType) (rest rest' : List (Label × GlobalType)) (act : GlobalActionR)
    (hstep_g : step g act g') (_hbstep_rest : BranchesStep step rest act rest')
    (ih_step : StepWFMotive _ _ _ hstep_g)
    (ih_bstep : BranchWFMotive rest act rest' _hbstep_rest)
    (hwf_rest : ∀ p ∈ ((label, g) :: rest), p.2.wellFormed = true) :
    ∀ p ∈ ((label, g') :: rest'), p.2.wellFormed = true := by
  -- Split head/tail cases and use IHs.
  intro p hp
  cases hp with
  | head =>
      have hg_wf : g.wellFormed = true := hwf_rest (label, g) List.mem_cons_self
      have hg'_wf : g'.wellFormed = true := ih_step hg_wf
      simpa using hg'_wf
  | tail _ hp' =>
      have hwf_tail : ∀ q ∈ rest, q.2.wellFormed = true := fun q hq =>
        hwf_rest q (List.mem_cons_of_mem (label, g) hq)
      exact ih_bstep hwf_tail p hp'

theorem step_preserves_wellFormed (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hwf : g.wellFormed = true) : g'.wellFormed = true := by
  -- Recursor with constructor-specific helpers.
  refine @step.rec (motive_1 := StepWFMotive) (motive_2 := BranchWFMotive)
    step_preserves_wf_comm_head step_preserves_wf_comm_async step_preserves_wf_mu
    branches_wf_nil branches_wf_cons g act g' hstep hwf


end Choreography.Harmony
