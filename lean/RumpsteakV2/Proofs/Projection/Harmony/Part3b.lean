import RumpsteakV2.Proofs.Projection.Harmony.Part3
import RumpsteakV2.Protocol.Projection.Blind

namespace RumpsteakV2.Proofs.Projection.Harmony
/-! ### Non-participant mu/branch helpers

This file isolates the mu/branch-specific helpers for non-participant step preservation,
keeping Part3 under the 600-line cap.
-/

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Props
open RumpsteakV2.Protocol.Projection.Trans (trans_wellFormed_of_wellFormed)
open RumpsteakV2.Protocol.Projection.Blind (isBlind isBlind_mu_body isBlind_substitute)

private theorem proj_trans_other_step_mu_chain
    (t : String) (body : GlobalType) (role : String)
    (hclosed : (GlobalType.mu t body).isClosed = true)
    (hsubst_wf : (body.substitute t (.mu t body)).wellFormed = true)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    EQ2 (projTrans (body.substitute t (.mu t body)) role) (projTrans (.mu t body) role) := by
  -- Unfold-substitute chain with well-formedness witnesses.
  have h2 := trans_substitute_unfold t body role hclosed
  have h3 : EQ2 (projTrans (.mu t body) role).unfold (projTrans (.mu t body) role) := by
    exact EQ2_symm (EQ2_unfold_right (EQ2_refl (projTrans (.mu t body) role)))
  have hWFb := trans_wellFormed_of_wellFormed (body.substitute t (.mu t body)) role hsubst_wf
  have hWFc := trans_wellFormed_of_wellFormed (.mu t body) role hwf
  have hWFunfold := LocalTypeR.WellFormed.unfold hWFc
  exact EQ2_trans_wf h2 h3 hWFb hWFunfold hWFc

/-- Helper: mu case for non-participants. -/
theorem proj_trans_other_step_mu
    (t : String) (body : GlobalType) (act : GlobalActionR) (g' : GlobalType)
    (hstep_sub : step (body.substitute t (.mu t body)) act g')
    (ih_step :
      (body.substitute t (.mu t body)).isClosed = true →
      (body.substitute t (.mu t body)).wellFormed = true →
      isBlind (body.substitute t (.mu t body)) = true →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        EQ2 (projTrans g' role) (projTrans (body.substitute t (.mu t body)) role))
    (hclosed : (GlobalType.mu t body).isClosed = true)
    (hwf : (GlobalType.mu t body).wellFormed = true)
    (hblind : isBlind (GlobalType.mu t body) = true)
    (role : String) (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    EQ2 (projTrans g' role) (projTrans (GlobalType.mu t body) role) := by
  -- Chain IH with trans_substitute_unfold and the unfold lemma.
  have hsubst_closed : (body.substitute t (.mu t body)).isClosed = true :=
    GlobalType.isClosed_substitute_mu t body hclosed
  have hsubst_wf : (body.substitute t (.mu t body)).wellFormed = true :=
    wellFormed_mu_unfold t body hwf
  have hsubst_blind : isBlind (body.substitute t (.mu t body)) = true :=
    isBlind_substitute body t (.mu t body) (isBlind_mu_body hblind) hblind hclosed
  have hWFg' : g'.wellFormed = true := step_preserves_wellFormed _ _ _ hstep_sub hsubst_wf
  have h1 : EQ2 (projTrans g' role) (projTrans (body.substitute t (.mu t body)) role) :=
    ih_step hsubst_closed hsubst_wf hsubst_blind role hns hnr
  have h23 := proj_trans_other_step_mu_chain t body role hclosed hsubst_wf hwf
  have hWFa := trans_wellFormed_of_wellFormed g' role hWFg'
  have hWFb := trans_wellFormed_of_wellFormed (body.substitute t (.mu t body)) role hsubst_wf
  have hWFc := trans_wellFormed_of_wellFormed (.mu t body) role hwf
  exact EQ2_trans_wf h1 h23 hWFa hWFb hWFc

/-- Helper: BranchesStep.nil case. -/
theorem proj_trans_other_step_branches_nil (act : GlobalActionR) (role : String)
    (_hns : role ≠ act.sender) (_hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (projTransBranches [] role) (projTransBranches [] role) := by
  -- Empty branch lists are trivially related.
  simp [projTransBranches, RumpsteakV2.Protocol.Projection.Trans.transBranches, BranchesRel]

private abbrev StepIH (g g' : GlobalType) (act : GlobalActionR) : Prop :=
  -- Branch-step head hypothesis type.
  g.isClosed = true → g.wellFormed = true → isBlind g = true →
    ∀ role, role ≠ act.sender → role ≠ act.receiver →
      EQ2 (projTrans g' role) (projTrans g role)

private abbrev BranchIH (rest rest' : List (Label × GlobalType)) (act : GlobalActionR) : Prop :=
  -- Branch-step tail hypothesis type.
  (∀ p ∈ rest, p.2.isClosed = true) →
    (∀ p ∈ rest, p.2.wellFormed = true) →
    (∀ p ∈ rest, isBlind p.2 = true) →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        BranchesRel EQ2 (projTransBranches rest' role) (projTransBranches rest role)

/-- Helper: BranchesStep.cons case. -/
theorem proj_trans_other_step_branches_cons
    (label : Label) (g g' : GlobalType) (rest rest' : List (Label × GlobalType))
    (act : GlobalActionR) (ih_step : StepIH g g' act) (ih_bstep : BranchIH rest rest' act)
    (hclosed : ∀ p ∈ ((label, g) :: rest), p.2.isClosed = true)
    (hwf : ∀ p ∈ ((label, g) :: rest), p.2.wellFormed = true)
    (hblind : ∀ p ∈ ((label, g) :: rest), isBlind p.2 = true)
    (role : String) (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (projTransBranches ((label, g') :: rest') role)
      (projTransBranches ((label, g) :: rest) role) := by
  -- Build the cons proof from the head IH and tail IH.
  simp [projTransBranches, RumpsteakV2.Protocol.Projection.Trans.transBranches, BranchesRel]
  constructor
  · exact ih_step (hclosed (label, g) List.mem_cons_self)
      (hwf (label, g) List.mem_cons_self)
      (hblind (label, g) List.mem_cons_self) role hns hnr
  · exact ih_bstep (fun p hp => hclosed p (List.mem_cons_of_mem (label, g) hp))
      (fun p hp => hwf p (List.mem_cons_of_mem (label, g) hp))
      (fun p hp => hblind p (List.mem_cons_of_mem (label, g) hp)) role hns hnr

/-- Motive for non-participant step preservation. -/
abbrev StepMotive (g : GlobalType) (act : GlobalActionR) (g' : GlobalType) (_ : step g act g') : Prop :=
  g.isClosed = true → g.wellFormed = true →
  isBlind g = true →
  ∀ role, role ≠ act.sender → role ≠ act.receiver →
    EQ2 (projTrans g' role) (projTrans g role)

/-- Motive for branch-wise non-participant preservation. -/
abbrev BranchMotive (bs : List (Label × GlobalType)) (act : GlobalActionR)
    (bs' : List (Label × GlobalType)) (_ : BranchesStep step bs act bs') : Prop :=
  (∀ p ∈ bs, p.2.isClosed = true) →
  (∀ p ∈ bs, p.2.wellFormed = true) →
  (∀ p ∈ bs, isBlind p.2 = true) →
  ∀ role, role ≠ act.sender → role ≠ act.receiver →
    BranchesRel EQ2 (projTransBranches bs' role) (projTransBranches bs role)

end RumpsteakV2.Proofs.Projection.Harmony
