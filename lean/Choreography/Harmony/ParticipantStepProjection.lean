import Choreography.Harmony.Substitution

/-! # Choreography.Harmony.ParticipantStepProjection

Participant-side and non-participant projection-step harmony lemmas.
-/

/-
The Problem. Prove projection-step alignment for sender/receiver/non-participant roles.

Solution Structure. Build head-step lemmas, then discharge async/non-participant cases.
-/

namespace Choreography.Harmony
/-! ## Participant Projection Lemmas

These lemmas capture the “head communication” case for participants.
We use a lightweight predicate `action_pred` that asserts the action
matches the top-level communication of `g`. Under this predicate,
`comm_async` is impossible, so the projection transition is deterministic.
-/

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
open Choreography.Projection.Project
  (trans_comm_sender trans_comm_receiver trans_comm_other trans_wellFormed_of_wellFormed)
open Choreography.Projection.Project (ProjectableClosedWellFormed)
open Choreography.Projection.Projectb (CProject)

/-! ## Shared Projection Predicates -/

abbrev projTransBranches := Choreography.Projection.Project.transBranches

private def action_pred (g : GlobalType) (act : GlobalActionR) : Prop :=
  -- Action matches the head comm of g, otherwise false.
  match g with
  | .comm sender receiver _ =>
      GlobalActionR.sender act = sender ∧ GlobalActionR.receiver act = receiver
  | _ => False

private theorem mem_transBranches_of_mem (branches : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ branches) :
    (label, projTrans cont role) ∈ projTransBranches branches role := by
  induction branches with
  | nil => cases hmem
  | cons hd tl ih =>
      cases hd with
      | mk label_hd cont_hd =>
        cases hmem with
        | head =>
            simp [projTransBranches, Choreography.Projection.Project.transBranches]
        | tail _ htl =>
            have ih' := ih htl
            simp [projTransBranches, Choreography.Projection.Project.transBranches, List.mem_cons, ih']

/-! ## Sender Head Case -/

/-- Sender projection follows the head communication matching the action. -/
private theorem proj_trans_sender_step_comm_head
    (sender receiver : String) (branches : List (Label × GlobalType)) (label : Label)
    (g' : GlobalType) (hmem : (label, g') ∈ branches) :
    ∃ bs cont,
      projTrans (GlobalType.comm sender receiver branches) sender =
        LocalTypeR.send receiver bs ∧
      (label, cont) ∈ bs ∧
      EQ2 (projTrans g' sender) cont := by
  -- Head comm: sender projects to a send with matching branch.
  refine ⟨projTransBranches branches sender, projTrans g' sender, ?_, ?_, ?_⟩
  · simpa [projTrans] using (trans_comm_sender sender receiver sender branches rfl)
  · have hmem' : (label, projTrans g' sender) ∈ projTransBranches branches sender :=
      mem_transBranches_of_mem branches label g' sender hmem
    simpa using hmem'
  · simp [projTrans, EQ2_refl]

/-- Sender-side projection for head steps in the original harmony statement. -/


theorem proj_trans_sender_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hpred : action_pred g act) :
    ∃ bs cont,
      projTrans g (GlobalActionR.sender act) =
        .send (GlobalActionR.receiver act) bs ∧
      (GlobalActionR.label act, cont) ∈ bs ∧
      EQ2 (projTrans g' (GlobalActionR.sender act)) cont := by
  cases hstep with
  | comm_head sender receiver branches label =>
      rename_i hmem
      -- act is definitionally the head action in this constructor.
      simpa using (proj_trans_sender_step_comm_head sender receiver branches label g' hmem)
  | comm_async sender receiver branches branches' act label cont hns hcond hmem hcan hbs =>
      have hpred' :
          GlobalActionR.sender act = sender ∧ GlobalActionR.receiver act = receiver := by
        simpa [action_pred] using hpred
      have hcontra : False := by
        have hrcv : GlobalActionR.receiver act ≠ receiver := hcond hpred'.1
        exact hrcv hpred'.2
      exact hcontra.elim
  | mu _ _ _ _ _ =>
      -- action_pred is false on mu
      simp [action_pred] at hpred

/-! ## Receiver Head Case -/

/-- Receiver projection follows the head communication matching the action. -/
private theorem proj_trans_receiver_step_comm_head
    (sender receiver : String) (branches : List (Label × GlobalType)) (label : Label)
    (g' : GlobalType) (hno_self : (GlobalType.comm sender receiver branches).noSelfComm = true)
    (hmem : (label, g') ∈ branches) :
    ∃ bs cont,
      projTrans (GlobalType.comm sender receiver branches) receiver =
        LocalTypeR.recv sender bs ∧
      (label, cont) ∈ bs ∧
      EQ2 (projTrans g' receiver) cont := by
  -- Head comm: receiver projects to a recv with matching branch.
  have hne : receiver ≠ sender := by
    have hno := hno_self
    simp [GlobalType.noSelfComm] at hno
    intro hEq; exact hno.1 hEq.symm
  refine ⟨projTransBranches branches receiver, projTrans g' receiver, ?_, ?_, ?_⟩
  · simpa [projTrans] using (trans_comm_receiver sender receiver receiver branches rfl hne)
  · have hmem' : (label, projTrans g' receiver) ∈ projTransBranches branches receiver :=
      mem_transBranches_of_mem branches label g' receiver hmem
    simpa using hmem'
  · simp [projTrans, EQ2_refl]

/-- Receiver-side projection for head steps in the original harmony statement. -/


theorem proj_trans_receiver_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hpred : action_pred g act)
    (hno_self : g.noSelfComm = true) :
    ∃ bs cont,
      projTrans g (GlobalActionR.receiver act) =
        .recv (GlobalActionR.sender act) bs ∧
      (GlobalActionR.label act, cont) ∈ bs ∧
      EQ2 (projTrans g' (GlobalActionR.receiver act)) cont := by
  cases hstep with
  | comm_head sender receiver branches label =>
      rename_i hmem
      -- act is definitionally the head action in this constructor.
      simpa using (proj_trans_receiver_step_comm_head sender receiver branches label g' hno_self hmem)
  | comm_async sender receiver branches branches' act label cont hns hcond hmem hcan hbs =>
      have hpred' :
          GlobalActionR.sender act = sender ∧ GlobalActionR.receiver act = receiver := by
        simpa [action_pred] using hpred
      have hcontra : False := by
        have hrcv : GlobalActionR.receiver act ≠ receiver := hcond hpred'.1
        exact hrcv hpred'.2
      exact hcontra.elim
  | mu _ _ _ _ _ =>
      simp [action_pred] at hpred

/-! ## Non-Participant Step Helpers -/

/-- Helper: projectability yields a CProject witness. -/
private theorem cproject_of_projectable (g : GlobalType) (role : String)
    (hproj : ProjectableClosedWellFormed g) : ∃ lt, CProject g role lt := by
  -- Extract the projectability witness from the bundle.
  exact hproj.2.2 role

/-- Helper: comm_head case with nonempty branches. -/
private theorem proj_trans_other_step_comm_head_nonempty
    (sender receiver : String) (fl : Label) (fc : GlobalType) (rest : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ ((fl, fc) :: rest))
    (hclosed : (GlobalType.comm sender receiver ((fl, fc) :: rest)).isClosed = true)
    (hwf : (GlobalType.comm sender receiver ((fl, fc) :: rest)).wellFormed = true)
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hproj : ProjectableClosedWellFormed (GlobalType.comm sender receiver ((fl, fc) :: rest))) :
    EQ2 (projTrans cont role)
      (projTrans (GlobalType.comm sender receiver ((fl, fc) :: rest)) role) := by
  -- Rewrite the comm projection to the first continuation.
  have htrans_g :
      projTrans (GlobalType.comm sender receiver ((fl, fc) :: rest)) role = projTrans fc role :=
    trans_comm_other sender receiver role ((fl, fc) :: rest) hns hnr
  -- Get a CProject witness and branch-side invariants.
  have hproj_comm : ∃ lt, CProject (GlobalType.comm sender receiver ((fl, fc) :: rest)) role lt :=
    cproject_of_projectable _ role hproj
  have hclosed_branches : ∀ b ∈ ((fl, fc) :: rest), b.2.isClosed = true :=
    GlobalType.isClosed_comm_branches sender receiver ((fl, fc) :: rest) hclosed
  have hallwf_branches : ∀ b ∈ ((fl, fc) :: rest), b.2.wellFormed = true :=
    GlobalType.wellFormed_comm_branches sender receiver ((fl, fc) :: rest) hwf
  -- Apply branch coherence and rewrite with trans_comm_other.
  have hcoherent :=
    branches_project_coherent sender receiver fl fc rest label cont role hmem
      hns hnr hclosed_branches hallwf_branches hproj_comm
  simpa [htrans_g] using hcoherent

/-- Helper: comm_head case (handles empty branches by contradiction). -/


theorem proj_trans_other_step_comm_head
    (sender receiver : String) (branches : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ branches)
    (hclosed : (GlobalType.comm sender receiver branches).isClosed = true)
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true)
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hproj : ProjectableClosedWellFormed (GlobalType.comm sender receiver branches)) :
    EQ2 (projTrans cont role)
      (projTrans (GlobalType.comm sender receiver branches) role) := by
  -- Split on branch structure to reach the nonempty helper.
  cases branches with
  | nil => cases hmem
  | cons head rest =>
      cases head with
      | mk fl fc =>
          exact proj_trans_other_step_comm_head_nonempty sender receiver fl fc rest
            label cont role hmem hclosed hwf hns hnr hproj

/-- Helper: comm_async case when role is the sender. -/

/-! ## Non-Participant Async: Sender/Receiver Cases -/

private theorem proj_trans_other_step_comm_async_sender
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (role : String)
    (hbranch_rel : BranchesRel EQ2 (projTransBranches branches' role) (projTransBranches branches role))
    (hrs : role = sender) :
    EQ2 (projTrans (GlobalType.comm sender receiver branches') role)
        (projTrans (GlobalType.comm sender receiver branches) role) := by
  -- Rewrite both sides to sends and use EQ2.construct.
  have hsend' :
      projTrans (GlobalType.comm sender receiver branches') role =
        .send receiver (projTransBranches branches' role) := by
    simpa [projTrans] using (trans_comm_sender sender receiver role branches' hrs)
  have hsend :
      projTrans (GlobalType.comm sender receiver branches) role =
        .send receiver (projTransBranches branches role) := by
    simpa [projTrans] using (trans_comm_sender sender receiver role branches hrs)
  rw [hsend', hsend]
  exact EQ2.construct ⟨rfl, hbranch_rel⟩

/-- Helper: comm_async case when role is the receiver. -/
private theorem proj_trans_other_step_comm_async_receiver
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (role : String)
    (hbranch_rel : BranchesRel EQ2 (projTransBranches branches' role) (projTransBranches branches role))
    (hrr : role = receiver) (hrs : role ≠ sender) :
    EQ2 (projTrans (GlobalType.comm sender receiver branches') role)
        (projTrans (GlobalType.comm sender receiver branches) role) := by
  -- Rewrite both sides to recvs and use EQ2.construct.
  have hrecv' :
      projTrans (GlobalType.comm sender receiver branches') role =
        .recv sender (projTransBranches branches' role) := by
    simpa [projTrans] using (trans_comm_receiver sender receiver role branches' hrr hrs)
  have hrecv :
      projTrans (GlobalType.comm sender receiver branches) role =
        .recv sender (projTransBranches branches role) := by
    simpa [projTrans] using (trans_comm_receiver sender receiver role branches hrr hrs)
  rw [hrecv', hrecv]
  exact EQ2.construct ⟨rfl, hbranch_rel⟩

/-- Helper: comm_async case for non-participants (role ≠ sender/receiver). -/

/-! ## Non-Participant Async: Other Roles -/

private theorem proj_trans_other_step_comm_async_other_cons
    (sender receiver : String) (label label' : Label) (cont cont' : GlobalType)
    (rest rest' : List (Label × GlobalType)) (role : String)
    (hbranch_rel :
      BranchesRel EQ2 (projTransBranches ((label', cont') :: rest') role)
        (projTransBranches ((label, cont) :: rest) role))
    (hrs : role ≠ sender) (hrr : role ≠ receiver) :
    EQ2 (projTrans (GlobalType.comm sender receiver ((label', cont') :: rest')) role)
        (projTrans (GlobalType.comm sender receiver ((label, cont) :: rest)) role) := by
  -- Non-participants project to the head continuation in both branch lists.
  simp [projTrans, trans_comm_other, hrs, hrr]
  have hbranch_rel' :
      BranchesRel EQ2
        ((label', projTrans cont' role) :: projTransBranches rest' role)
        ((label, projTrans cont role) :: projTransBranches rest role) := by
    simpa [projTransBranches, Choreography.Projection.Project.transBranches] using hbranch_rel
  cases hbranch_rel' with
  | cons hpair _ => exact hpair.2

private theorem proj_trans_other_step_comm_async_other
    (sender receiver : String) (branches branches' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hbstep : BranchesStep step branches act branches')
    (hbranch_rel : BranchesRel EQ2 (projTransBranches branches' role) (projTransBranches branches role))
    (hrs : role ≠ sender) (hrr : role ≠ receiver) :
    EQ2 (projTrans (GlobalType.comm sender receiver branches') role)
        (projTrans (GlobalType.comm sender receiver branches) role) := by
  -- Reduce by cases on the BranchesStep derivation.
  cases hbstep with
  | nil =>
      simp [projTrans, trans_comm_other, hrs, hrr]
      exact EQ2_refl _
  | cons label cont cont' rest rest' _act _hstep _hbstep =>
      -- Reuse the cons/cons helper (labels are preserved by BranchesStep).
      have hbranch_rel' :
          BranchesRel EQ2 (projTransBranches ((label, cont') :: rest') role)
            (projTransBranches ((label, cont) :: rest) role) := by
        simpa using hbranch_rel
      exact proj_trans_other_step_comm_async_other_cons
        sender receiver label label cont cont' rest rest' role hbranch_rel' hrs hrr

/-! ## Async Dispatcher -/

/-- Helper: comm_async case (dispatches by role). -/


theorem proj_trans_other_step_comm_async
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (act : GlobalActionR)
    (hbstep : BranchesStep step branches act branches')
    (ih_bstep :
      (∀ p ∈ branches, p.2.isClosed = true) →
      (∀ p ∈ branches, p.2.wellFormed = true) →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        BranchesRel EQ2 (projTransBranches branches' role) (projTransBranches branches role))
    (hclosed : (GlobalType.comm sender receiver branches).isClosed = true)
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true)
    (role : String) (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    EQ2 (projTrans (GlobalType.comm sender receiver branches') role)
        (projTrans (GlobalType.comm sender receiver branches) role) := by
  -- Derive branch invariants and the BranchesRel IH.
  have hbranches_closed : ∀ p ∈ branches, p.2.isClosed = true :=
    GlobalType.isClosed_comm_branches sender receiver branches hclosed
  have hbranches_wf : ∀ p ∈ branches, p.2.wellFormed = true :=
    GlobalType.wellFormed_comm_branches sender receiver branches hwf
  have hbranch_rel := ih_bstep hbranches_closed hbranches_wf role hns hnr
  -- Split on participation in the outer comm.
  by_cases hrs : role = sender
  · exact proj_trans_other_step_comm_async_sender sender receiver branches branches' role hbranch_rel hrs
  · by_cases hrr : role = receiver
    · exact proj_trans_other_step_comm_async_receiver sender receiver branches branches' role hbranch_rel hrr hrs
    · exact proj_trans_other_step_comm_async_other sender receiver branches branches' act role
        hbstep hbranch_rel hrs hrr


end Choreography.Harmony
