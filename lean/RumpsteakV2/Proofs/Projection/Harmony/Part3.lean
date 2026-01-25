import RumpsteakV2.Proofs.Projection.Harmony.Part2

namespace RumpsteakV2.Proofs.Projection.Harmony
/-! ### Participant Projection Lemmas

These lemmas capture the “head communication” case for participants.
We use a lightweight predicate `action_pred` that asserts the action
matches the top-level communication of `g`. Under this predicate,
`comm_async` is impossible, so the projection transition is deterministic.
-/

private def action_pred (g : GlobalType) (act : GlobalActionR) : Prop :=
  -- Action matches the head comm of g, otherwise false.
  match g with
  | .comm sender receiver _ =>
      GlobalActionR.sender act = sender ∧ GlobalActionR.receiver act = receiver
  | _ => False

private theorem mem_transBranches_of_mem (branches : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ branches) :
    (label, projTrans cont role) ∈ transBranches branches role := by
  induction branches with
  | nil => cases hmem
  | cons hd tl ih =>
      cases hd with
      | mk label_hd cont_hd =>
        cases hmem with
        | head =>
            simp [transBranches]
        | tail _ htl =>
            have ih' := ih htl
            simp [transBranches, List.mem_cons, ih']

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
  refine ⟨transBranches branches sender, projTrans g' sender, ?_, ?_, ?_⟩
  · simpa [projTrans] using (trans_comm_sender sender receiver sender branches rfl)
  · have hmem' : (label, projTrans g' sender) ∈ transBranches branches sender :=
      mem_transBranches_of_mem branches label g' sender hmem
    simpa using hmem'
  · simp [projTrans, EQ2_refl]

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
  refine ⟨transBranches branches receiver, projTrans g' receiver, ?_, ?_, ?_⟩
  · simpa [projTrans] using (trans_comm_receiver sender receiver receiver branches rfl hne)
  · have hmem' : (label, projTrans g' receiver) ∈ transBranches branches receiver :=
      mem_transBranches_of_mem branches label g' receiver hmem
    simpa using hmem'
  · simp [projTrans, EQ2_refl]

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
    (hclosed : g.isClosed = true) (hwf : g.wellFormed = true)
    (hproj : ProjectableClosedWellFormed) : ∃ lt, CProject g role lt := by
  -- Use the projectability assumption specialized to g.
  have hproj_g : Projectable g := by
    simpa [ProjectableClosedWellFormed] using (hproj g hclosed hwf)
  exact hproj_g role

/-- Helper: comm_head case with nonempty branches. -/
private theorem proj_trans_other_step_comm_head_nonempty
    (sender receiver : String) (fl : Label) (fc : GlobalType) (rest : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ ((fl, fc) :: rest))
    (hclosed : (GlobalType.comm sender receiver ((fl, fc) :: rest)).isClosed = true)
    (hwf : (GlobalType.comm sender receiver ((fl, fc) :: rest)).wellFormed = true)
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hproj : ProjectableClosedWellFormed) :
    EQ2 (projTrans cont role)
      (projTrans (GlobalType.comm sender receiver ((fl, fc) :: rest)) role) := by
  -- Rewrite the comm projection to the first continuation.
  have htrans_g :
      projTrans (GlobalType.comm sender receiver ((fl, fc) :: rest)) role = projTrans fc role :=
    trans_comm_other sender receiver role ((fl, fc) :: rest) hns hnr
  -- Get a CProject witness and branch-side invariants.
  have hproj_comm : ∃ lt, CProject (GlobalType.comm sender receiver ((fl, fc) :: rest)) role lt :=
    cproject_of_projectable _ role hclosed hwf hproj
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
private theorem proj_trans_other_step_comm_head
    (sender receiver : String) (branches : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ branches)
    (hclosed : (GlobalType.comm sender receiver branches).isClosed = true)
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true)
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hproj : ProjectableClosedWellFormed) :
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
private theorem proj_trans_other_step_comm_async_sender
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (role : String)
    (hbranch_rel : BranchesRel EQ2 (transBranches branches' role) (transBranches branches role))
    (hrs : role = sender) :
    EQ2 (projTrans (GlobalType.comm sender receiver branches') role)
        (projTrans (GlobalType.comm sender receiver branches) role) := by
  -- Rewrite both sides to sends and use EQ2.construct.
  have hsend' :
      projTrans (GlobalType.comm sender receiver branches') role =
        .send receiver (transBranches branches' role) := by
    simpa [projTrans] using (trans_comm_sender sender receiver role branches' hrs)
  have hsend :
      projTrans (GlobalType.comm sender receiver branches) role =
        .send receiver (transBranches branches role) := by
    simpa [projTrans] using (trans_comm_sender sender receiver role branches hrs)
  rw [hsend', hsend]
  exact EQ2.construct ⟨rfl, hbranch_rel⟩

/-- Helper: comm_async case when role is the receiver. -/
private theorem proj_trans_other_step_comm_async_receiver
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (role : String)
    (hbranch_rel : BranchesRel EQ2 (transBranches branches' role) (transBranches branches role))
    (hrr : role = receiver) (hrs : role ≠ sender) :
    EQ2 (projTrans (GlobalType.comm sender receiver branches') role)
        (projTrans (GlobalType.comm sender receiver branches) role) := by
  -- Rewrite both sides to recvs and use EQ2.construct.
  have hrecv' :
      projTrans (GlobalType.comm sender receiver branches') role =
        .recv sender (transBranches branches' role) := by
    simpa [projTrans] using (trans_comm_receiver sender receiver role branches' hrr hrs)
  have hrecv :
      projTrans (GlobalType.comm sender receiver branches) role =
        .recv sender (transBranches branches role) := by
    simpa [projTrans] using (trans_comm_receiver sender receiver role branches hrr hrs)
  rw [hrecv', hrecv]
  exact EQ2.construct ⟨rfl, hbranch_rel⟩

/-- Helper: comm_async case for non-participants (role ≠ sender/receiver). -/
private theorem proj_trans_other_step_comm_async_other_cons
    (sender receiver : String) (label label' : Label) (cont cont' : GlobalType)
    (rest rest' : List (Label × GlobalType)) (role : String)
    (hbranch_rel :
      BranchesRel EQ2 (transBranches ((label', cont') :: rest') role)
        (transBranches ((label, cont) :: rest) role))
    (hrs : role ≠ sender) (hrr : role ≠ receiver) :
    EQ2 (projTrans (GlobalType.comm sender receiver ((label', cont') :: rest')) role)
        (projTrans (GlobalType.comm sender receiver ((label, cont) :: rest)) role) := by
  -- Non-participants project to the head continuation in both branch lists.
  simp [projTrans, trans_comm_other, hrs, hrr]
  have hbranch_rel' :
      BranchesRel EQ2
        ((label', projTrans cont' role) :: transBranches rest' role)
        ((label, projTrans cont role) :: transBranches rest role) := by
    simpa [transBranches] using hbranch_rel
  cases hbranch_rel' with
  | cons hpair _ => exact hpair.2

private theorem proj_trans_other_step_comm_async_other
    (sender receiver : String) (branches branches' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hbstep : BranchesStep step branches act branches')
    (hbranch_rel : BranchesRel EQ2 (transBranches branches' role) (transBranches branches role))
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
          BranchesRel EQ2 (transBranches ((label, cont') :: rest') role)
            (transBranches ((label, cont) :: rest) role) := by
        simpa using hbranch_rel
      exact proj_trans_other_step_comm_async_other_cons
        sender receiver label label cont cont' rest rest' role hbranch_rel' hrs hrr

/-- Helper: comm_async case (dispatches by role). -/
private theorem proj_trans_other_step_comm_async
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (act : GlobalActionR)
    (hbstep : BranchesStep step branches act branches')
    (ih_bstep :
      (∀ p ∈ branches, p.2.isClosed = true) →
      (∀ p ∈ branches, p.2.wellFormed = true) →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        BranchesRel EQ2 (transBranches branches' role) (transBranches branches role))
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

/-! ### Well-formedness Preservation for Steps (Local Helper) -/

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

/-! ### comm_wellFormed helpers -/

private lemma branch_wf_parts {b : Label × GlobalType} (h : b.2.wellFormed = true) :
    b.2.allVarsBound = true ∧ b.2.allCommsNonEmpty = true ∧
      b.2.noSelfComm = true ∧ b.2.isProductive = true := by
  -- Split the wellFormed conjuncts for branch-level reuse.
  simpa [GlobalType.wellFormed, Bool.and_eq_true] using h

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
    cases hbranches : branches <;> simp [hbranches] at hne <;> simp [hbranches]
  simp [GlobalType.wellFormed, GlobalType.allVarsBound, GlobalType.allCommsNonEmpty,
    GlobalType.noSelfComm, GlobalType.isProductive, hvars, hallcomms, hnoself, hprod, hne', hneq]

private lemma comm_sender_ne_receiver_of_wf {sender receiver : String} {branches : List (Label × GlobalType)}
    (hwf_comm : (GlobalType.comm sender receiver branches).wellFormed = true) : sender ≠ receiver := by
  -- noSelfComm rules out sender = receiver.
  have hnoself : (GlobalType.comm sender receiver branches).noSelfComm = true := by
    have hwf' := hwf_comm; simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf'; exact hwf'.1.2
  by_cases h : sender = receiver
  · subst h; have : False := by simp [GlobalType.noSelfComm] at hnoself; exact this.elim
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
    (_label : Label) (_cont : GlobalType) (_hns_cond : _) (_hcond : _) (_hmem : _) (_hcan : _)
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

private theorem branches_wf_nil (act : GlobalActionR)
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

private theorem step_preserves_wellFormed (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hwf : g.wellFormed = true) : g'.wellFormed = true := by
  -- Recursor with constructor-specific helpers.
  refine @step.rec (motive_1 := StepWFMotive) (motive_2 := BranchWFMotive)
    step_preserves_wf_comm_head step_preserves_wf_comm_async step_preserves_wf_mu
    branches_wf_nil branches_wf_cons g act g' hstep hwf

private theorem proj_trans_other_step_mu_chain
    (t : String) (body : GlobalType) (role : String)
    (hclosed : (GlobalType.mu t body).isClosed = true)
    (hsubst_wf : (body.substitute t (.mu t body)).wellFormed = true)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    EQ2 (projTrans (body.substitute t (.mu t body)) role) (projTrans (.mu t body) role) := by
  -- Unfold-substitute chain with well-formedness witnesses.
  have h2 := trans_substitute_unfold t body role hclosed
  have h3 := EQ2_symm (EQ2_unfold_right (EQ2_refl _))
  have hWFb := trans_wellFormed_of_wellFormed _ _ hsubst_wf
  have hWFc := trans_wellFormed_of_wellFormed _ _ hwf
  have hWFunfold := LocalTypeR.WellFormed.unfold hWFc
  exact EQ2_trans_wf h2 h3 hWFb hWFunfold hWFc

/-- Helper: mu case for non-participants. -/
private theorem proj_trans_other_step_mu
    (t : String) (body : GlobalType) (act : GlobalActionR) (g' : GlobalType)
    (hstep_sub : step (body.substitute t (.mu t body)) act g')
    (ih_step :
      (body.substitute t (.mu t body)).isClosed = true →
      (body.substitute t (.mu t body)).wellFormed = true →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        EQ2 (projTrans g' role) (projTrans (body.substitute t (.mu t body)) role))
    (hclosed : (GlobalType.mu t body).isClosed = true)
    (hwf : (GlobalType.mu t body).wellFormed = true)
    (role : String) (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    EQ2 (projTrans g' role) (projTrans (GlobalType.mu t body) role) := by
  -- Chain IH with trans_substitute_unfold and the unfold lemma.
  have hsubst_closed : (body.substitute t (.mu t body)).isClosed = true :=
    GlobalType.isClosed_substitute_mu t body hclosed
  have hsubst_wf : (body.substitute t (.mu t body)).wellFormed = true :=
    wellFormed_mu_unfold t body hwf
  have hWFg' : g'.wellFormed = true := step_preserves_wellFormed _ _ _ hstep_sub hsubst_wf
  have h1 : EQ2 (projTrans g' role) (projTrans (body.substitute t (.mu t body)) role) :=
    ih_step hsubst_closed hsubst_wf role hns hnr
  have h23 := proj_trans_other_step_mu_chain t body role hclosed hsubst_wf hwf
  have hWFa := trans_wellFormed_of_wellFormed g' role hWFg'
  have hWFb := trans_wellFormed_of_wellFormed _ _ hsubst_wf
  have hWFc := trans_wellFormed_of_wellFormed _ _ hwf
  exact EQ2_trans_wf h1 h23 hWFa hWFb hWFc

/-- Helper: BranchesStep.nil case. -/
private theorem proj_trans_other_step_branches_nil (act : GlobalActionR) (role : String)
    (_hns : role ≠ act.sender) (_hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (transBranches [] role) (transBranches [] role) := by
  -- Empty branch lists are trivially related.
  simp [transBranches, BranchesRel]

private abbrev StepIH (g g' : GlobalType) (act : GlobalActionR) : Prop :=
  -- Branch-step head hypothesis type.
  g.isClosed = true → g.wellFormed = true →
    ∀ role, role ≠ act.sender → role ≠ act.receiver →
      EQ2 (projTrans g' role) (projTrans g role)

private abbrev BranchIH (rest rest' : List (Label × GlobalType)) (act : GlobalActionR) : Prop :=
  -- Branch-step tail hypothesis type.
  (∀ p ∈ rest, p.2.isClosed = true) →
    (∀ p ∈ rest, p.2.wellFormed = true) →
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        BranchesRel EQ2 (transBranches rest' role) (transBranches rest role)

/-- Helper: BranchesStep.cons case. -/
private theorem proj_trans_other_step_branches_cons
    (label : Label) (g g' : GlobalType) (rest rest' : List (Label × GlobalType))
    (act : GlobalActionR) (ih_step : StepIH g g' act) (ih_bstep : BranchIH rest rest' act)
    (hclosed : ∀ p ∈ ((label, g) :: rest), p.2.isClosed = true)
    (hwf : ∀ p ∈ ((label, g) :: rest), p.2.wellFormed = true)
    (role : String) (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (transBranches ((label, g') :: rest') role)
      (transBranches ((label, g) :: rest) role) := by
  -- Build the cons proof from the head IH and tail IH.
  simp [transBranches]
  refine List.Forall₂.cons ?head ?tail
  · constructor
    · rfl
    · exact ih_step (hclosed (label, g) List.mem_cons_self)
        (hwf (label, g) List.mem_cons_self) role hns hnr
  · exact ih_bstep (fun p hp => hclosed p (List.mem_cons_of_mem (label, g) hp))
      (fun p hp => hwf p (List.mem_cons_of_mem (label, g) hp)) role hns hnr

/-- Motive for non-participant step preservation. -/
private abbrev StepMotive (g : GlobalType) (act : GlobalActionR) (g' : GlobalType) (_ : step g act g') : Prop :=
  g.isClosed = true → g.wellFormed = true →
  ∀ role, role ≠ act.sender → role ≠ act.receiver →
    EQ2 (projTrans g' role) (projTrans g role)

/-- Motive for branch-wise non-participant preservation. -/
private abbrev BranchMotive (bs : List (Label × GlobalType)) (act : GlobalActionR)
    (bs' : List (Label × GlobalType)) (_ : BranchesStep step bs act bs') : Prop :=
  (∀ p ∈ bs, p.2.isClosed = true) →
  (∀ p ∈ bs, p.2.wellFormed = true) →
  ∀ role, role ≠ act.sender → role ≠ act.receiver →
    BranchesRel EQ2 (transBranches bs' role) (transBranches bs role)

end RumpsteakV2.Proofs.Projection.Harmony
