import RumpsteakV2.Protocol.Projection.Project.MuveImplBase

namespace RumpsteakV2.Protocol.Projection.Project

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.Participation
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Props

/-! ## EQ_end: Non-participants project to EEnd

This section establishes that if a role doesn't participate in a global protocol,
then the projection function `trans` produces a local type EQ2-equivalent to EEnd.

This corresponds to Coq's `EQ_end` theorem from indProj.v (lines 147-152). -/

/-- Non-participants project to EEnd (EQ2-equivalent).

If a role doesn't participate in the global type and the global type is well-formed
(closed, all comms have branches), then trans g role is EQ2-equivalent to .end.

### Proof Strategy

1. Show that `trans` on a non-participant produces a "muve" type (mu-var-end chain):
   - `trans_muve_of_not_part_of2`: if ¬part_of2 role g, then isMuve (trans g role)

2. Show that for closed global types, trans produces closed muve local types:
   - wellFormed includes allVarsBound, so trans produces closed types

3. Apply coinduction: ClosedMuveRel is a post-fixpoint of EQ2F

4. Since trans g role is closed muve, ClosedMuveRel .end (trans g role) holds

5. By EQ2_coind, EQ2 .end (trans g role)

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:147-152`. -/
private theorem EQ_end_closed (g : GlobalType) (role : String)
    (hwf : g.wellFormed = true) : isClosed (trans g role) = true := by
  -- Use allVarsBound + freeVars containment for trans.
  rw [isClosed_eq_true_iff]
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  rcases hwf with ⟨⟨⟨hbound, _hne⟩, _hnsc⟩, _hprod⟩
  have hsub := trans_freeVars_subset g role
  have gclosed : g.freeVars = [] := allVarsBound_nil_implies_freeVars_nil g hbound
  simp only [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have hgx := hsub hx
  simp [gclosed] at hgx

private theorem EQ_end_coind (g : GlobalType) (role : String)
    (hmuve : isMuve (trans g role) = true)
    (hclosed : isClosed (trans g role) = true) :
    EQ2 .end (trans g role) := by
  -- Close by the ClosedMuveRel coinduction principle.
  have hinR : ClosedMuveRel .end (trans g role) := ⟨rfl, hmuve, hclosed⟩
  exact EQ2_coind ClosedMuveRel_postfix .end (trans g role) hinR

theorem EQ_end (role : String) (g : GlobalType)
    (hnotpart : ¬ part_of2 role g)
    (hwf : g.wellFormed = true) :
    EQ2 .end (trans g role) := by
  -- Reduce to closed muve coinduction.
  have hmuve : isMuve (trans g role) = true := trans_muve_of_not_part_of2 g role hnotpart hwf
  have hclosed : isClosed (trans g role) = true := EQ_end_closed g role hwf
  exact EQ_end_coind g role hmuve hclosed

/-! ## CProject and Muve Types

When a role doesn't participate in a global type, the CProject relation constrains
the local type candidate to be a "muve" type (mu-var-end chain). This is because:
- For non-participant comm nodes, CProjectF requires AllBranchesProj to the same candidate
- For mu nodes, CProjectF requires the body projection
- The only leaf types in CProject are .end (for .end) and .var t (for .var t)

Combined with wellFormedness (which implies closedness), this means non-participant
projections are closed muve types, which are EQ2-equivalent to .end. -/

/-- Helper: comm allCommsNonEmpty implies branch allCommsNonEmpty. -/
private theorem allCommsNonEmptyBranches_of_comm {sender receiver : String}
    {branches : List (Label × GlobalType)}
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true) :
    allCommsNonEmptyBranches branches = true := by
  -- Unpack the comm boolean to reach the branches clause.
  have hne' : branches ≠ [] ∧ allCommsNonEmptyBranches branches = true := by
    have hne' := hne
    simp [GlobalType.allCommsNonEmpty, Bool.and_eq_true] at hne'
    exact hne'
  exact hne'.2

/-- Auxiliary: Non-participant projections are muve types.
    Uses structural properties only (allCommsNonEmpty, noSelfComm) to avoid the semantic gap
    where body.allVarsBound [t] does not imply body.allVarsBound []. -/
private theorem CProject_muve_of_not_part_of2_aux_end (role : String) (lt : LocalTypeR)
    (hproj : CProject .end role lt) : isMuve lt = true := by
  -- Reduce CProjectF for `.end` and discharge non-end constructors by contradiction.
  have hF := CProject_destruct hproj
  cases lt with
  | «end» =>
      -- The only valid candidate is `.end`.
      rfl
  | var _ =>
      -- `.var` cannot satisfy the `.end` CProjectF clause.
      simp [CProjectF] at hF
  | mu _ _ =>
      -- `.mu` cannot satisfy the `.end` CProjectF clause.
      simp [CProjectF] at hF
  | send _ _ =>
      -- `.send` cannot satisfy the `.end` CProjectF clause.
      simp [CProjectF] at hF
  | recv _ _ =>
      -- `.recv` cannot satisfy the `.end` CProjectF clause.
      simp [CProjectF] at hF

private theorem CProject_muve_of_not_part_of2_aux_var (t role : String) (lt : LocalTypeR)
    (hproj : CProject (.var t) role lt) : isMuve lt = true := by
  -- Reduce CProjectF for `.var` and discharge non-var constructors.
  have hF := CProject_destruct hproj
  cases lt with
  | var _ =>
      -- Any `.var` candidate is muve.
      rfl
  | «end» =>
      -- `.end` cannot satisfy the `.var` CProjectF clause.
      simp [CProjectF] at hF
  | mu _ _ =>
      -- `.mu` cannot satisfy the `.var` CProjectF clause.
      simp [CProjectF] at hF
  | send _ _ =>
      -- `.send` cannot satisfy the `.var` CProjectF clause.
      simp [CProjectF] at hF
  | recv _ _ =>
      -- `.recv` cannot satisfy the `.var` CProjectF clause.
      simp [CProjectF] at hF

private theorem CProject_muve_of_not_part_of2_aux_comm_nil (sender receiver _role : String)
    (lt : LocalTypeR) (hne : (GlobalType.comm sender receiver []).allCommsNonEmpty = true) :
    isMuve lt = true := by
  -- Empty branches contradict allCommsNonEmpty, so this case is unreachable.
  have : False := by
    simp [GlobalType.allCommsNonEmpty, List.isEmpty_nil] at hne
  exact False.elim this

/-- Helper: mu case for CProject_muve_of_not_part_of2_aux. -/
private theorem CProject_muve_of_not_part_of2_aux_mu (t : String) (lt candBody : LocalTypeR)
    (hcase :
      (LocalTypeR.isGuarded t candBody = true ∧ lt = LocalTypeR.mu t candBody) ∨
      (LocalTypeR.isGuarded t candBody = false ∧ lt = LocalTypeR.end))
    (ih_body : isMuve candBody = true) : isMuve lt = true := by
  -- Reduce the mu case to the body witness.
  cases lt with
  | mu t' candBody' =>
      rcases hcase with ⟨_hguard, hEq⟩ | ⟨_hguard, hEq⟩
      · cases hEq
        simpa [isMuve] using ih_body
      · cases hEq
  | «end» =>
      simp [isMuve]
  | var _ =>
      simp [isMuve]
  | send _ _ =>
      rcases hcase with ⟨_hguard, hEq⟩ | ⟨_hguard, hEq⟩ <;> cases hEq
  | recv _ _ =>
      rcases hcase with ⟨_hguard, hEq⟩ | ⟨_hguard, hEq⟩ <;> cases hEq

/-- Helper: comm/cons case data for CProject_muve_of_not_part_of2_aux. -/
private theorem CProject_muve_of_not_part_of2_aux_comm_cons_data (sender receiver : String)
    (first : Label × GlobalType) (rest : List (Label × GlobalType)) (role : String) (lt : LocalTypeR)
    (hproj : CProject (GlobalType.comm sender receiver (first :: rest)) role lt)
    (hnotpart : ¬ part_of2 role (GlobalType.comm sender receiver (first :: rest)))
    (hne : (GlobalType.comm sender receiver (first :: rest)).allCommsNonEmpty = true) :
    CProject first.2 role lt ∧ ¬ part_of2 role first.2 ∧ first.2.allCommsNonEmpty = true := by
  -- Non-participant comm reduces to the first branch.
  have hF := CProject_destruct hproj
  have hns : role ≠ sender := by
    intro heq; subst heq
    have hpart : part_of2 role (GlobalType.comm role receiver (first :: rest)) :=
      part_of2.intro _ (part_ofF.comm_direct _ _ _ (by simp [is_participant]))
    exact hnotpart hpart
  have hnr : role ≠ receiver := by
    intro heq; subst heq
    have hpart : part_of2 role (GlobalType.comm sender role (first :: rest)) :=
      part_of2.intro _ (part_ofF.comm_direct _ _ _ (by simp [is_participant]))
    exact hnotpart hpart
  simp [CProjectF, hns, hnr] at hF
  have hfirst_proj : CProject first.2 role lt := hF first (by simp)
  have hnotpart_first : ¬ part_of2 role first.2 := by
    intro hpart; exact hnotpart (part_of2.intro _ (part_ofF.comm_branch _ _ first.1 first.2 _ (by simp) hpart))
  have hbranches := allCommsNonEmptyBranches_of_comm (sender := sender) (receiver := receiver) hne
  have hbranches' : first.2.allCommsNonEmpty = true ∧ allCommsNonEmptyBranches rest = true := by
    simpa [GlobalType.allCommsNonEmptyBranches, Bool.and_eq_true] using hbranches
  exact ⟨hfirst_proj, hnotpart_first, hbranches'.1⟩
theorem CProject_muve_of_not_part_of2_aux : (g : GlobalType) → (role : String) → (lt : LocalTypeR) →
    CProject g role lt → ¬ part_of2 role g → g.allCommsNonEmpty = true → isMuve lt = true
  | GlobalType.end, role, lt, hproj, _, _ =>
      CProject_muve_of_not_part_of2_aux_end role lt hproj
  | GlobalType.var t, role, lt, hproj, _, _ =>
      CProject_muve_of_not_part_of2_aux_var t role lt hproj
  | GlobalType.mu t body, role, lt, hproj, hnotpart, hne => by
      -- Mu case: recurse on the body and finish via the helper.
      have hF := CProject_destruct hproj
      rcases hF with ⟨candBody, hbody_proj, hcase⟩
      have hnotpart_body : ¬ part_of2 role body := not_part_of2_mu hnotpart
      have hne_body : body.allCommsNonEmpty = true := by simpa [GlobalType.allCommsNonEmpty] using hne
      have ih_body := CProject_muve_of_not_part_of2_aux body role candBody hbody_proj hnotpart_body hne_body
      exact CProject_muve_of_not_part_of2_aux_mu t lt candBody hcase ih_body
  | GlobalType.comm sender receiver [], role, lt, _hproj, _, hne =>
      CProject_muve_of_not_part_of2_aux_comm_nil sender receiver role lt hne
  | GlobalType.comm sender receiver (first :: rest), role, lt, hproj, hnotpart, hne => by
      rcases CProject_muve_of_not_part_of2_aux_comm_cons_data sender receiver first rest role lt hproj hnotpart hne with
        ⟨hfirst_proj, hnotpart_first, hne_first⟩
      exact CProject_muve_of_not_part_of2_aux first.2 role lt hfirst_proj hnotpart_first hne_first
termination_by g _ _ _ _ _ => sizeOf g
decreasing_by
  all_goals simp_wf; simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1]; omega

/-- Non-participant projections are muve types.

If a role doesn't participate in a global type, any CProject candidate
for that role must be a muve type (only mu/var/end constructors).

Proof by well-founded induction on global type size. -/
theorem CProject_muve_of_not_part_of2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (hwf : g.wellFormed = true) :
    isMuve lt = true := by
  have hne : g.allCommsNonEmpty = true := by
    -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    rcases hwf with ⟨⟨⟨_havb, hne⟩, _hnsc⟩, _hprod⟩
    exact hne
  exact CProject_muve_of_not_part_of2_aux g role lt hproj hnotpart hne

/-- Auxiliary: Non-participant projections have free vars contained in bound vars.
    This is the generalized version that tracks bound variables through mu bindings.

    Key insight: allVarsBound bvars means freeVars ⊆ bvars. For mu, the bound var is
    added to bvars, allowing the recursive call to track that var properly. -/
private theorem CProject_freeVars_subset_bvars_end (role : String) (lt : LocalTypeR)
    (hproj : CProject .end role lt) : ∀ v, v ∈ lt.freeVars → v ∈ [] := by
  -- CProjectF forces lt = .end, whose freeVars are empty.
  have hF := CProject_destruct hproj
  cases lt with
  | «end» =>
      -- .end has no free variables.
      intro v hv
      simp [LocalTypeR.freeVars] at hv
  | var _ =>
      -- `.var` cannot satisfy the `.end` projection clause.
      simp [CProjectF] at hF
  | mu _ _ =>
      -- `.mu` cannot satisfy the `.end` projection clause.
      simp [CProjectF] at hF
  | send _ _ =>
      -- `.send` cannot satisfy the `.end` projection clause.
      simp [CProjectF] at hF
  | recv _ _ =>
      -- `.recv` cannot satisfy the `.end` projection clause.
      simp [CProjectF] at hF

private theorem CProject_freeVars_subset_bvars_var (t role : String) (lt : LocalTypeR)
    (bvars : List String) (hproj : CProject (GlobalType.var t) role lt)
    (havb : (GlobalType.var t).allVarsBound bvars = true) :
    ∀ v, v ∈ lt.freeVars → v ∈ bvars := by
  -- Reduce the candidate to a variable and pull membership from allVarsBound.
  have hF := CProject_destruct hproj
  cases lt with
  | var s =>
      intro v hv
      have ht' : t ∈ bvars := by
        simpa [GlobalType.allVarsBound, List.contains_iff_mem] using havb
      have hs : t = s := by
        simpa [CProjectF] using hF
      simp [LocalTypeR.freeVars] at hv
      subst hv
      simpa [hs] using ht'
  | «end» =>
      simp [CProjectF] at hF
  | mu _ _ =>
      simp [CProjectF] at hF
  | send _ _ =>
      simp [CProjectF] at hF
  | recv _ _ =>
      simp [CProjectF] at hF

private theorem CProject_freeVars_subset_bvars_mu_mu (t : String) (candBody : LocalTypeR)
    (bvars : List String)
    (ih_body : ∀ v, v ∈ candBody.freeVars → v ∈ t :: bvars) :
    ∀ v, v ∈ (LocalTypeR.mu t candBody).freeVars → v ∈ bvars := by
  -- Drop the binder and exclude its variable from the freeVars list.
  intro v hv
  simp [LocalTypeR.freeVars, List.mem_filter, bne_iff_ne] at hv
  obtain ⟨hv_in, hv_ne⟩ := hv
  have hv_in' := ih_body v hv_in
  simp [List.mem_cons] at hv_in'
  cases hv_in' with
  | inl heq => exact (hv_ne heq).elim
  | inr hin => exact hin

private theorem CProject_freeVars_subset_bvars_mu_case (t : String) (lt candBody : LocalTypeR)
    (bvars : List String)
    (hcase :
      (LocalTypeR.isGuarded t candBody = true ∧ lt = LocalTypeR.mu t candBody) ∨
      (LocalTypeR.isGuarded t candBody = false ∧ lt = LocalTypeR.end))
    (ih_body : ∀ v, v ∈ candBody.freeVars → v ∈ t :: bvars) :
    ∀ v, v ∈ lt.freeVars → v ∈ bvars := by
  -- Reduce the mu case to the body witness.
  cases lt with
  | mu t' candBody' =>
      rcases hcase with ⟨_hguard, hEq⟩ | ⟨_hguard, hEq⟩
      · cases hEq
        exact CProject_freeVars_subset_bvars_mu_mu t candBody bvars ih_body
      · cases hEq
  | «end» =>
      intro v hv
      simp [LocalTypeR.freeVars] at hv
  | var _ =>
      rcases hcase with ⟨_hguard, hEq⟩ | ⟨_hguard, hEq⟩ <;> cases hEq
  | send _ _ =>
      rcases hcase with ⟨_hguard, hEq⟩ | ⟨_hguard, hEq⟩ <;> cases hEq
  | recv _ _ =>
      rcases hcase with ⟨_hguard, hEq⟩ | ⟨_hguard, hEq⟩ <;> cases hEq

private theorem CProject_freeVars_subset_bvars_comm_nil (sender receiver _role : String)
    (lt : LocalTypeR) (bvars : List String)
    (hne : (GlobalType.comm sender receiver []).allCommsNonEmpty = true) :
    ∀ v, v ∈ lt.freeVars → v ∈ bvars := by
  -- Empty branches contradict allCommsNonEmpty.
  have : False := by
    simp [GlobalType.allCommsNonEmpty, List.isEmpty_nil] at hne
  exact this.elim

private theorem CProject_freeVars_subset_bvars_comm_cons_data (sender receiver : String)
    (first : Label × GlobalType) (rest : List (Label × GlobalType)) (role : String)
    (lt : LocalTypeR) (bvars : List String)
    (hproj : CProject (GlobalType.comm sender receiver (first :: rest)) role lt)
    (hnotpart : ¬ part_of2 role (GlobalType.comm sender receiver (first :: rest)))
    (havb : (GlobalType.comm sender receiver (first :: rest)).allVarsBound bvars = true)
    (hne : (GlobalType.comm sender receiver (first :: rest)).allCommsNonEmpty = true) :
    CProject first.2 role lt ∧ ¬ part_of2 role first.2 ∧
      first.2.allVarsBound bvars = true ∧ first.2.allCommsNonEmpty = true := by
  have hF := CProject_destruct hproj -- comm case reduces to the first branch
  have hns : role ≠ sender := by
    intro heq; subst heq; exact hnotpart (part_of2.intro _ (part_ofF.comm_direct _ _ _ (by simp [is_participant])))
  have hnr : role ≠ receiver := by
    intro heq; subst heq; exact hnotpart (part_of2.intro _ (part_ofF.comm_direct _ _ _ (by simp [is_participant])))
  simp [CProjectF, hns, hnr] at hF
  have hfirst_proj : CProject first.2 role lt := hF first (by simp)
  have hnotpart_first : ¬ part_of2 role first.2 := by
    intro hpart; exact hnotpart (part_of2.intro _ (part_ofF.comm_branch _ _ first.1 first.2 _ (by simp) hpart))
  have havb_first : first.2.allVarsBound bvars = true := by
    have h : first.2.allVarsBound bvars = true ∧ allVarsBoundBranches rest bvars = true := by
      simpa [GlobalType.allVarsBound, allVarsBoundBranches, Bool.and_eq_true] using havb
    exact h.1
  have hbranches' : first.2.allCommsNonEmpty = true ∧ allCommsNonEmptyBranches rest = true := by
    simpa [GlobalType.allCommsNonEmptyBranches, Bool.and_eq_true] using
      (allCommsNonEmptyBranches_of_comm (sender := sender) (receiver := receiver) hne)
  exact ⟨hfirst_proj, hnotpart_first, havb_first, hbranches'.1⟩
private theorem CProject_freeVars_subset_bvars :
    (g : GlobalType) → (role : String) → (lt : LocalTypeR) → (bvars : List String) →
    CProject g role lt → ¬ part_of2 role g → g.allVarsBound bvars = true →
    g.allCommsNonEmpty = true → ∀ v, v ∈ lt.freeVars → v ∈ bvars
  | GlobalType.end, role, lt, bvars, hproj, _, _, _ => by
      have hF := CProject_destruct hproj
      cases lt <;> try (cases hF) <;> intro v hv <;> cases hv
  | GlobalType.var t, role, lt, bvars, hproj, _, havb, _ =>
      CProject_freeVars_subset_bvars_var t role lt bvars hproj havb
  | GlobalType.mu t body, role, lt, bvars, hproj, hnotpart, havb, hne => by
      rcases CProject_destruct hproj with ⟨candBody, hbody_proj, hcase⟩ -- mu case
      have hnotpart_body : ¬ part_of2 role body := not_part_of2_mu hnotpart
      have havb_body : body.allVarsBound (t :: bvars) = true := by simpa [GlobalType.allVarsBound] using havb
      have hne_body : body.allCommsNonEmpty = true := by simpa [GlobalType.allCommsNonEmpty] using hne
      have ih_body := CProject_freeVars_subset_bvars body role candBody (t :: bvars) hbody_proj hnotpart_body havb_body hne_body
      exact CProject_freeVars_subset_bvars_mu_case t lt candBody bvars hcase ih_body
  | GlobalType.comm _ _ [], role, lt, bvars, _hproj, _hnotpart, _havb, hne =>
      CProject_freeVars_subset_bvars_comm_nil _ _ role lt bvars hne
  | GlobalType.comm sender receiver (first :: rest), role, lt, bvars, hproj, hnotpart, havb, hne => by
      rcases CProject_freeVars_subset_bvars_comm_cons_data sender receiver first rest role lt bvars hproj hnotpart havb hne with
        ⟨hfirst_proj, hnotpart_first, havb_first, hne_first⟩
      exact CProject_freeVars_subset_bvars first.2 role lt bvars hfirst_proj hnotpart_first havb_first hne_first
termination_by g _ _ _ _ _ _ _ => sizeOf g
decreasing_by
  all_goals simp_wf; simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1]; omega
/-- Auxiliary: Non-participant projections are closed types.
    Uses allVarsBound to show freeVars = [] for the candidate.

    Key insight: CProject_freeVars_subset_bvars with bvars = [] gives freeVars ⊆ [],
    which means freeVars = []. -/
private theorem CProject_closed_of_not_part_of2_aux (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (havb : g.allVarsBound = true)
    (hne : g.allCommsNonEmpty = true) :
    isClosed lt = true := by
  -- Reduce closedness to freeVars ⊆ [].
  simp only [isClosed, beq_iff_eq]
  have hsub := CProject_freeVars_subset_bvars g role lt [] hproj hnotpart havb hne
  exact List.subset_nil.mp (fun v hv => hsub v hv)

/-- Non-participant projections are closed types.

If a role doesn't participate in a well-formed (closed) global type,
any CProject candidate for that role must be closed (no free variables).

Proof by well-founded induction on global type size. -/
theorem CProject_closed_of_not_part_of2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (hwf : g.wellFormed = true) :
    isClosed lt = true := by
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  rcases hwf with ⟨⟨⟨havb, hne⟩, _hnsc⟩, _hprod⟩
  exact CProject_closed_of_not_part_of2_aux g role lt hproj hnotpart havb hne


end RumpsteakV2.Protocol.Projection.Project
