import RumpsteakV2.Protocol.Projection.Trans.Participation


namespace RumpsteakV2.Protocol.Projection.Trans
/-! ## Fully Proven Contractiveness with All-Branch Participation

The `participatesAllBranches` predicate is stronger than `participatesFirstBranch`:
- For direct participants, it requires participation in ALL branch continuations
- This ensures that `transBranches` produces contractive results
- The theorem `trans_isContractive_of_participatesAllBranches` is fully provable
-/

theorem participatesAllBranches_imp_participatesFirstBranch (g : GlobalType) (role : String) :
    participatesAllBranches role g = true → participatesFirstBranch role g = true := by
  intro h
  match g with
  | .end => simpa [participatesAllBranches] using h
  | .var _ => simpa [participatesAllBranches] using h
  | .mu _ body =>
      simpa [participatesAllBranches, participatesFirstBranch] using
        (participatesAllBranches_imp_participatesFirstBranch body role h)
  | .comm sender receiver branches =>
      unfold participatesAllBranches at h
      unfold participatesFirstBranch
      cases hpart : is_participant role sender receiver with
      | true =>
          simp [hpart]
      | false =>
          simp only [hpart, Bool.false_and, Bool.false_or] at h ⊢
          match hbranches : branches with
          | [] =>
              simp at h
          | (_, cont) :: _ =>
              exact participatesAllBranches_imp_participatesFirstBranch cont role h
termination_by sizeOf g
decreasing_by
  all_goals (first | exact sizeOf_body_lt_mu _ _ | (subst hbranches; exact sizeOf_cont_lt_comm _ _ _ _ _))

mutual
  private theorem trans_isContractive_of_participatesAllBranches_mu
      (t : String) (body : GlobalType) (role : String)
      (hpart : participatesAllBranches role (.mu t body) = true) :
      (trans (.mu t body) role).isContractive = true := by
    -- Mu case: propagate contractiveness down the body.
    unfold participatesAllBranches at hpart
    simp only [trans]
    by_cases hguard : (trans body role).isGuarded t
    · simp only [hguard, ↓reduceIte, LocalTypeR.isContractive, Bool.true_and]
      exact trans_isContractive_of_participatesAllBranches body role hpart
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte, LocalTypeR.isContractive]

  private theorem trans_isContractive_of_participatesAllBranches_comm_participant
      (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
      (hpart_direct : is_participant role sender receiver = true)
      (hbranches : participatesAllBranchesList role branches = true) :
      (trans (.comm sender receiver branches) role).isContractive = true := by
    -- Direct participant: contractiveness from all branches.
    unfold is_participant at hpart_direct
    cases hrole_s : role == sender with
    | true =>
        have heq : role = sender := beq_iff_eq.mp hrole_s
        rw [trans_comm_sender sender receiver role branches heq]
        simp only [LocalTypeR.isContractive]
        exact transBranches_isContractive_of_participatesAllBranches branches role hbranches
    | false =>
        simp only [hrole_s, Bool.false_or] at hpart_direct
        have heq : role = receiver := beq_iff_eq.mp hpart_direct
        have hne : role ≠ sender := by
          intro heq'
          rw [heq'] at hrole_s
          simp at hrole_s
        rw [trans_comm_receiver sender receiver role branches heq hne]
        simp only [LocalTypeR.isContractive]
        exact transBranches_isContractive_of_participatesAllBranches branches role hbranches

  private theorem trans_isContractive_of_participatesAllBranches_comm_nonpart
      (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
      (hpart_direct : is_participant role sender receiver = false)
      (hpart : participatesAllBranches role (.comm sender receiver branches) = true) :
      (trans (.comm sender receiver branches) role).isContractive = true := by
    -- Non-participant: follow the first branch.
    simp only [participatesAllBranches, hpart_direct, Bool.not_false, Bool.false_and, Bool.false_or,
      Bool.true_and] at hpart
    unfold is_participant at hpart_direct
    have hne_s : role ≠ sender := by
      intro heq
      rw [heq] at hpart_direct
      simp at hpart_direct
    have hne_r : role ≠ receiver := by
      intro heq
      rw [heq] at hpart_direct
      simp at hpart_direct
    rw [trans_comm_other sender receiver role branches hne_s hne_r]
    match hbranches : branches with
    | [] => simp at hpart
    | (label, cont) :: rest =>
        exact trans_isContractive_of_participatesAllBranches cont role hpart

  private theorem trans_isContractive_of_participatesAllBranches_comm
      (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
      (hpart : participatesAllBranches role (.comm sender receiver branches) = true) :
      (trans (.comm sender receiver branches) role).isContractive = true := by
    -- Comm case split on direct participation.
    cases hpart_direct : is_participant role sender receiver with
    | true =>
        simp only [participatesAllBranches, hpart_direct, Bool.not_true, Bool.false_and,
          Bool.or_false] at hpart
        exact trans_isContractive_of_participatesAllBranches_comm_participant sender receiver branches role
          hpart_direct hpart
    | false =>
        exact trans_isContractive_of_participatesAllBranches_comm_nonpart sender receiver branches role
          hpart_direct hpart

  /-- Projection is contractive when role participates through all branches.
      This version is FULLY PROVABLE because we have participation
      info for all branch continuations. -/
  theorem trans_isContractive_of_participatesAllBranches (g : GlobalType) (role : String)
      (hpart : participatesAllBranches role g = true) :
      (trans g role).isContractive = true := by
    match g with
    | .end => by simpa [participatesAllBranches] using hpart
    | .var _ => by simpa [participatesAllBranches] using hpart
    | .mu t body =>
        exact trans_isContractive_of_participatesAllBranches_mu t body role hpart
    | .comm sender receiver branches =>
        exact trans_isContractive_of_participatesAllBranches_comm sender receiver branches role hpart
  termination_by sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | (subst hbranches; exact sizeOf_cont_lt_comm _ _ _ _ _)

  /-- Helper: transBranches is contractive when role participates in all branches. -/
  theorem transBranches_isContractive_of_participatesAllBranches
      (branches : List (Label × GlobalType)) (role : String)
      (hpart : participatesAllBranchesList role branches = true) :
      LocalTypeR.isContractiveBranches (transBranches branches role) = true := by
    match branches with
    | [] =>
        simp [transBranches, LocalTypeR.isContractiveBranches]
    | (_, cont) :: rest =>
        simp only [transBranches, LocalTypeR.isContractiveBranches, Bool.and_eq_true]
        unfold participatesAllBranchesList at hpart
        simp only [Bool.and_eq_true] at hpart
        constructor
        · exact trans_isContractive_of_participatesAllBranches cont role hpart.1
        · exact transBranches_isContractive_of_participatesAllBranches rest role hpart.2
  termination_by sizeOf branches
  decreasing_by
    all_goals first
      | exact sizeOf_cont_lt_cons _ _ _
      | exact sizeOf_tail_lt_cons _ _
end

/-- Projection preserves well-formedness when role participates through all branches.
    This version is FULLY PROVABLE. -/
theorem trans_preserves_WellFormed_allBranches (g : GlobalType) (role : String)
    (hclosed : g.isClosed = true)
    (hpart : participatesAllBranches role g = true) :
    LocalTypeR.WellFormed (trans g role) := by
  constructor
  · exact trans_isClosed_of_isClosed g role hclosed
  · exact trans_isContractive_of_participatesAllBranches g role hpart

end RumpsteakV2.Protocol.Projection.Trans

/-! ## Additional Contractiveness Lemmas -/

namespace RumpsteakV2.Protocol.Projection.Trans

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

mutual
  private theorem trans_isContractive_of_isProductive_mu
      (t : String) (body : GlobalType) (role : String)
      (hprod : (GlobalType.mu t body).isProductive = true) :
      (trans (.mu t body) role).isContractive = true := by
    -- Mu case: reduce to body contractiveness.
    simp only [GlobalType.isProductive] at hprod
    have hbody_prod : body.isProductive = true := by
      apply GlobalType.isProductive_mono body [] [t]
      · intro x hx; simp at hx
      · exact hprod
    have hbody : (trans body role).isContractive = true :=
      trans_isContractive_of_isProductive body role hbody_prod
    by_cases hguard : (trans body role).isGuarded t
    · simp [trans, hguard, LocalTypeR.isContractive, hbody]
    · simp [trans, hguard, LocalTypeR.isContractive]

  private theorem trans_isContractive_of_isProductive_comm_sender
      (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
      (hrs : role = sender) (hprod : isProductiveBranches branches [] = true) :
      (trans (.comm sender receiver branches) role).isContractive = true := by
    -- Sender case: contractive branches.
    have hbranches :
        LocalTypeR.isContractiveBranches (transBranches branches role) = true :=
      transBranches_isContractive_of_isProductive branches role hprod
    have htrans := trans_comm_sender sender receiver role branches hrs
    simp [htrans, LocalTypeR.isContractive, hbranches]

  private theorem trans_isContractive_of_isProductive_comm_receiver
      (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
      (hrr : role = receiver) (hrs : role ≠ sender)
      (hprod : isProductiveBranches branches [] = true) :
      (trans (.comm sender receiver branches) role).isContractive = true := by
    -- Receiver case: contractive branches.
    have hbranches :
        LocalTypeR.isContractiveBranches (transBranches branches role) = true :=
      transBranches_isContractive_of_isProductive branches role hprod
    have htrans := trans_comm_receiver sender receiver role branches hrr hrs
    simp [htrans, LocalTypeR.isContractive, hbranches]

  private theorem trans_isContractive_of_isProductive_comm_nonpart
      (sender receiver : String) (branches : List (Label × GlobalType)) (role : String)
      (hrs : role ≠ sender) (hrr : role ≠ receiver)
      (hprod : isProductiveBranches branches [] = true) :
      (trans (.comm sender receiver branches) role).isContractive = true := by
    -- Non-participant: follow first branch (or end).
    cases hbranches : branches with
    | nil =>
        simp [trans, hrs, hrr, LocalTypeR.isContractive]
    | cons head tail =>
        cases head with
        | mk label cont =>
            simp [trans, hrs, hrr]
            simp [hbranches, isProductiveBranches, Bool.and_eq_true] at hprod
            exact trans_isContractive_of_isProductive cont role hprod.1

  /-- trans yields a contractive local type for productive globals. -/
  theorem trans_isContractive_of_isProductive
      (g : GlobalType) (role : String) (hprod : g.isProductive = true) :
      (trans g role).isContractive = true := by
    match g with
    | .end =>
        simp [trans, LocalTypeR.isContractive]
    | .var _ =>
        simp [trans, LocalTypeR.isContractive]
    | .mu t body =>
        exact trans_isContractive_of_isProductive_mu t body role hprod
    | .comm sender receiver branches =>
        have hprod' : isProductiveBranches branches [] = true := by
          simpa [GlobalType.isProductive] using hprod
        by_cases hrs : role = sender
        · exact trans_isContractive_of_isProductive_comm_sender sender receiver branches role hrs hprod'
        · by_cases hrr : role = receiver
          · exact trans_isContractive_of_isProductive_comm_receiver sender receiver branches role hrr hrs hprod'
          · exact trans_isContractive_of_isProductive_comm_nonpart sender receiver branches role hrs hrr hprod'
  termination_by sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | (subst hbranches; exact sizeOf_cont_lt_comm _ _ _ _ _)

  /-- Helper: transBranches is contractive for productive branches. -/
  theorem transBranches_isContractive_of_isProductive
      (branches : List (Label × GlobalType)) (role : String)
      (hprod : isProductiveBranches branches [] = true) :
      LocalTypeR.isContractiveBranches (transBranches branches role) = true := by
    match branches with
    | [] =>
        simp [transBranches, LocalTypeR.isContractiveBranches]
    | (_, cont) :: rest =>
        simp only [transBranches, LocalTypeR.isContractiveBranches, Bool.and_eq_true]
        simp [isProductiveBranches, Bool.and_eq_true] at hprod
        constructor
        · exact trans_isContractive_of_isProductive cont role hprod.1
        · exact transBranches_isContractive_of_isProductive rest role hprod.2
  termination_by sizeOf branches
  decreasing_by
    all_goals first
      | exact sizeOf_cont_lt_cons _ _ _
      | exact sizeOf_tail_lt_cons _ _
end

/-- Well-formed globals project to well-formed locals. -/
theorem trans_wellFormed_of_wellFormed (g : GlobalType) (role : String)
    (hwf : g.wellFormed = true) : LocalTypeR.WellFormed (trans g role) := by
  have hclosed : g.isClosed = true := GlobalType.isClosed_of_wellFormed g hwf
  have hprod : g.isProductive = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.2
  have hcontr : (trans g role).isContractive = true :=
    trans_isContractive_of_isProductive g role hprod
  exact ⟨trans_isClosed_of_isClosed g role hclosed, hcontr⟩

end RumpsteakV2.Protocol.Projection.Trans
