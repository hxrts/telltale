import Choreography.Projection.Trans.Participation

/-! # Trans Contractive

Contractiveness preservation for projection: `trans_isContractive_of_participatesAllBranches`
and `trans_wellFormed_of_wellFormed`.
-/

namespace Choreography.Projection.Trans
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
/-! ## Fully Proven Contractiveness with All-Branch Participation

The `participatesAllBranches` predicate is stronger than `participatesFirstBranch`:
- For direct participants, it requires participation in ALL branch continuations
- This ensures that `transBranches` produces contractive results
- The theorem `trans_isContractive_of_participatesAllBranches` is fully provable
-/

/-! ## Size-Of Lemmas for Termination -/

private theorem sizeOf_snd_lt_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf b < sizeOf (a, b) := by
  simp only [sizeOf, Prod._sizeOf_1]
  omega

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf x < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_head_snd_lt_cons (pair : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (pair :: rest) := by
  have h1 : sizeOf pair.2 < sizeOf pair := sizeOf_snd_lt_prod pair.1 pair.2
  have h2 : sizeOf pair < sizeOf (pair :: rest) := sizeOf_head_lt_cons pair rest
  exact Nat.lt_trans h1 h2

private theorem sizeOf_bs_lt_comm (sender receiver : String) (bs : List (Label × GlobalType)) :
    sizeOf bs < sizeOf (GlobalType.comm sender receiver bs) := by
  simp only [GlobalType.comm.sizeOf_spec]
  have h : 0 < 1 + sizeOf sender + sizeOf receiver := by omega
  omega

private theorem sizeOf_cont_lt_comm
    (sender receiver : String) (label : Label) (cont : GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf (GlobalType.comm sender receiver ((label, cont) :: rest)) := by
  have h1 : sizeOf cont < sizeOf ((label, cont) :: rest) :=
    sizeOf_head_snd_lt_cons (label, cont) rest
  have h2 : sizeOf ((label, cont) :: rest) < sizeOf (GlobalType.comm sender receiver ((label, cont) :: rest)) :=
    sizeOf_bs_lt_comm sender receiver ((label, cont) :: rest)
  exact Nat.lt_trans h1 h2

private theorem sizeOf_cont_lt_cons (label : Label) (cont : GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf ((label, cont) :: rest) := by
  exact sizeOf_head_snd_lt_cons (label, cont) rest

private theorem sizeOf_body_lt_mu (t : String) (body : GlobalType) :
    sizeOf body < sizeOf (GlobalType.mu t body) := by
  have hk : 0 < 1 + sizeOf t := by
    simp only [Nat.one_add]
    exact Nat.succ_pos (sizeOf t)
  have h : sizeOf body < (1 + sizeOf t) + sizeOf body :=
    Nat.lt_add_of_pos_left (n := sizeOf body) (k := 1 + sizeOf t) hk
  simp only [sizeOf, GlobalType._sizeOf_1]
  omega

theorem participatesAllBranches_imp_participatesFirstBranch (g : GlobalType) (role : String) :
    participatesAllBranches role g = true → participatesFirstBranch role g = true := by
  intro h
  match g with
  | .end =>
      simp [participatesAllBranches] at h
  | .var _ =>
      simp [participatesAllBranches] at h
  | .mu _ body =>
      simpa [participatesAllBranches, participatesFirstBranch] using
        (participatesAllBranches_imp_participatesFirstBranch body role h)
  | .comm sender receiver [] =>
      unfold participatesAllBranches at h
      unfold participatesFirstBranch
      cases hpart : is_participant role sender receiver with
      | true => simp [hpart] at h ⊢
      | false =>
          simp only [hpart, Bool.false_and, Bool.false_or] at h ⊢
          cases h
  | .comm sender receiver ((label, cont) :: rest) =>
      unfold participatesAllBranches at h
      unfold participatesFirstBranch
      cases hpart : is_participant role sender receiver with
      | true =>
          simp
      | false =>
          simp only [hpart, Bool.false_and, Bool.false_or] at h ⊢
          exact participatesAllBranches_imp_participatesFirstBranch cont role h
termination_by sizeOf g
decreasing_by
  all_goals
    first
    | exact sizeOf_body_lt_mu _ _
    | exact sizeOf_cont_lt_comm _ _ _ _ _

mutual
  /-- Projection is contractive when role participates through all branches. -/
  theorem trans_isContractive_of_participatesAllBranches (g : GlobalType) (role : String)
      (hpart : participatesAllBranches role g = true) :
      (trans g role).isContractive = true := by
    match g with
    | .end =>
        simp [trans, LocalTypeR.isContractive]
    | .var _ =>
        simp [trans, LocalTypeR.isContractive]
    | .mu t body =>
        simp [participatesAllBranches] at hpart
        simp only [trans]
        by_cases hguard : (trans body role).isGuarded t
        · simp [hguard, LocalTypeR.isContractive]
          exact trans_isContractive_of_participatesAllBranches body role hpart
        · simp [hguard, LocalTypeR.isContractive]
    | .comm sender receiver [] =>
        cases hpart_direct : is_participant role sender receiver with
        | true =>
            have hbranches : participatesAllBranchesList role [] = true := by
              unfold participatesAllBranches at hpart
              simp [hpart_direct] at hpart
              exact hpart
            unfold is_participant at hpart_direct
            cases hrole_s : role == sender with
            | true =>
                have heq : role = sender := beq_iff_eq.mp hrole_s
                rw [trans_comm_sender sender receiver role [] heq]
                simp [LocalTypeR.isContractive, isContractiveBranches, transBranches]
            | false =>
                simp only [hrole_s, Bool.false_or] at hpart_direct
                have heq : role = receiver := beq_iff_eq.mp hpart_direct
                have hne : role ≠ sender := by
                  intro heq'
                  rw [heq'] at hrole_s
                  simp at hrole_s
                rw [trans_comm_receiver sender receiver role [] heq hne]
                simp [LocalTypeR.isContractive, isContractiveBranches, transBranches]
        | false =>
            have hne_s : role ≠ sender := by
              intro heq
              have : is_participant role sender receiver = true := by
                simp [is_participant, heq]
              simp [hpart_direct] at this
            have hne_r : role ≠ receiver := by
              intro heq
              have : is_participant role sender receiver = true := by
                simp [is_participant, heq, Bool.or_comm]
              simp [hpart_direct] at this
            rw [trans_comm_other sender receiver role [] hne_s hne_r]
            simp [LocalTypeR.isContractive]
    | .comm sender receiver ((label, cont) :: rest) =>
        cases hpart_direct : is_participant role sender receiver with
        | true =>
            have hbranches : participatesAllBranchesList role ((label, cont) :: rest) = true := by
              unfold participatesAllBranches at hpart
              simp [hpart_direct] at hpart
              exact hpart
            unfold is_participant at hpart_direct
            cases hrole_s : role == sender with
            | true =>
                have heq : role = sender := beq_iff_eq.mp hrole_s
                rw [trans_comm_sender sender receiver role ((label, cont) :: rest) heq]
                simp only [LocalTypeR.isContractive]
                exact transBranches_isContractive_of_participatesAllBranches ((label, cont) :: rest) role hbranches
            | false =>
                simp only [hrole_s, Bool.false_or] at hpart_direct
                have heq : role = receiver := beq_iff_eq.mp hpart_direct
                have hne : role ≠ sender := by
                  intro heq'
                  rw [heq'] at hrole_s
                  simp at hrole_s
                rw [trans_comm_receiver sender receiver role ((label, cont) :: rest) heq hne]
                simp only [LocalTypeR.isContractive]
                exact transBranches_isContractive_of_participatesAllBranches ((label, cont) :: rest) role hbranches
        | false =>
            unfold participatesAllBranches at hpart
            simp [hpart_direct] at hpart
            unfold is_participant at hpart_direct
            have hne_s : role ≠ sender := by
              intro heq
              rw [heq] at hpart_direct
              simp at hpart_direct
            have hne_r : role ≠ receiver := by
              intro heq
              rw [heq] at hpart_direct
              simp at hpart_direct
            rw [trans_comm_other sender receiver role ((label, cont) :: rest) hne_s hne_r]
            exact trans_isContractive_of_participatesAllBranches cont role hpart
  termination_by sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | exact sizeOf_cont_lt_comm _ _ _ _ _

  /-- Helper: transBranches is contractive when role participates in all branches. -/
  theorem transBranches_isContractive_of_participatesAllBranches
      (branches : List (Label × GlobalType)) (role : String)
      (hpart : participatesAllBranchesList role branches = true) :
      isContractiveBranches (transBranches branches role) = true := by
    match branches with
    | [] =>
        simp [transBranches, isContractiveBranches]
    | (_, cont) :: rest =>
        simp only [transBranches, isContractiveBranches, Bool.and_eq_true]
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

end Choreography.Projection.Trans

/-! ## Additional Contractiveness Lemmas -/

namespace Choreography.Projection.Trans

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

mutual
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
        -- Mu case: reduce to body contractiveness.
        simp only [GlobalType.isProductive] at hprod
        have hbody_prod : body.isProductive = true := by
          apply isProductive_mono body [] [t]
          · intro x hx; simp at hx
          · exact hprod
        have hbody : (trans body role).isContractive = true :=
          trans_isContractive_of_isProductive body role hbody_prod
        by_cases hguard : (trans body role).isGuarded t
        · simp [trans, hguard, LocalTypeR.isContractive, hbody]
        · simp [trans, hguard, LocalTypeR.isContractive]
    | .comm sender receiver branches =>
        have hprod' : isProductiveBranches branches [] = true := by
          simpa [GlobalType.isProductive] using hprod
        by_cases hrs : role = sender
        · have hbranches :
            isContractiveBranches (transBranches branches role) = true :=
            transBranches_isContractive_of_isProductive branches role hprod'
          have htrans := trans_comm_sender sender receiver role branches hrs
          simp [htrans, LocalTypeR.isContractive, hbranches]
        · by_cases hrr : role = receiver
          · have hbranches :
              isContractiveBranches (transBranches branches role) = true :=
              transBranches_isContractive_of_isProductive branches role hprod'
            have htrans := trans_comm_receiver sender receiver role branches hrr hrs
            simp [htrans, LocalTypeR.isContractive, hbranches]
          · match branches with
            | [] =>
                simp [trans, hrs, hrr, LocalTypeR.isContractive]
            | (label, cont) :: tail =>
                simp [trans, hrs, hrr]
                have hpair : cont.isProductive = true ∧
                    isProductiveBranches tail [] = true := by
                  simpa [isProductiveBranches, Bool.and_eq_true] using hprod'
                exact trans_isContractive_of_isProductive cont role hpair.1
  termination_by sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | exact sizeOf_cont_lt_comm _ _ _ _ _

  /-- Helper: transBranches is contractive for productive branches. -/
  theorem transBranches_isContractive_of_isProductive
      (branches : List (Label × GlobalType)) (role : String)
      (hprod : isProductiveBranches branches [] = true) :
      isContractiveBranches (transBranches branches role) = true := by
    match branches with
    | [] =>
        simp [transBranches, isContractiveBranches]
    | (_, cont) :: rest =>
        simp only [transBranches, isContractiveBranches, Bool.and_eq_true]
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

end Choreography.Projection.Trans
