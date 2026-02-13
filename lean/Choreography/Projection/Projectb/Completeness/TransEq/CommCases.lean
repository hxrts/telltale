import Choreography.Projection.Projectb.Completeness.TransEq.Core

/-! # Choreography.Projection.Projectb.Completeness.TransEq.CommCases

Communication-case lemmas for `trans_eq_of_CProject`.
-/

/-
The Problem. The comm-case proof for trans-equality is sizable and easier to
maintain separately from the constructor-base helpers.

Solution Structure. Contains comm-case helper lemmas and finishes
`trans_eq_of_CProject`.
-/

namespace Choreography.Projection.Projectb
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

/-! ## Communication Cases -/

theorem trans_eq_of_CProject_comm_case
    (sender receiver role : String) (branches : List (Label × GlobalType)) (cand : LocalTypeR)
    (hproj : CProject (.comm sender receiver branches) role cand)
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (ih : ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb) :
    Trans.trans (.comm sender receiver branches) role = cand := by
  -- Route to sender/receiver/non-participant handlers.
  by_cases hrs : role = sender
  · exact trans_eq_of_CProject_comm_sender_case sender receiver role branches cand hrs hproj hne ih
  · by_cases hrr : role = receiver
    · exact trans_eq_of_CProject_comm_receiver_case sender receiver role branches cand hrr hrs hproj hne ih
    · exact trans_eq_of_CProject_comm_other_case sender receiver role branches cand hrs hrr hproj hne ih

/-! ## trans_eq_of_CProject Main Recursion -/

/-- If CProject holds and all comms are non-empty, `trans` must return the same candidate. -/
theorem trans_eq_of_CProject (g : GlobalType) (role : String) (cand : LocalTypeR)
    (hproj : CProject g role cand) (hne : g.allCommsNonEmpty = true) :
    Trans.trans g role = cand := by
  -- Dispatch on the global constructor and reuse helper lemmas.
  cases g with
  | «end» => exact trans_eq_of_CProject_end role cand hproj
  | var t => exact trans_eq_of_CProject_var t role cand hproj
  | mu t body =>
      have hf := CProject_destruct hproj
      simp [CProjectF] at hf
      rcases hf with ⟨candBody, hbody, hcase⟩
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have htrans_body : Trans.trans body role = candBody :=
        trans_eq_of_CProject body role candBody hbody hne_body
      exact trans_eq_of_CProject_mu t body role cand candBody hcase htrans_body
  -- trans_eq_of_CProject: Comm Branch
  | comm sender receiver branches =>
      have hne_branches :
          ∀ gb ∈ branches, gb.2.allCommsNonEmpty = true :=
        GlobalType.allCommsNonEmpty_comm_branches sender receiver branches hne
      have ih :
          ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb :=
        fun gb hmem lb hcp => trans_eq_of_CProject gb.2 role lb hcp (hne_branches gb hmem)
      exact trans_eq_of_CProject_comm_case sender receiver role branches cand hproj hne ih
  -- trans_eq_of_CProject: Delegate Branch
  | delegate p q sid r cont =>
      by_cases hp : role = p
      · have hf := CProject_destruct hproj
        cases cand with
        | send partner lbs =>
            cases lbs with
            | nil =>
                simp [CProjectF, hp] at hf
            | cons b bs =>
                cases bs with
                | nil =>
                    cases b with
                    | mk lbl rest =>
                        cases rest with
                        | mk vt contCand =>
                            simp [CProjectF, hp] at hf
                            rcases hf with ⟨hpartner, hlbl, hvt, hcont⟩
                            have hne_cont : cont.allCommsNonEmpty = true := by
                              simpa [GlobalType.allCommsNonEmpty] using hne
                            have hcont' : Trans.trans cont p = contCand :=
                              trans_eq_of_CProject cont p contCand hcont hne_cont
                            subst hpartner
                            subst hlbl
                            subst hvt
                            simp [Trans.trans, hp]
                            exact hcont'
                | cons b2 bs2 =>
/- ## Structured Block 1 -/
                    simp [CProjectF, hp] at hf
        | recv _ _ =>
            simp [CProjectF, hp] at hf
        | «end» =>
            simp [CProjectF, hp] at hf
        | var _ =>
            simp [CProjectF, hp] at hf
        | mu _ _ =>
            simp [CProjectF, hp] at hf
      -- trans_eq_of_CProject: Delegate Receiver/Other
      · by_cases hq : role = q
        · have hnp : q ≠ p := by
            intro hqp
            exact hp (hq.trans hqp)
          have hf := CProject_destruct hproj
          cases cand with
          | recv partner lbs =>
              cases lbs with
              | nil =>
                  simp [CProjectF, hq, hnp] at hf
              | cons b bs =>
                  cases bs with
                  | nil =>
                      cases b with
                      | mk lbl rest =>
                          cases rest with
                          | mk vt contCand =>
                              have hf' :
                                  partner = p ∧ lbl = ⟨"_delegate", .unit⟩ ∧
                                    vt = some (.chan sid r) ∧ CProject cont q contCand := by
                                simpa [CProjectF, hq, hnp] using hf
                              rcases hf' with ⟨hpartner, hlbl, hvt, hcont⟩
                              have hne_cont : cont.allCommsNonEmpty = true := by
                                simpa [GlobalType.allCommsNonEmpty] using hne
                              have hcont' : Trans.trans cont q = contCand :=
                                trans_eq_of_CProject cont q contCand hcont hne_cont
                              subst hpartner
                              subst hlbl
                              subst hvt
                              have hpeq : (role == partner) = false := by
                                have : (q == partner) = false := beq_eq_false_iff_ne.mpr hnp
                                simpa [hq] using this
                              have hqeq : (role == q) = true := by
                                simp [hq]
                              have hcont'' : Trans.trans cont role = contCand := by
                                simpa [hq] using hcont'
                              simp [Trans.trans, hpeq, hqeq, hcont'']
                  | cons b2 bs2 =>
                      simp [CProjectF, hq, hnp] at hf
          | send _ _ =>
              simp [CProjectF, hq, hnp] at hf
/- ## Structured Block 2 -/
          | «end» =>
              simp [CProjectF, hq, hnp] at hf
          | var _ =>
              simp [CProjectF, hq, hnp] at hf
          | mu _ _ =>
              simp [CProjectF, hq, hnp] at hf
        -- trans_eq_of_CProject: Delegate Non-Participant
        · -- non-participant: follow continuation
          have hf := CProject_destruct hproj
          simp [CProjectF, hp, hq] at hf
          have hne_cont : cont.allCommsNonEmpty = true := by
            simpa [GlobalType.allCommsNonEmpty] using hne
          have hcont' : Trans.trans cont role = cand :=
            trans_eq_of_CProject cont role cand hf hne_cont
          simp [Trans.trans, hp, hq, hcont']
termination_by g
decreasing_by
  all_goals
    first
    | (subst_vars; exact sizeOf_body_lt_mu _ _)
    | (subst_vars; apply sizeOf_elem_snd_lt_comm; assumption)
    | (subst_vars; simp only [sizeOf, GlobalType._sizeOf_1]; omega)

/-! ## projectb Completeness Helpers -/

/-! ## projectb Completeness: Base Cases -/

/-- Completeness: if CProject holds and all comms are non-empty, then projectb returns true.
    Proven by well-founded recursion on g. -/
theorem projectb_complete_end (role : String) (cand : LocalTypeR)
    (h : CProject .end role cand) : projectb .end role cand = true := by
  -- Only the end candidate is consistent with CProject for end.
  have hF := CProject_destruct h
  cases cand <;> simp [CProjectF, projectb] at hF ⊢

theorem projectb_complete_var (t : String) (role : String) (cand : LocalTypeR)
    (h : CProject (.var t) role cand) : projectb (.var t) role cand = true := by
  -- CProject forces the variable name to match.
  have hF := CProject_destruct h
  cases cand <;> simp [CProjectF, projectb] at hF ⊢
  · subst hF; simp

/-! ## projectb Completeness: Mu Cases -/

theorem projectb_complete_mu_mu (t : String) (body : GlobalType) (role : String)
    (candBody : LocalTypeR) (hguard : candBody.isGuarded t = true)
    (hproj_body : projectb body role candBody = true) :
    projectb (GlobalType.mu t body) role (.mu t candBody) = true := by
  -- Guarded branch of projectb.
  simp [projectb, hguard, hproj_body]

theorem projectb_complete_mu_end (t : String) (body : GlobalType) (role : String)
    (candBody : LocalTypeR) (hguard : candBody.isGuarded t = false)
    (hproj_body : projectb body role candBody = true)
    (htrans_body : Trans.trans body role = candBody) :
    projectb (GlobalType.mu t body) role .end = true := by
  -- Unguarded branch of projectb.
  simp [projectb, htrans_body, hguard, hproj_body]

/-! ## projectb Completeness: Mu Dispatcher -/

theorem projectb_complete_mu
    (t : String) (body : GlobalType) (role : String) (cand candBody : LocalTypeR)
    (hcase : (candBody.isGuarded t = true ∧ cand = .mu t candBody) ∨
      (candBody.isGuarded t = false ∧ cand = .end))
    (hproj_body : projectb body role candBody = true)
    (htrans_body : Trans.trans body role = candBody) :
    projectb (GlobalType.mu t body) role cand = true := by
  -- Use the guardedness witness to pick the correct `projectb` branch.
  cases cand with
  | mu t' candBody' =>
      rcases hcase with ⟨hguard, hmu⟩ | ⟨_hguard, hend⟩
      · cases hmu; exact projectb_complete_mu_mu t body role candBody hguard hproj_body
      · cases hend
  | «end» =>
      rcases hcase with ⟨_hguard, hmu⟩ | ⟨hguard, hend⟩
      · cases hmu
      · cases hend; exact projectb_complete_mu_end t body role candBody hguard hproj_body htrans_body
  | var _ =>
      cases hcase with
      | inl h => cases h.2
      | inr h => cases h.2
  | send _ _ =>
      cases hcase with
      | inl h => cases h.2
      | inr h => cases h.2
  | recv _ _ =>
      cases hcase with
      | inl h => cases h.2
      | inr h => cases h.2

/-! ## projectb Completeness: Comm Cases -/

theorem projectb_complete_comm_sender
    (s r role : String) (gbs : List (Label × GlobalType))
    (partner : String) (lbs : List BranchR)
    (hs : role = s) (hpartner : partner = r)
    (hbranches_proj : projectbBranches gbs role lbs = true) :
    projectb (GlobalType.comm s r gbs) role (.send partner lbs) = true := by
  subst hs
  subst hpartner
  simp [projectb, hbranches_proj]

/-! ## projectb Completeness: Comm Receiver -/

theorem projectb_complete_comm_receiver
    (s r role : String) (gbs : List (Label × GlobalType))
    (partner : String) (lbs : List BranchR)
    (hr : role = r) (hs : role ≠ s) (hpartner : partner = s)
    (hbranches_proj : projectbBranches gbs role lbs = true) :
    projectb (GlobalType.comm s r gbs) role (.recv partner lbs) = true := by
  have hne_sender : (role == s) = false := by
    simp [beq_eq_false_iff_ne, hs]
  have hne_receiver : (role == r) = true := by
    simp [hr]
  have hpartner_beq : (partner == s) = true := by
    simp [hpartner]
  simpa [projectb, hne_sender, hne_receiver, hpartner_beq] using hbranches_proj

/-! ## projectb Completeness: Comm Non-Participant -/

theorem projectb_complete_comm_other
    (s r role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hs : role ≠ s) (hr : role ≠ r)
    (hbranches_proj : projectbAllBranches gbs role cand = true) :
    projectb (GlobalType.comm s r gbs) role cand = true := by
  -- Non-participants reduce to the all-branches check.
  have hne_s : (role == s) = false := beq_eq_false_iff_ne.mpr hs
  have hne_r : (role == r) = false := beq_eq_false_iff_ne.mpr hr
  unfold projectb
  simp [hne_s, hne_r, hbranches_proj]



end Choreography.Projection.Projectb
