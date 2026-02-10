import Choreography.Projection.Projectb.Soundness

/-! ## Core Development -/

namespace Choreography.Projection.Projectb
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

/-! # Choreography.Projection.Projectb.Completeness

`trans_eq_of_CProject` and full completeness of `projectb`.
-/

/-
The Problem. We need to show that `projectb` is complete: if CProject holds for
some candidate, then `projectb` returns that candidate. This ensures the checker
finds all valid projections, not just some of them.

Solution Structure. The proof proceeds by coinduction on CProject:
1. `trans_eq_of_CProject`: CProject implies trans computes the candidate
2. Case analysis on global type constructors (end, var, mu, comm)
3. Branch helpers for send/recv cases with Forall₂ induction
-/

/-! ### trans Branch Helper -/

/-- Helper: compute `transBranches` from a BranchesProjRel witness. -/
private theorem transBranches_eq_of_BranchesProjRel
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List BranchR)
    (hrel : BranchesProjRel CProject gbs role lbs)
    (hne : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb) :
    Trans.transBranches gbs role = lbs := by
  induction hrel with
  | nil =>
      simp [Trans.transBranches]
  | @cons ghd lhd gtl ltl hpair hrest ihrest =>
      obtain ⟨hlabel, hnone, hproj⟩ := hpair
      have hne_tail : ∀ gb ∈ gtl, gb.2.allCommsNonEmpty = true := by
        intro gb hmem
        exact hne gb (List.Mem.tail ghd hmem)
      have ih_tail :
          ∀ gb ∈ gtl, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb := by
        intro gb hmem lb hcp
        exact ih gb (List.Mem.tail ghd hmem) lb hcp
      have htail : Trans.transBranches gtl role = ltl :=
        ihrest hne_tail ih_tail
      cases ghd with
      | mk glabel gcont =>
          cases lhd with
          | mk lbl rest =>
              cases rest with
              | mk vt cont =>
                  have htrans_head : Trans.trans gcont role = cont :=
                    ih (glabel, gcont) (List.Mem.head gtl) cont hproj
                  -- Use label/valtype equalities to align the head branch.
                  subst hlabel
                  subst hnone
                  simp [Trans.transBranches, htrans_head, htail]

/-- Helper: `trans` equality for end case. -/
private theorem trans_eq_of_CProject_end (role : String) (cand : LocalTypeR)
    (hproj : CProject .end role cand) : Trans.trans .end role = cand := by
  -- CProjectF for end only allows the end candidate.
  have hf := CProject_destruct hproj
  cases cand <;> simp [CProjectF, Trans.trans] at hf ⊢

/-- Helper: `trans` equality for var case. -/
private theorem trans_eq_of_CProject_var (t : String) (role : String) (cand : LocalTypeR)
    (hproj : CProject (.var t) role cand) : Trans.trans (.var t) role = cand := by
  -- CProjectF forces matching variables, otherwise contradiction.
  have hf := CProject_destruct hproj
  cases cand with
  | var t' =>
      -- Variable case: use the equality extracted from CProjectF.
      simpa [CProjectF, Trans.trans] using hf
  | «end» => simp [CProjectF] at hf
  | send _ _ => simp [CProjectF] at hf
  | recv _ _ => simp [CProjectF] at hf
  | mu _ _ => simp [CProjectF] at hf

/-- Helper: `trans` equality for mu case once the body trans is fixed. -/
private theorem trans_eq_of_CProject_mu
    (t : String) (body : GlobalType) (role : String)
    (cand candBody : LocalTypeR)
    (hcase :
      (candBody.isGuarded t = true ∧ cand = .mu t candBody) ∨
        (candBody.isGuarded t = false ∧ cand = .end))
    (htrans_body : Trans.trans body role = candBody) :
    Trans.trans (.mu t body) role = cand := by
  -- Use the guardedness witness to pick the correct `trans` branch.
  cases hcase with
  | inl hguarded =>
      rcases hguarded with ⟨hguard, hlt⟩
      subst hlt
      simp [Trans.trans, htrans_body, hguard]
  | inr hunguarded =>
      rcases hunguarded with ⟨hguard, hlt⟩
      subst hlt
      simp [Trans.trans, htrans_body, hguard]

/-- Helper: sender comm case once branches are aligned. -/
private theorem trans_eq_of_CProject_comm_sender
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (lbs : List BranchR) (hrs : role = sender)
    (htrans_branches : Trans.transBranches branches role = lbs) :
    Trans.trans (.comm sender receiver branches) role = .send receiver lbs := by
  -- Rewrite the comm trans with the computed branch translation.
  have htrans_comm :
      Trans.trans (.comm sender receiver branches) role =
        .send receiver (Trans.transBranches branches role) := by
    simpa [hrs] using (Trans.trans_comm_sender sender receiver role branches hrs)
  simp [htrans_comm, htrans_branches]

/-- Helper: receiver comm case once branches are aligned. -/
private theorem trans_eq_of_CProject_comm_receiver
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (lbs : List BranchR) (hrr : role = receiver) (hrs : role ≠ sender)
    (htrans_branches : Trans.transBranches branches role = lbs) :
    Trans.trans (.comm sender receiver branches) role = .recv sender lbs := by
  -- Rewrite the comm trans with the computed branch translation.
  have htrans_comm :
      Trans.trans (.comm sender receiver branches) role =
        .recv sender (Trans.transBranches branches role) := by
    simpa [hrr, hrs] using (Trans.trans_comm_receiver sender receiver role branches hrr hrs)
  simp [htrans_comm, htrans_branches]

/-- Helper: non-participant comm case once the head branch is fixed. -/
private theorem trans_eq_of_CProject_comm_other
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (first : Label × GlobalType) (rest : List (Label × GlobalType)) (cand : LocalTypeR)
    (hrs : role ≠ sender) (hrr : role ≠ receiver) (hbranches_eq : branches = first :: rest)
    (htrans_first : Trans.trans first.2 role = cand) :
    Trans.trans (.comm sender receiver branches) role = cand := by
  -- Non-participants inherit the projection from the head branch.
  have htrans_comm :
      Trans.trans (.comm sender receiver branches) role = Trans.trans first.2 role := by
    simpa [hbranches_eq] using
      (Trans.trans_comm_other sender receiver role (first :: rest) hrs hrr)
  simp [htrans_comm, htrans_first]

/-- Helper: sender comm case for send candidates. -/
private theorem trans_eq_of_CProject_comm_sender_send
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (partner : String) (lbs : List BranchR) (hrs : role = sender)
    (hproj : CProject (GlobalType.comm sender receiver branches) role (.send partner lbs))
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (ih : ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb) :
    Trans.trans (.comm sender receiver branches) role = .send partner lbs := by
  -- Extract branch projection and translate the branches.
  have hf := CProject_destruct hproj
  simp [CProjectF, hrs] at hf
  rcases hf with ⟨hpartner, hbranches⟩
  have hbranches' : BranchesProjRel CProject branches role lbs := by
    simpa [hrs] using hbranches
  have hne_branches :
      ∀ gb ∈ branches, gb.2.allCommsNonEmpty = true :=
    GlobalType.allCommsNonEmpty_comm_branches sender receiver branches hne
  have htrans_branches : Trans.transBranches branches role = lbs :=
    transBranches_eq_of_BranchesProjRel branches role lbs hbranches' hne_branches
      (fun gb hmem lb hcp => ih gb hmem lb hcp)
  subst hpartner
  have htrans :=
    trans_eq_of_CProject_comm_sender sender partner role branches lbs hrs htrans_branches
  simpa using htrans

/-- Helper: receiver comm case for recv candidates. -/
private theorem trans_eq_of_CProject_comm_receiver_recv
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (partner : String) (lbs : List BranchR) (hrr : role = receiver)
    (hrs : role ≠ sender)
    (hproj : CProject (GlobalType.comm sender receiver branches) role (.recv partner lbs))
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (ih : ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb) :
    Trans.trans (.comm sender receiver branches) role = .recv partner lbs := by
  -- Extract branch projection and translate the branches.
  have hns : receiver ≠ sender := by simpa [hrr] using hrs
  have hf := CProject_destruct hproj
  simp [CProjectF, hrr, hns] at hf
  rcases hf with ⟨hpartner, hbranches⟩
  have hbranches' : BranchesProjRel CProject branches role lbs := by
    simpa [hrr] using hbranches
  have hne_branches :
      ∀ gb ∈ branches, gb.2.allCommsNonEmpty = true :=
    GlobalType.allCommsNonEmpty_comm_branches sender receiver branches hne
  have htrans_branches : Trans.transBranches branches role = lbs :=
    transBranches_eq_of_BranchesProjRel branches role lbs hbranches' hne_branches
      (fun gb hmem lb hcp => ih gb hmem lb hcp)
  subst hpartner
  have htrans :=
    trans_eq_of_CProject_comm_receiver partner receiver role branches lbs hrr hrs htrans_branches
  simpa using htrans

/-- Helper: non-participant comm case on non-empty branches. -/
private theorem trans_eq_of_CProject_comm_other_nonempty
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (first : Label × GlobalType) (rest : List (Label × GlobalType)) (cand : LocalTypeR)
    (hrs : role ≠ sender) (hrr : role ≠ receiver) (hbranches_eq : branches = first :: rest)
    (hproj : CProject (GlobalType.comm sender receiver branches) role cand)
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (ih : ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb) :
    Trans.trans (.comm sender receiver branches) role = cand := by
  -- Non-participants inherit the first branch projection.
  have hf := CProject_destruct hproj
  simp [CProjectF, hrs, hrr] at hf
  have hmem : first ∈ branches := by simp [hbranches_eq]
  have hproj_first : CProject first.2 role cand := hf first hmem
  have hne_branches :
      ∀ gb ∈ branches, gb.2.allCommsNonEmpty = true :=
    GlobalType.allCommsNonEmpty_comm_branches sender receiver branches hne
  have htrans_first : Trans.trans first.2 role = cand :=
    ih first hmem cand hproj_first
  have htrans :=
    trans_eq_of_CProject_comm_other sender receiver role branches first rest cand hrs hrr
      hbranches_eq htrans_first
  simpa [hbranches_eq] using htrans

/-- Helper: non-participant comm case dispatcher. -/
private theorem trans_eq_of_CProject_comm_other_case
    (sender receiver role : String) (branches : List (Label × GlobalType)) (cand : LocalTypeR)
    (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (hproj : CProject (GlobalType.comm sender receiver branches) role cand)
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (ih : ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb) :
    Trans.trans (.comm sender receiver branches) role = cand := by
  -- Empty branches are impossible under allCommsNonEmpty.
  cases hbranches_eq : branches with
  | nil =>
      have : False := by
        simp [GlobalType.allCommsNonEmpty, hbranches_eq] at hne
      exact this.elim
  | cons first rest =>
      subst hbranches_eq
      exact trans_eq_of_CProject_comm_other_nonempty sender receiver role (first :: rest) first rest
        cand hrs hrr rfl hproj hne ih

/-- Helper: sender comm case dispatcher. -/
private theorem trans_eq_of_CProject_comm_sender_case
    (sender receiver role : String) (branches : List (Label × GlobalType)) (cand : LocalTypeR)
    (hrs : role = sender) (hproj : CProject (GlobalType.comm sender receiver branches) role cand)
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (ih : ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb) :
    Trans.trans (.comm sender receiver branches) role = cand := by
  -- Only send candidates are possible for sender roles.
  cases cand with
  | send partner lbs =>
      exact trans_eq_of_CProject_comm_sender_send sender receiver role branches partner lbs
        hrs hproj hne ih
  | «end» =>
      have hf' : False := by
        have hf := CProject_destruct hproj
        simp [CProjectF, hrs] at hf
      exact hf'.elim
  | var _ =>
      have hf' : False := by
        have hf := CProject_destruct hproj
        simp [CProjectF, hrs] at hf
      exact hf'.elim
  | recv _ _ =>
      have hf' : False := by
        have hf := CProject_destruct hproj
        simp [CProjectF, hrs] at hf
      exact hf'.elim
  | mu _ _ =>
      have hf' : False := by
        have hf := CProject_destruct hproj
        simp [CProjectF, hrs] at hf
      exact hf'.elim

/-- Helper: receiver comm case dispatcher. -/
private theorem trans_eq_of_CProject_comm_receiver_case
    (sender receiver role : String) (branches : List (Label × GlobalType)) (cand : LocalTypeR)
    (hrr : role = receiver) (hrs : role ≠ sender)
    (hproj : CProject (GlobalType.comm sender receiver branches) role cand)
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (ih : ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb) :
    Trans.trans (.comm sender receiver branches) role = cand := by
  -- Only recv candidates are possible for receiver roles.
  have hns : receiver ≠ sender := by simpa [hrr] using hrs
  cases cand with
  | recv partner lbs =>
      exact trans_eq_of_CProject_comm_receiver_recv sender receiver role branches partner lbs
        hrr hrs hproj hne ih
  | «end» =>
      have hf' : False := by
        have hf := CProject_destruct hproj
        simp [CProjectF, hrr, hns] at hf
      exact hf'.elim
  | var _ =>
      have hf' : False := by
        have hf := CProject_destruct hproj
        simp [CProjectF, hrr, hns] at hf
      exact hf'.elim
  | send _ _ =>
      have hf' : False := by
        have hf := CProject_destruct hproj
        simp [CProjectF, hrr, hns] at hf
      exact hf'.elim
  | mu _ _ =>
      have hf' : False := by
        have hf := CProject_destruct hproj
        simp [CProjectF, hrr, hns] at hf
      exact hf'.elim

/-- Helper: comm case dispatcher across role participation. -/
private theorem trans_eq_of_CProject_comm_case
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
  | comm sender receiver branches =>
      have hne_branches :
          ∀ gb ∈ branches, gb.2.allCommsNonEmpty = true :=
        GlobalType.allCommsNonEmpty_comm_branches sender receiver branches hne
      have ih :
          ∀ gb ∈ branches, ∀ lb, CProject gb.2 role lb → Trans.trans gb.2 role = lb :=
        fun gb hmem lb hcp => trans_eq_of_CProject gb.2 role lb hcp (hne_branches gb hmem)
      exact trans_eq_of_CProject_comm_case sender receiver role branches cand hproj hne ih
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
                    simp [CProjectF, hp] at hf
        | recv _ _ =>
            simp [CProjectF, hp] at hf
        | «end» =>
            simp [CProjectF, hp] at hf
        | var _ =>
            simp [CProjectF, hp] at hf
        | mu _ _ =>
            simp [CProjectF, hp] at hf
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
          | «end» =>
              simp [CProjectF, hq, hnp] at hf
          | var _ =>
              simp [CProjectF, hq, hnp] at hf
          | mu _ _ =>
              simp [CProjectF, hq, hnp] at hf
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

/-- Completeness: if CProject holds and all comms are non-empty, then projectb returns true.
    Proven by well-founded recursion on g. -/
private theorem projectb_complete_end (role : String) (cand : LocalTypeR)
    (h : CProject .end role cand) : projectb .end role cand = true := by
  -- Only the end candidate is consistent with CProject for end.
  have hF := CProject_destruct h
  cases cand <;> simp [CProjectF, projectb] at hF ⊢

private theorem projectb_complete_var (t : String) (role : String) (cand : LocalTypeR)
    (h : CProject (.var t) role cand) : projectb (.var t) role cand = true := by
  -- CProject forces the variable name to match.
  have hF := CProject_destruct h
  cases cand <;> simp [CProjectF, projectb] at hF ⊢
  · subst hF; simp

private theorem projectb_complete_mu_mu (t : String) (body : GlobalType) (role : String)
    (candBody : LocalTypeR) (hguard : candBody.isGuarded t = true)
    (hproj_body : projectb body role candBody = true) :
    projectb (GlobalType.mu t body) role (.mu t candBody) = true := by
  -- Guarded branch of projectb.
  simp [projectb, hguard, hproj_body]

private theorem projectb_complete_mu_end (t : String) (body : GlobalType) (role : String)
    (candBody : LocalTypeR) (hguard : candBody.isGuarded t = false)
    (hproj_body : projectb body role candBody = true)
    (htrans_body : Trans.trans body role = candBody) :
    projectb (GlobalType.mu t body) role .end = true := by
  -- Unguarded branch of projectb.
  simp [projectb, htrans_body, hguard, hproj_body]

private theorem projectb_complete_mu
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

private theorem projectb_complete_comm_sender
    (s r role : String) (gbs : List (Label × GlobalType))
    (partner : String) (lbs : List BranchR)
    (hs : role = s) (hpartner : partner = r)
    (hbranches_proj : projectbBranches gbs role lbs = true) :
    projectb (GlobalType.comm s r gbs) role (.send partner lbs) = true := by
  subst hs
  subst hpartner
  simp [projectb, hbranches_proj]

private theorem projectb_complete_comm_receiver
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

private theorem projectb_complete_comm_other
    (s r role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hs : role ≠ s) (hr : role ≠ r)
    (hbranches_proj : projectbAllBranches gbs role cand = true) :
    projectb (GlobalType.comm s r gbs) role cand = true := by
  -- Non-participants reduce to the all-branches check.
  have hne_s : (role == s) = false := beq_eq_false_iff_ne.mpr hs
  have hne_r : (role == r) = false := beq_eq_false_iff_ne.mpr hr
  unfold projectb
  simp [hne_s, hne_r, hbranches_proj]

/-! ### Completeness Helpers -/

/-- Helper: branch projection for comm sender/receiver cases. -/
private theorem projectbBranches_of_CProject_comm
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List BranchR)
    (hbranches : BranchesProjRel CProject gbs role lbs)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true) :
    projectbBranches gbs role lbs = true := by
  -- Use branch relation and recurse on continuations.
  exact BranchesProjRel_to_projectbBranches gbs role lbs hbranches
    (fun gb hmem lb hcp => ih gb hmem lb hcp)

/-- Helper: all-branches projection for non-participants. -/
private theorem projectbAllBranches_of_CProject_comm
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR)
    (hbranches : AllBranchesProj CProject gbs role cand)
    (ih : ∀ gb ∈ gbs, CProject gb.2 role cand → projectb gb.2 role cand = true) :
    projectbAllBranches gbs role cand = true := by
  -- Use all-branches relation and recurse on continuations.
  exact AllBranchesProj_to_projectbAllBranches gbs role cand hbranches
    (fun gb hmem hcp => ih gb hmem hcp)

/-- Helper: completeness for mu cases. -/
private theorem projectb_complete_mu_case
    (t : String) (body : GlobalType) (role : String) (cand : LocalTypeR)
    (hproj : CProject (GlobalType.mu t body) role cand)
    (hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (ih : ∀ candBody, CProject body role candBody → projectb body role candBody = true) :
    projectb (GlobalType.mu t body) role cand = true := by
  -- Extract the body projection and reuse trans equality to pick the branch.
  have hF := CProject_destruct hproj
  simp [CProjectF] at hF
  rcases hF with ⟨candBody, hbody, hcase⟩
  have hne_body : body.allCommsNonEmpty = true := by
    simpa [GlobalType.allCommsNonEmpty] using hne
  have hproj_body : projectb body role candBody = true :=
    ih candBody hbody
  have htrans_body : Trans.trans body role = candBody :=
    trans_eq_of_CProject body role candBody hbody hne_body
  exact projectb_complete_mu t body role cand candBody hcase hproj_body htrans_body

/-- Helper: completeness for comm sender cases. -/
private theorem projectb_complete_comm_sender_case
    (s r role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hs : role = s) (hproj : CProject (.comm s r gbs) role cand)
    (_hne_branches : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true) :
    projectb (.comm s r gbs) role cand = true := by
  -- Sender roles must yield send candidates with branch-wise projections.
  have hF := CProject_destruct hproj
  simp [CProjectF, hs] at hF
  cases cand with
  | send partner lbs =>
      rcases hF with ⟨hpartner, hbranches⟩
      have hbranches_proj : projectbBranches gbs role lbs = true :=
        projectbBranches_of_CProject_comm gbs role lbs (by simpa [hs] using hbranches) ih
      exact projectb_complete_comm_sender s r role gbs partner lbs hs hpartner hbranches_proj
  | _ => cases hF

/-- Helper: completeness for comm receiver cases. -/
private theorem projectb_complete_comm_receiver_case
    (s r role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hr : role = r) (hs : role ≠ s) (hproj : CProject (.comm s r gbs) role cand)
    (_hne_branches : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true) :
    projectb (.comm s r gbs) role cand = true := by
  -- Receiver roles must yield recv candidates with branch-wise projections.
  have hrs : r ≠ s := by simpa [hr] using hs
  have hF := CProject_destruct hproj
  simp [CProjectF, hr, hrs] at hF
  cases cand with
  | recv partner lbs =>
      rcases hF with ⟨hpartner, hbranches⟩
      have hbranches_proj : projectbBranches gbs role lbs = true :=
        projectbBranches_of_CProject_comm gbs role lbs (by simpa [hr] using hbranches) ih
      exact projectb_complete_comm_receiver s r role gbs partner lbs hr hs hpartner hbranches_proj
  | _ => cases hF

/-- Helper: completeness for comm non-participant cases. -/
private theorem projectb_complete_comm_other_case
    (s r role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hs : role ≠ s) (hr : role ≠ r) (hproj : CProject (.comm s r gbs) role cand)
    (_hne_branches : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true)
    (ih : ∀ gb ∈ gbs, CProject gb.2 role cand → projectb gb.2 role cand = true) :
    projectb (.comm s r gbs) role cand = true := by
  -- Non-participants must project all branches to the same candidate.
  have hF := CProject_destruct hproj
  simp [CProjectF, hs, hr] at hF
  have hbranches_proj : projectbAllBranches gbs role cand = true :=
    projectbAllBranches_of_CProject_comm gbs role cand hF ih
  exact projectb_complete_comm_other s r role gbs cand hs hr hbranches_proj

/-- Completeness: every CProject witness satisfies the boolean checker. -/
theorem projectb_complete (g : GlobalType) (role : String) (cand : LocalTypeR)
    (h : CProject g role cand) (hne : g.allCommsNonEmpty = true) :
    projectb g role cand = true := by
  -- Main recursion over the global constructor.
  cases g with
  | «end» => exact projectb_complete_end role cand h
  | var t => exact projectb_complete_var t role cand h
  | mu t body =>
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have ih_body : ∀ candBody, CProject body role candBody → projectb body role candBody = true :=
        fun candBody hbody => projectb_complete body role candBody hbody hne_body
      exact projectb_complete_mu_case t body role cand h hne ih_body
  | comm s r gbs =>
      have hne_branches : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true :=
        GlobalType.allCommsNonEmpty_comm_branches _ _ gbs hne
      have ih_branches :
          ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true :=
        fun gb hmem lb hcp => projectb_complete gb.2 role lb hcp (hne_branches gb hmem)
      have ih_all :
          ∀ gb ∈ gbs, CProject gb.2 role cand → projectb gb.2 role cand = true :=
        fun gb hmem hcp => projectb_complete gb.2 role cand hcp (hne_branches gb hmem)
      by_cases hs : role = s
      · exact projectb_complete_comm_sender_case s r role gbs cand hs h hne_branches ih_branches
      · by_cases hr : role = r
        · exact projectb_complete_comm_receiver_case s r role gbs cand hr hs h hne_branches ih_branches
        · exact projectb_complete_comm_other_case s r role gbs cand hs hr h hne_branches ih_all
  | delegate p q sid r cont =>
      have hne_cont : cont.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      by_cases hp : role = p
      · have hf := CProject_destruct h
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
                            have hproj_cont : projectb cont role contCand = true := by
                              simpa [hp] using
                                (projectb_complete cont p contCand hcont hne_cont)
                            subst hpartner
                            subst hlbl
                            subst hvt
                            simp [projectb, hp]
                            refine And.intro ?_ (And.intro ?_ ?_)
                            · simp [reduceBEq]
                            · simp [reduceBEq]
                            · simpa [hp] using hproj_cont
                | cons b2 bs2 =>
                    simp [CProjectF, hp] at hf
        | recv _ _ =>
            simp [CProjectF, hp] at hf
        | «end» =>
            simp [CProjectF, hp] at hf
        | var _ =>
            simp [CProjectF, hp] at hf
        | mu _ _ =>
            simp [CProjectF, hp] at hf
      · by_cases hq : role = q
        · have hnp : q ≠ p := by
            intro hqp
            exact hp (hq.trans hqp)
          have hf := CProject_destruct h
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
                              have hproj_cont : projectb cont role contCand = true := by
                                simpa [hq] using
                                  (projectb_complete cont q contCand hcont hne_cont)
                              subst hpartner
                              subst hlbl
                              subst hvt
                              simp [projectb, hq, hnp]
                              refine And.intro ?_ (And.intro ?_ ?_)
                              · simp [reduceBEq]
                              · simp [reduceBEq]
                              · simpa [hq] using hproj_cont
                  | cons b2 bs2 =>
                      simp [CProjectF, hq, hnp] at hf
          | send _ _ =>
              simp [CProjectF, hq, hnp] at hf
          | «end» =>
              simp [CProjectF, hq, hnp] at hf
          | var _ =>
              simp [CProjectF, hq, hnp] at hf
          | mu _ _ =>
              simp [CProjectF, hq, hnp] at hf
        · -- non-participant: follow continuation
          have hf := CProject_destruct h
          simp [CProjectF, hp, hq] at hf
          have hproj_cont : projectb cont role cand = true :=
            projectb_complete cont role cand hf hne_cont
          have hpeq : (role == p) = false := beq_eq_false_iff_ne.mpr hp
          have hqeq : (role == q) = false := beq_eq_false_iff_ne.mpr hq
          unfold projectb
          simp [hpeq, hqeq, hproj_cont]
termination_by g
decreasing_by
  all_goals
    -- Now we have context like: hg : g = GlobalType... and hmem : gb ∈ gbs
    -- Use cases to match which termination goal we're in
    first
    -- mu case: sizeOf body < sizeOf g where g = GlobalType.mu t body
    | (subst_vars; exact sizeOf_body_lt_mu _ _)
    -- comm case: sizeOf gb.2 < sizeOf g where g = GlobalType.comm s r gbs and gb ∈ gbs
    | (subst_vars; apply sizeOf_elem_snd_lt_comm; assumption)
    -- delegate case: sizeOf cont < sizeOf g
    | (subst_vars; simp only [sizeOf, GlobalType._sizeOf_1]; omega)

/-- projectb = true iff CProject holds (for non-empty comms). -/
theorem projectb_iff_CProject (g : GlobalType) (role : String) (cand : LocalTypeR)
    (hne : g.allCommsNonEmpty = true) :
    projectb g role cand = true ↔ CProject g role cand :=
  ⟨projectb_sound g role cand, fun h => projectb_complete g role cand h hne⟩

end Choreography.Projection.Projectb
