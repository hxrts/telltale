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
theorem transBranches_eq_of_BranchesProjRel
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
theorem trans_eq_of_CProject_end (role : String) (cand : LocalTypeR)
    (hproj : CProject .end role cand) : Trans.trans .end role = cand := by
  -- CProjectF for end only allows the end candidate.
  have hf := CProject_destruct hproj
  cases cand <;> simp [CProjectF, Trans.trans] at hf ⊢

/-- Helper: `trans` equality for var case. -/
theorem trans_eq_of_CProject_var (t : String) (role : String) (cand : LocalTypeR)
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
theorem trans_eq_of_CProject_mu
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
theorem trans_eq_of_CProject_comm_sender
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
theorem trans_eq_of_CProject_comm_receiver
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
theorem trans_eq_of_CProject_comm_other
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
theorem trans_eq_of_CProject_comm_sender_send
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
theorem trans_eq_of_CProject_comm_receiver_recv
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
theorem trans_eq_of_CProject_comm_other_nonempty
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
theorem trans_eq_of_CProject_comm_other_case
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
theorem trans_eq_of_CProject_comm_sender_case
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
theorem trans_eq_of_CProject_comm_receiver_case
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

end Choreography.Projection.Projectb
