import Choreography.Projection.Project.ImplConstructors.Base

/-! # Choreography.Projection.Project.ImplConstructors.SendRecv

Send and recv constructor agreement with matching branches.
-/

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
-/

set_option linter.unnecessarySimpa false

/-! ## Core Development -/

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
open SessionCoTypes.EQ2Paco
open Paco
open SessionTypes.Participation
/-! ### Send constructor agreement -/

/- If CProject g role (.send partner lbs) holds, then g must be a comm where role is sender
    (possibly through non-participant layers), and trans g role = .send partner (transBranches ...).

    This follows from CProjectF: only comm with role=sender produces .send. -/

-- Reduce the non-participant comm case of CProjectF to AllBranchesProj.
private theorem CProjectF_comm_other_iff
    (sender receiver role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hrs : role ≠ sender) (hrr : role ≠ receiver) :
    CProjectF CProject (.comm sender receiver gbs) role cand ↔
      AllBranchesProj CProject gbs role cand := by
  simp [CProjectF, hrs, hrr]
/-- Helper: sender case for send projection agreement (comm/cons). -/
private theorem CProject_send_implies_trans_send_comm_cons_sender
    (sender receiver : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (role partner : String) (lbs : List BranchR)
    (hf : CProjectF CProject (GlobalType.comm sender receiver (first :: rest)) role
      (LocalTypeR.send partner lbs))
    (hrs : role = sender) (hwf : (GlobalType.comm sender receiver (first :: rest)).wellFormed = true) :
    ∃ gbs', trans (GlobalType.comm sender receiver (first :: rest)) role =
        .send partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- Sender case is direct from CProjectF.
  simp [CProjectF, hrs] at hf
  obtain ⟨hpartner, hbranches⟩ := hf
  have hbranches' : BranchesProjRel CProject (first :: rest) role lbs := by
    simpa [hrs] using hbranches
  refine ⟨(first :: rest), ?_, hbranches', ?_⟩
  · rw [hrs, trans_comm_sender sender receiver sender (first :: rest) rfl, hpartner]
  · intro gb hmem
    exact GlobalType.wellFormed_comm_branches sender receiver (first :: rest) hwf gb hmem

/-- Helper: receiver role cannot project to `.send`. -/
private theorem CProject_send_implies_trans_send_comm_receiver_contra
    (sender receiver role partner : String) (gbs : List (Label × GlobalType))
    (lbs : List BranchR)
    (hproj : CProject (.comm sender receiver gbs) role (.send partner lbs))
    (hrr : role = receiver) (hrs : role ≠ sender) : False := by
  -- CProjectF forbids .send when the role is receiver.
  have hne : receiver ≠ sender := by
    intro h
    exact hrs (hrr.trans h)
  have hf := CProject_destruct hproj
  simpa [CProjectF, hrr, hne] using hf

/-- Helper: non-participant comm case for send projection agreement. -/
private theorem CProject_send_implies_trans_send_comm_other
    (sender receiver role partner : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (lbs : List BranchR) (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (hrec :
      ∃ gbs', trans first.2 role = .send partner (transBranches gbs' role) ∧
        BranchesProjRel CProject gbs' role lbs ∧
        (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true)) :
    ∃ gbs', trans (.comm sender receiver (first :: rest)) role =
        .send partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- Non-participants use trans_comm_other to select the head branch.
  obtain ⟨gbs', htrans', hbranches', hwf'⟩ := hrec
  refine ⟨gbs', ?_, hbranches', hwf'⟩
  have htrans :
      trans (.comm sender receiver (first :: rest)) role = trans first.2 role := by
    simpa using trans_comm_other sender receiver role (first :: rest) hrs hrr
  simpa [htrans] using htrans'

mutual
/-- Helper: comm/cons case for send projection agreement. -/
private theorem CProject_send_implies_trans_send_comm_cons (g : GlobalType) (sender receiver : String)
      (first : Label × GlobalType) (rest : List (Label × GlobalType)) (role partner : String)
      (lbs : List BranchR) (hproj : CProject g role (.send partner lbs))
      (hg : g = (GlobalType.comm sender receiver (first :: rest))) (hwf : g.wellFormed = true) :
      ∃ gbs', trans (GlobalType.comm sender receiver (first :: rest)) role =
        .send partner (transBranches gbs' role) ∧
        BranchesProjRel CProject gbs' role lbs ∧ (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
    subst hg
    -- Sender case is direct; non-participant recurses on the first branch.
    by_cases hrs : role = sender
    · exact CProject_send_implies_trans_send_comm_cons_sender
        sender receiver first rest role partner lbs (CProject_destruct hproj) hrs hwf
    · by_cases hrr : role = receiver
      · exact (CProject_send_implies_trans_send_comm_receiver_contra sender receiver role partner
          (first :: rest) lbs hproj hrr hrs).elim
      · have hf' : AllBranchesProj CProject (first :: rest) role (.send partner lbs) := by
          exact (CProjectF_comm_other_iff sender receiver role (first :: rest)
            (.send partner lbs) hrs hrr).1 (CProject_destruct hproj)
        have hfirst : CProject first.2 role (.send partner lbs) :=
          CProject_first_of_AllBranchesProj hf'
        have hwf_first : first.2.wellFormed = true :=
          wellFormed_first_of_comm sender receiver first rest hwf
        have hrec := CProject_send_implies_trans_send first.2 role partner lbs hfirst hwf_first
        exact CProject_send_implies_trans_send_comm_other sender receiver role partner first rest lbs
          hrs hrr hrec
termination_by (sizeOf g) * 3
decreasing_by
    all_goals
      simpa [hg] using sizeOf_snd_lt_comm_head_mul3 sender receiver first rest

/-- Helper: comm case for send projection agreement. -/
private theorem CProject_send_implies_trans_send_comm (sender receiver : String)
      (gbs : List (Label × GlobalType)) (role partner : String) (lbs : List BranchR)
      (hproj : CProject (.comm sender receiver gbs) role (.send partner lbs))
      (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
      ∃ gbs', trans (.comm sender receiver gbs) role =
          .send partner (transBranches gbs' role) ∧
        BranchesProjRel CProject gbs' role lbs ∧
        (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
    -- Split on the branch list; empty is impossible under wellFormed.
    cases hgb : gbs with
    | nil =>
        have hwf' : (GlobalType.comm sender receiver []).wellFormed = true := by
          simpa [hgb] using hwf
        have hne : (GlobalType.comm sender receiver []).allCommsNonEmpty = true :=
          allCommsNonEmpty_of_wellFormed _ hwf'
        have : False := by simpa [GlobalType.allCommsNonEmpty] using hne
        exact this.elim
    | cons first rest =>
        have hproj' : CProject (.comm sender receiver (first :: rest)) role (.send partner lbs) := by
          simpa [hgb] using hproj
        have hwf' : (GlobalType.comm sender receiver (first :: rest)).wellFormed = true := by
          simpa [hgb] using hwf
        exact CProject_send_implies_trans_send_comm_cons (.comm sender receiver (first :: rest))
          sender receiver first rest role partner lbs hproj' rfl hwf'
termination_by (sizeOf (GlobalType.comm sender receiver gbs)) * 3 + 1
decreasing_by
    all_goals
      simp [hgb, GlobalType.comm.sizeOf_spec]
/-- If CProject g role (.send partner lbs) holds, then g must be a comm where role is sender
      (possibly through non-participant layers), and trans g role = .send partner (transBranches ...). -/
theorem CProject_send_implies_trans_send (g : GlobalType) (role : String)
      (partner : String) (lbs : List BranchR)
      (hproj : CProject g role (.send partner lbs))
      (hwf : g.wellFormed = true) :
      ∃ gbs', trans g role = .send partner (transBranches gbs' role) ∧
        BranchesProjRel CProject gbs' role lbs ∧
        (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
    -- Dispatch by constructor; comm uses the helper above.
    cases hg : g with
    | «end» =>
        exact CProject_send_implies_trans_send_end role partner lbs (by simpa [hg] using hproj)
    | var v =>
        exact CProject_send_implies_trans_send_var v role partner lbs (by simpa [hg] using hproj)
    | mu t body =>
        exact CProject_send_implies_trans_send_mu t body role partner lbs
          (by simpa [hg] using hproj)
    | comm sender receiver gbs =>
        simpa [hg] using
          (CProject_send_implies_trans_send_comm sender receiver gbs role partner lbs
            (by simpa [hg] using hproj) (by simpa [hg] using hwf))
termination_by (sizeOf g) * 3 + 2
decreasing_by
    all_goals
      simp [hg, GlobalType.comm.sizeOf_spec]
end

/-- Helper: `.end` cannot project to `.recv`. -/
private theorem CProject_recv_implies_trans_recv_end (role partner : String)
    (lbs : List BranchR)
    (hproj : CProject .end role (.recv partner lbs)) :
    ∃ gbs', trans .end role = .recv partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- CProjectF forbids .end → .recv.
  have hf := CProject_destruct hproj
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: `.var` cannot project to `.recv`. -/
private theorem CProject_recv_implies_trans_recv_var (v role partner : String)
    (lbs : List BranchR)
    (hproj : CProject (.var v) role (.recv partner lbs)) :
    ∃ gbs', trans (.var v) role = .recv partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- CProjectF forbids .var → .recv.
  have hf := CProject_destruct hproj
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: `.mu` cannot project to `.recv`. -/
private theorem CProject_recv_implies_trans_recv_mu (t : String) (body : GlobalType)
    (role partner : String) (lbs : List BranchR)
    (hproj : CProject (.mu t body) role (.recv partner lbs)) :
    ∃ gbs', trans (.mu t body) role = .recv partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- CProjectF forbids .mu → .recv.
  have hf := CProject_destruct hproj
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: receiver case for recv projection agreement (comm/cons). -/
private theorem CProject_recv_implies_trans_recv_comm_cons_receiver
    (sender receiver : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (role partner : String) (lbs : List BranchR)
    (hf : CProjectF CProject (GlobalType.comm sender receiver (first :: rest)) role
      (LocalTypeR.recv partner lbs))
    (hrs : role ≠ sender) (hrr : role = receiver)
    (hwf : (GlobalType.comm sender receiver (first :: rest)).wellFormed = true) :
    ∃ gbs', trans (GlobalType.comm sender receiver (first :: rest)) role =
        .recv partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- Receiver case is direct from CProjectF.
  subst hrr
  simp [CProjectF, hrs] at hf
  obtain ⟨hpartner, hbranches⟩ := hf
  refine ⟨(first :: rest), ?_, hbranches, ?_⟩
  · rw [trans_comm_receiver sender role role (first :: rest) rfl hrs, hpartner]
  · intro gb hmem
    exact GlobalType.wellFormed_comm_branches sender role (first :: rest) hwf gb hmem

/-! ### Recv constructor agreement -/

/-- Helper: sender role cannot project to `.recv`. -/
private theorem CProject_recv_implies_trans_recv_comm_sender_contra
    (sender receiver role partner : String) (gbs : List (Label × GlobalType))
    (lbs : List BranchR)
    (hproj : CProject (.comm sender receiver gbs) role (.recv partner lbs))
    (hrs : role = sender) : False := by
  -- CProjectF forbids .recv when the role is sender.
  have hf := CProject_destruct hproj
  simpa [CProjectF, hrs] using hf

/-- Helper: non-participant comm case for recv projection agreement. -/
private theorem CProject_recv_implies_trans_recv_comm_other
    (sender receiver role partner : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (lbs : List BranchR) (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (hrec :
      ∃ gbs', trans first.2 role = .recv partner (transBranches gbs' role) ∧
        BranchesProjRel CProject gbs' role lbs ∧
        (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true)) :
    ∃ gbs', trans (.comm sender receiver (first :: rest)) role =
        .recv partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- Non-participants use trans_comm_other to select the head branch.
  obtain ⟨gbs', htrans', hbranches', hwf'⟩ := hrec
  refine ⟨gbs', ?_, hbranches', hwf'⟩
  have htrans :
      trans (.comm sender receiver (first :: rest)) role = trans first.2 role := by
    simpa using trans_comm_other sender receiver role (first :: rest) hrs hrr
  simpa [htrans] using htrans'

/- Symmetric version for recv. -/
mutual
/-- Helper: comm/cons case for recv projection agreement. -/
private theorem CProject_recv_implies_trans_recv_comm_cons (g : GlobalType) (sender receiver : String)
      (first : Label × GlobalType) (rest : List (Label × GlobalType)) (role partner : String)
      (lbs : List BranchR) (hproj : CProject g role (.recv partner lbs))
      (hg : g = (GlobalType.comm sender receiver (first :: rest))) (hwf : g.wellFormed = true) :
      ∃ gbs', trans (GlobalType.comm sender receiver (first :: rest)) role =
        .recv partner (transBranches gbs' role) ∧
        BranchesProjRel CProject gbs' role lbs ∧ (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
    subst hg -- Receiver case is direct; non-participant recurses on the first branch.
    by_cases hrs : role = sender
    · exact (CProject_recv_implies_trans_recv_comm_sender_contra sender receiver role partner
        (first :: rest) lbs hproj hrs).elim
    · by_cases hrr : role = receiver
      · exact CProject_recv_implies_trans_recv_comm_cons_receiver sender receiver first rest role
          partner lbs (CProject_destruct hproj) hrs hrr hwf
      · have hf' : AllBranchesProj CProject (first :: rest) role (.recv partner lbs) := by
          exact (CProjectF_comm_other_iff sender receiver role (first :: rest)
            (.recv partner lbs) hrs hrr).1 (CProject_destruct hproj)
        have hfirst : CProject first.2 role (.recv partner lbs) :=
          CProject_first_of_AllBranchesProj hf'
        have hwf_first : first.2.wellFormed = true := by
          exact wellFormed_first_of_comm sender receiver first rest hwf
        have hrec :=
          CProject_recv_implies_trans_recv first.2 role partner lbs hfirst hwf_first
        exact CProject_recv_implies_trans_recv_comm_other sender receiver role partner first rest lbs
          hrs hrr hrec
termination_by (sizeOf g) * 3
decreasing_by
    all_goals
      simpa [hg] using sizeOf_snd_lt_comm_head_mul3 sender receiver first rest

/-- Helper: comm case for recv projection agreement. -/
private theorem CProject_recv_implies_trans_recv_comm (sender receiver : String)
      (gbs : List (Label × GlobalType)) (role partner : String) (lbs : List BranchR)
      (hproj : CProject (.comm sender receiver gbs) role (.recv partner lbs))
      (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
      ∃ gbs', trans (.comm sender receiver gbs) role =
          .recv partner (transBranches gbs' role) ∧
        BranchesProjRel CProject gbs' role lbs ∧
        (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
    -- Split on the branch list; empty is impossible under wellFormed.
    cases hgb : gbs with
    | nil =>
        have hwf' : (GlobalType.comm sender receiver []).wellFormed = true := by
          simpa [hgb] using hwf
        have hne : (GlobalType.comm sender receiver []).allCommsNonEmpty = true :=
          allCommsNonEmpty_of_wellFormed _ hwf'
        have : False := by simpa [GlobalType.allCommsNonEmpty] using hne
        exact this.elim
    | cons first rest =>
        have hproj' : CProject (.comm sender receiver (first :: rest)) role (.recv partner lbs) := by
          simpa [hgb] using hproj
        have hwf' : (GlobalType.comm sender receiver (first :: rest)).wellFormed = true := by
          simpa [hgb] using hwf
        exact CProject_recv_implies_trans_recv_comm_cons (.comm sender receiver (first :: rest))
          sender receiver first rest role partner lbs hproj' rfl hwf'
termination_by (sizeOf (GlobalType.comm sender receiver gbs)) * 3 + 1
decreasing_by
    all_goals
      simp [hgb, GlobalType.comm.sizeOf_spec]
/-- Symmetric version for recv. -/
theorem CProject_recv_implies_trans_recv (g : GlobalType) (role : String) (partner : String)
      (lbs : List BranchR) (hproj : CProject g role (.recv partner lbs)) (hwf : g.wellFormed = true) :
      ∃ gbs', trans g role = .recv partner (transBranches gbs' role) ∧ BranchesProjRel CProject gbs' role lbs ∧
        (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
    cases hg : g with -- Dispatch by constructor; comm uses the helper above.
    | «end» => exact CProject_recv_implies_trans_recv_end role partner lbs (by simpa [hg] using hproj)
    | var v => exact CProject_recv_implies_trans_recv_var v role partner lbs (by simpa [hg] using hproj)
    | mu t body =>
        exact CProject_recv_implies_trans_recv_mu t body role partner lbs (by simpa [hg] using hproj)
    | comm sender receiver gbs =>
        simpa [hg] using
          (CProject_recv_implies_trans_recv_comm sender receiver gbs role partner lbs
            (by simpa [hg] using hproj) (by simpa [hg] using hwf))
termination_by (sizeOf g) * 3 + 2
decreasing_by
    all_goals
      simp [hg, GlobalType.comm.sizeOf_spec]
end

/-- Helper: if CProject g role lt holds with lt.isGuarded v = true,
    then (trans g role).isGuarded v = true.

    This follows from the EQ2 relationship between lt and trans g role:
    EQ2-equivalent types have the same observable head structure (modulo mu-unfolding),
    so if lt is not .var v at head, then trans g role is also not .var v at head.

    For well-formed types (contractive, closed), this property holds because:
    - EQ2 preserves the observable "kind" of the head constructor
    - isGuarded v = true means the type is not .var v at head (or shadowed by mu) -/
theorem CProject_isGuarded_trans {g : GlobalType} {role : String} {lt : LocalTypeR} {v : String}
    (hproj : CProject g role lt) (hwf : g.allCommsNonEmpty = true) (hguard : lt.isGuarded v = true) :
    (trans g role).isGuarded v = true := by
  -- Reduce to trans = lt from CProject, then rewrite.
  have htrans : trans g role = lt := trans_eq_of_CProject g role lt hproj hwf
  simpa [htrans] using hguard

end Choreography.Projection.Project
