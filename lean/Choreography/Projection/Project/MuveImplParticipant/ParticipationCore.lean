import Choreography.Projection.Project.MuveImplNonPart

/-! # Project MuveImplParticipant

Participant projection classification and part_of2_or_end theorem.
-/

-- Core Development

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
-/

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Projectb
open SessionTypes.Participation
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props

-- Size Helpers
/-- Helper: sizeOf a member's continuation is less than sizeOf the list. -/
private theorem sizeOf_mem_snd_lt {branches : List (Label × GlobalType)} {pair : Label × GlobalType}
    (hmem : pair ∈ branches) :
    sizeOf pair.2 < sizeOf branches := by
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
          omega
      | tail _ hmem' =>
          have ih' := ih hmem'
          simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1] at ih' ⊢
          omega

/-- Helper: sizeOf a member's continuation is less than sizeOf the comm. -/
private theorem sizeOf_mem_snd_lt_comm {sender receiver : String} {branches : List (Label × GlobalType)}
    {pair : Label × GlobalType} (hmem : pair ∈ branches) :
    sizeOf pair.2 < sizeOf (GlobalType.comm sender receiver branches) := by
  have h1 := sizeOf_mem_snd_lt hmem
  have hcomm : sizeOf (GlobalType.comm sender receiver branches) =
      1 + sizeOf sender + sizeOf receiver + sizeOf branches := by
    simp only [GlobalType.comm.sizeOf_spec]
  omega

-- Branch Property Inheritance
/-- Helper: allCommsNonEmpty for a branch list implies allCommsNonEmpty for each member. -/
private theorem allCommsNonEmpty_of_mem {branches : List (Label × GlobalType)} {pair : Label × GlobalType}
    (hmem : pair ∈ branches) (hne : allCommsNonEmptyBranches branches = true) :
    pair.2.allCommsNonEmpty = true := by
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at hne
      cases hmem with
      | head => exact hne.1
      | tail _ hmem' => exact ih hmem' hne.2

/-- Helper: noSelfComm for a branch list implies noSelfComm for each member. -/
private theorem noSelfComm_of_mem {branches : List (Label × GlobalType)} {pair : Label × GlobalType}
    (hmem : pair ∈ branches) (hnsc : noSelfCommBranches branches = true) :
    pair.2.noSelfComm = true := by
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [noSelfCommBranches, Bool.and_eq_true] at hnsc
      cases hmem with
      | head => exact hnsc.1
      | tail _ hmem' => exact ih hmem' hnsc.2

/-- Helper: comm allCommsNonEmpty implies branch allCommsNonEmpty. -/
private theorem allCommsNonEmptyBranches_of_comm {sender receiver : String}
    {branches : List (Label × GlobalType)}
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true) :
    allCommsNonEmptyBranches branches = true := by
  have hne' : branches.isEmpty = false ∧ allCommsNonEmptyBranches branches = true := by
    simpa [GlobalType.allCommsNonEmpty, Bool.and_eq_true] using hne
  exact hne'.2

/-- Helper: comm noSelfComm implies branch noSelfComm. -/
private theorem noSelfCommBranches_of_comm {sender receiver : String}
    {branches : List (Label × GlobalType)}
    (hnsc : (GlobalType.comm sender receiver branches).noSelfComm = true) :
    noSelfCommBranches branches = true := by
  have hnsc' : sender != receiver ∧ noSelfCommBranches branches = true := by
    simpa [GlobalType.noSelfComm, Bool.and_eq_true] using hnsc
  exact hnsc'.2

-- Participation Inversion
/-- Helper: non-participant comm inversion yields a branch witness. -/
private theorem part_of2_comm_inv_nonpart {role sender receiver : String}
    {branches : List (Label × GlobalType)}
    (hpart : part_of2 role (.comm sender receiver branches))
    (hs : role ≠ sender) (hr : role ≠ receiver) :
    ∃ label cont, (label, cont) ∈ branches ∧ part_of2 role cont := by
  have hcases := part_of2_comm_inv (role := role) (sender := sender) (receiver := receiver)
    (branches := branches) hpart
  cases hcases with
  | inl hparticipant =>
      simp [is_participant, Bool.or_eq_true, beq_iff_eq] at hparticipant
      cases hparticipant with
      | inl hsend => exact (hs hsend).elim
      | inr hrecv => exact (hr hrecv).elim
  | inr hexists => exact hexists

-- Muve Negation: Mu/Mu Helper
private theorem CProject_not_muve_of_part_of2_aux_mu_mu (t : String) (body : GlobalType)
    (role t' : String) (candBody : LocalTypeR)
    (hproj : CProject (.mu t body) role (.mu t' candBody))
    (hpart : part_of2 role (.mu t body))
    (hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (ih : ∀ lt', CProject body role lt' → part_of2 role body →
      body.allCommsNonEmpty = true → isMuve lt' = false) :
    isMuve (.mu t' candBody) = false := by
  have hF := CProject_destruct hproj
  dsimp [CProjectF] at hF
  rcases hF with ⟨candBody0, hbody_proj, hcase⟩
  cases hcase with
  | inl hmu =>
      rcases hmu with ⟨_hguard, hEq⟩
      cases hEq
      have hpart_body := part_of2_mu_inv hpart
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      simpa [isMuve] using ih candBody hbody_proj hpart_body hne_body
  | inr hend =>
      rcases hend with ⟨_hguard, hEq⟩
      cases hEq

/-- Helper: mu/end case for CProject_not_muve_of_part_of2_aux. -/
-- Muve Negation: Mu/End Helper
private theorem CProject_not_muve_of_part_of2_aux_mu_end (t : String) (body : GlobalType)
    (role : String)
    (hproj : CProject (.mu t body) role .end)
    (hpart : part_of2 role (.mu t body))
    (hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (ih : ∀ lt', CProject body role lt' → part_of2 role body →
      body.allCommsNonEmpty = true → isMuve lt' = false) :
    isMuve .end = false := by
  rcases CProject_destruct hproj with ⟨candBody0, hbody_proj, hcase⟩
  cases hcase with
  | inl hmu =>
      rcases hmu with ⟨_hguard, hEq⟩; cases hEq
  | inr hend =>
      rcases hend with ⟨hguard, hEq⟩; cases hEq
      have hpart_body := part_of2_mu_inv hpart
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have hmuve_false : isMuve candBody0 = false :=
        ih candBody0 hbody_proj hpart_body hne_body
      have hcontra : (true = false) := by
        simp [isMuve_of_not_guarded candBody0 t hguard] at hmuve_false
      cases hcontra

-- Muve Negation: Mu Dispatcher
private theorem CProject_not_muve_of_part_of2_aux_mu (t : String) (body : GlobalType)
    (role : String) (lt : LocalTypeR)
    (hproj : CProject (.mu t body) role lt)
    (hpart : part_of2 role (.mu t body))
    (hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (ih : ∀ lt', CProject body role lt' → part_of2 role body →
      body.allCommsNonEmpty = true → isMuve lt' = false) :
    isMuve lt = false := by
  cases lt with
  | mu t' candBody =>
      exact CProject_not_muve_of_part_of2_aux_mu_mu t body role t' candBody hproj hpart hne ih
  | «end» =>
      exact CProject_not_muve_of_part_of2_aux_mu_end t body role hproj hpart hne ih
  | var _ =>
      have : False := by
        have hF := CProject_destruct hproj
        simp [CProjectF] at hF
      exact this.elim
  | send _ _ => rfl
  | recv _ _ => rfl

-- Muve Negation: Comm Nonparticipant Helper
private theorem CProject_not_muve_of_part_of2_aux_comm_nonpart
    (sender receiver : String) (branches : List (Label × GlobalType))
    (role : String) (lt : LocalTypeR)
    (hF : ∀ pair, pair ∈ branches → CProject pair.2 role lt)
    (hpart : part_of2 role (.comm sender receiver branches))
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (hs : role ≠ sender) (hr : role ≠ receiver)
    (ih : ∀ pair, pair ∈ branches → CProject pair.2 role lt → part_of2 role pair.2 →
      pair.2.allCommsNonEmpty = true → isMuve lt = false) :
    isMuve lt = false := by
  obtain ⟨label, cont, hmem, hpart_cont⟩ :=
    part_of2_comm_inv_nonpart (role := role) (sender := sender) (receiver := receiver)
      (branches := branches) hpart hs hr
  have hcont_proj : CProject cont role lt := hF (label, cont) hmem
  have hne_branches : allCommsNonEmptyBranches branches = true := by
    exact allCommsNonEmptyBranches_of_comm (sender := sender) (receiver := receiver) hne
  have hne_cont : cont.allCommsNonEmpty = true := allCommsNonEmpty_of_mem hmem hne_branches
  exact ih (label, cont) hmem hcont_proj hpart_cont hne_cont

-- Muve Negation: Comm Cons Helper
private theorem CProject_not_muve_of_part_of2_aux_comm_cons
    (sender receiver : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (role : String) (lt : LocalTypeR)
    (hproj : CProject (.comm sender receiver (first :: rest)) role lt)
    (hpart : part_of2 role (.comm sender receiver (first :: rest)))
    (hne : (GlobalType.comm sender receiver (first :: rest)).allCommsNonEmpty = true)
    (ih : ∀ pair, pair ∈ first :: rest → CProject pair.2 role lt → part_of2 role pair.2 →
      pair.2.allCommsNonEmpty = true → isMuve lt = false) :
    isMuve lt = false := by
  by_cases hs : role = sender
  · subst hs
    have hF := CProject_destruct hproj
    cases lt with
    | send _ _ => rfl
    | recv _ _ => rfl
    | «end» =>
        have hfalse : False := by
          simp [CProjectF] at hF
        exact hfalse.elim
    | var _ =>
        have hfalse : False := by
          simp [CProjectF] at hF
        exact hfalse.elim
    | mu _ _ =>
        have hfalse : False := by
          simp [CProjectF] at hF
        exact hfalse.elim
  -- # Receiver/Nonparticipant Branches
  · by_cases hr : role = receiver
    · subst hr
      have hF := CProject_destruct hproj
      simp [CProjectF, hs] at hF
      cases lt with
      | send _ _ => rfl
      | recv _ _ => rfl
      | «end» =>
          have hfalse : False := by
            simp at hF
          exact hfalse.elim
      | var _ =>
          have hfalse : False := by
            simp at hF
          exact hfalse.elim
      | mu _ _ =>
          have hfalse : False := by
            simp at hF
          exact hfalse.elim
    · have hF := CProject_destruct hproj
      simp [CProjectF, hs, hr] at hF
      have hF' : ∀ pair, pair ∈ first :: rest → CProject pair.2 role lt := by
        intro pair hmem
        exact hF pair hmem
      exact CProject_not_muve_of_part_of2_aux_comm_nonpart sender receiver (first :: rest)
        role lt hF' hpart hne hs hr ih

/-- Auxiliary: Participant projections are NOT muve types.
    This is the converse of CProject_muve_of_not_part_of2.

    If a role participates in a well-formed global type and has a valid projection,
    then the projection must have send/recv at some level (not purely mu/var/end). -/
-- Muve Negation: Main Auxiliary Theorem
private theorem CProject_not_muve_of_part_of2_aux : (g : GlobalType) → (role : String) →
    (lt : LocalTypeR) →
    CProject g role lt →
    part_of2 role g →
    g.allCommsNonEmpty = true →
    isMuve lt = false
  | .end, role, _, _, hpart, _ => by exact (not_part_of2_end role hpart).elim
  | .var t, role, _, _, hpart, _ => by exact (not_part_of2_var role t hpart).elim
  | .mu t body, role, lt, hproj, hpart, hne => by  -- mu case
      exact CProject_not_muve_of_part_of2_aux_mu t body role lt hproj hpart hne
        (fun lt' hproj' hpart' hne' => CProject_not_muve_of_part_of2_aux body role lt' hproj' hpart' hne')
  | .comm _ _ [], _, _, _, _, hne => by
      (simp only [GlobalType.allCommsNonEmpty, List.isEmpty_nil, Bool.and_eq_true, decide_eq_true_eq] at hne;
        exact Bool.noConfusion hne.1)
  | .comm sender receiver (first :: rest), role, lt, hproj, hpart, hne => by
      have ih :
          ∀ pair : Label × GlobalType, pair ∈ first :: rest → CProject pair.2 role lt →
            part_of2 role pair.2 → pair.2.allCommsNonEmpty = true → isMuve lt = false := by
        intro pair hmem hproj' hpart' hne'
        exact CProject_not_muve_of_part_of2_aux pair.2 role lt hproj' hpart' hne'
      exact CProject_not_muve_of_part_of2_aux_comm_cons sender receiver first rest role lt hproj hpart hne ih
termination_by g _ _ _ _ _ => sizeOf g
decreasing_by
  all_goals
    simp_wf
    first
    | (simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1]; omega)
    | simpa [GlobalType.comm.sizeOf_spec] using sizeOf_mem_snd_lt_comm hmem

/-- Participant projections are NOT muve types.

If a role participates in a well-formed global type and has a valid projection,
then the projection must have send/recv at some level (not purely mu/var/end). -/
-- Muve Negation: Public Theorem
theorem CProject_not_muve_of_part_of2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hpart : part_of2 role g)
    (hwf : g.wellFormed = true) :
    isMuve lt = false := by
  have hne : g.allCommsNonEmpty = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  exact CProject_not_muve_of_part_of2_aux g role lt hproj hpart hne

/-- Helper: mu/mu case for CProject_part_of2_implies_part_of_all2_aux. -/
-- all-branch Participation: Mu/Mu Helper
private theorem CProject_part_of2_implies_part_of_all2_aux_mu_mu (t : String) (body : GlobalType)
    (role t' : String) (candBody : LocalTypeR)
    (hproj : CProject (.mu t body) role (.mu t' candBody))
    (hpart : part_of2 role (.mu t body))
    (hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (hnsc : (GlobalType.mu t body).noSelfComm = true)
    (ih : ∀ lt', CProject body role lt' → part_of2 role body →
      body.allCommsNonEmpty = true → body.noSelfComm = true → part_of_all2 role body) :
    part_of_all2 role (.mu t body) := by
  have hF := CProject_destruct hproj
  dsimp [CProjectF] at hF
  rcases hF with ⟨candBody0, hbody_proj, hcase⟩
  cases hcase with
  | inl hmu =>
      rcases hmu with ⟨_hguard, hEq⟩
      cases hEq
      have hpart_body := part_of2_mu_inv hpart
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have hnsc_body : body.noSelfComm = true := by
        simpa [GlobalType.noSelfComm] using hnsc
      have ih' := ih candBody hbody_proj hpart_body hne_body hnsc_body
      exact part_of_all2.intro _ (part_of_allF.mu t body ih')
  | inr hend =>
      rcases hend with ⟨_hguard, hEq⟩
      cases hEq

/-- Helper: mu/end case for CProject_part_of2_implies_part_of_all2_aux. -/
-- all-branch Participation: Mu/End Helper
private theorem CProject_part_of2_implies_part_of_all2_aux_mu_end (t : String) (body : GlobalType)
    (role : String)
    (hproj : CProject (.mu t body) role .end)
    (hpart : part_of2 role (.mu t body))
    (hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (hnsc : (GlobalType.mu t body).noSelfComm = true)
    (ih : ∀ lt', CProject body role lt' → part_of2 role body →
      body.allCommsNonEmpty = true → body.noSelfComm = true → part_of_all2 role body) :
    part_of_all2 role (.mu t body) := by
  have hF := CProject_destruct hproj
  dsimp [CProjectF] at hF
  rcases hF with ⟨candBody0, hbody_proj, hcase⟩
  cases hcase with
  | inl hmu =>
      rcases hmu with ⟨_hguard, hEq⟩
      cases hEq
  | inr hend =>
      rcases hend with ⟨_hguard, hEq⟩
      cases hEq
      have hpart_body := part_of2_mu_inv hpart
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have hnsc_body : body.noSelfComm = true := by
        simpa [GlobalType.noSelfComm] using hnsc
      have ih' := ih candBody0 hbody_proj hpart_body hne_body hnsc_body
      exact part_of_all2.intro _ (part_of_allF.mu t body ih')

/-- Helper: contradiction branch for comm non-participant in CProject_part_of2_implies_part_of_all2_aux. -/
-- all-branch Participation: Comm Contradiction Helper
private theorem CProject_part_of2_implies_part_of_all2_aux_comm_nonpart_contra
    (sender receiver : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (role : String) (lt : LocalTypeR) (pair : Label × GlobalType)
    (hmem : pair ∈ first :: rest)
    (hF : AllBranchesProj CProject (first :: rest) role lt)
    (hpart : part_of2 role (GlobalType.comm sender receiver (first :: rest)))
    (hne_branches : allCommsNonEmptyBranches (first :: rest) = true)
    (hs : role ≠ sender) (hr : role ≠ receiver)
    (hpart_pair : ¬ part_of2 role pair.2) :
    False := by
  have hpair_proj : CProject pair.2 role lt := hF pair hmem  -- derive a muve contradiction
  have hne_pair : pair.2.allCommsNonEmpty = true := allCommsNonEmpty_of_mem hmem hne_branches
  have hmuve : isMuve lt = true := CProject_muve_of_not_part_of2_aux pair.2 role lt hpair_proj hpart_pair hne_pair
  obtain ⟨label, cont, hmem_wit, hpart_wit⟩ := part_of2_comm_inv_nonpart (role := role) (sender := sender) (receiver := receiver) (branches := first :: rest) hpart hs hr
  have hwit_proj : CProject cont role lt := hF (label, cont) hmem_wit
  have hne_wit : cont.allCommsNonEmpty = true := allCommsNonEmpty_of_mem hmem_wit hne_branches
  have hnot_muve : isMuve lt = false := CProject_not_muve_of_part_of2_aux cont role lt hwit_proj hpart_wit hne_wit
  rw [hmuve] at hnot_muve; exact Bool.noConfusion hnot_muve

-- all-branch Participation: Mu Dispatcher
private theorem CProject_part_of2_implies_part_of_all2_aux_mu (t : String) (body : GlobalType)
    (role : String) (lt : LocalTypeR)
    (hproj : CProject (.mu t body) role lt)
    (hpart : part_of2 role (.mu t body))
    (hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (hnsc : (GlobalType.mu t body).noSelfComm = true)
    (ih : ∀ lt', CProject body role lt' → part_of2 role body →
      body.allCommsNonEmpty = true → body.noSelfComm = true → part_of_all2 role body) :
    part_of_all2 role (.mu t body) := by
  cases lt with
  | mu t' candBody =>
      exact CProject_part_of2_implies_part_of_all2_aux_mu_mu t body role t' candBody hproj hpart hne hnsc ih
  | «end» =>
      exact CProject_part_of2_implies_part_of_all2_aux_mu_end t body role hproj hpart hne hnsc ih
  | var _ | send _ _ | recv _ _ =>
      have : False := by
        have hF := CProject_destruct hproj
        simp [CProjectF] at hF
      exact this.elim

-- all-branch Participation: Comm Branch Helper
private theorem CProject_part_of2_implies_part_of_all2_aux_comm_branch
    (sender receiver : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (role : String) (lt : LocalTypeR) (pair : Label × GlobalType)
    (hmem : pair ∈ first :: rest)
    (hF : AllBranchesProj CProject (first :: rest) role lt)
    (hpart : part_of2 role (GlobalType.comm sender receiver (first :: rest)))
    (hne_branches : allCommsNonEmptyBranches (first :: rest) = true)
    (hnsc_branches : noSelfCommBranches (first :: rest) = true)
    (hs : role ≠ sender) (hr : role ≠ receiver)
    (ih : ∀ pair, pair ∈ first :: rest → CProject pair.2 role lt → part_of2 role pair.2 →
      pair.2.allCommsNonEmpty = true → pair.2.noSelfComm = true → part_of_all2 role pair.2) :
    part_of_all2 role pair.2 := by
  have hpair_proj : CProject pair.2 role lt := hF pair hmem
  by_cases hpart_pair : part_of2 role pair.2
  · have hne_pair : pair.2.allCommsNonEmpty = true := allCommsNonEmpty_of_mem hmem hne_branches
    have hnsc_pair : pair.2.noSelfComm = true := noSelfComm_of_mem hmem hnsc_branches
    exact ih pair hmem hpair_proj hpart_pair hne_pair hnsc_pair
  · have hcontra : False :=
      CProject_part_of2_implies_part_of_all2_aux_comm_nonpart_contra
        sender receiver first rest role lt pair hmem hF hpart hne_branches hs hr hpart_pair
    exact False.elim hcontra

-- all-branch Participation: Comm Cons Helper
private theorem CProject_part_of2_implies_part_of_all2_aux_comm_cons
    (sender receiver : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (role : String) (lt : LocalTypeR)
    (hproj : CProject (.comm sender receiver (first :: rest)) role lt)
    (hpart : part_of2 role (.comm sender receiver (first :: rest)))
    (hne : (GlobalType.comm sender receiver (first :: rest)).allCommsNonEmpty = true)
    (hnsc : (GlobalType.comm sender receiver (first :: rest)).noSelfComm = true)
    (ih : ∀ pair, pair ∈ first :: rest → CProject pair.2 role lt → part_of2 role pair.2 →
      pair.2.allCommsNonEmpty = true → pair.2.noSelfComm = true → part_of_all2 role pair.2) :
    part_of_all2 role (.comm sender receiver (first :: rest)) := by
  have hF := CProject_destruct hproj
  simp [CProjectF] at hF
  by_cases hs : role = sender
  · exact part_of_all2.intro _ (part_of_allF.comm_direct sender receiver (first :: rest)
      (by simp [is_participant, hs]))
  · by_cases hr : role = receiver
    · exact part_of_all2.intro _ (part_of_allF.comm_direct sender receiver (first :: rest)
        (by simp [is_participant, hr]))
    · simp [hs, hr] at hF
      have hne_branches : allCommsNonEmptyBranches (first :: rest) = true :=
        allCommsNonEmptyBranches_of_comm (sender := sender) (receiver := receiver) hne
      have hnsc_branches : noSelfCommBranches (first :: rest) = true :=
        noSelfCommBranches_of_comm (sender := sender) (receiver := receiver) hnsc
      apply part_of_all2.intro _ (part_of_allF.comm_all_branches sender receiver (first :: rest) _)
      intro pair hmem
      exact CProject_part_of2_implies_part_of_all2_aux_comm_branch sender receiver first rest
        role lt pair hmem hF hpart hne_branches hnsc_branches hs hr ih
/-- If a role participates and projects, then it participates on all branches. -/
-- all-branch Participation: Main Auxiliary Theorem
private theorem CProject_part_of2_implies_part_of_all2_aux : (g : GlobalType) → (role : String) →
    (lt : LocalTypeR) →
    CProject g role lt →
    part_of2 role g →
    g.allCommsNonEmpty = true →
    g.noSelfComm = true →
    part_of_all2 role g
  | .end, role, _, _, hpart, _, _ => by exact (not_part_of2_end role hpart).elim
  | .var t, role, _, _, hpart, _, _ => by exact (not_part_of2_var role t hpart).elim
  | .mu t body, role, lt, hproj, hpart, hne, hnsc => by
      exact CProject_part_of2_implies_part_of_all2_aux_mu t body role lt hproj hpart hne hnsc
        (fun lt' hproj' hpart' hne' hnsc' =>
          CProject_part_of2_implies_part_of_all2_aux body role lt' hproj' hpart' hne' hnsc')
  | .comm _ _ [], _, _, _, _, hne, _ => by
      simp only [GlobalType.allCommsNonEmpty, List.isEmpty_nil, Bool.and_eq_true,
        decide_eq_true_eq] at hne; exact Bool.noConfusion hne.1
  | .comm sender receiver (first :: rest), role, lt, hproj, hpart, hne, hnsc => by
      exact CProject_part_of2_implies_part_of_all2_aux_comm_cons sender receiver first rest role lt
        hproj hpart hne hnsc
        (fun pair hmem hproj' hpart' hne' hnsc' =>
          CProject_part_of2_implies_part_of_all2_aux pair.2 role lt hproj' hpart' hne' hnsc')
termination_by g _ _ _ _ _ _ => sizeOf g
decreasing_by
  all_goals
    simp_wf
    first
    | (simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1]; omega)
    | simpa [GlobalType.comm.sizeOf_spec] using sizeOf_mem_snd_lt_comm hmem

/-- CProject participation implies all-branch participation (under well-formedness). -/
-- all-branch Participation: Public Theorem
theorem CProject_part_of2_implies_part_of_all2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hpart : part_of2 role g)
    (hwf : g.wellFormed = true) :
    part_of_all2 role g := by
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact CProject_part_of2_implies_part_of_all2_aux g role lt hproj hpart hwf.1.1.2 hwf.1.2
end Choreography.Projection.Project
