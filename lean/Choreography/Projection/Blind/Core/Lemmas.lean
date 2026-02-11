import Choreography.Projection.Blind.Core.Predicate

/-! # Choreography.Projection.Blind.Core.Lemmas

Propagation and uniformity lemmas for blindness.
-/

/-
The Problem. Mid-level blindness lemmas are needed to support the main
projectability theorem while keeping the predicate development compact.

Solution Structure. Collects propagation/non-empty/branch-uniformity lemmas
on top of the predicate/checker development.
-/

namespace Choreography.Projection.Blind

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb

section
open Classical

/-! ## Propagation Lemmas -/

theorem payload_beq_refl (p : PayloadSort) : (p == p) = true := by
  -- Payload sort equality is reflexive by cases.
  induction p with
  | unit => rfl
  | nat => rfl
  | bool => rfl
  | string => rfl
  | real => rfl
  | vector n => simp only [reduceBEq, beq_self_eq_true]
  | prod p1 p2 ih1 ih2 =>
      have heq :
          (PayloadSort.prod p1 p2 == PayloadSort.prod p1 p2) = ((p1 == p1) && (p2 == p2)) := rfl
      simp [heq, ih1, ih2]

theorem label_beq_refl (lbl : Label) : (lbl == lbl) = true := by
  -- Reduce to component-wise beq on label fields.
  cases lbl with
  | mk name sort =>
      have heq :
          (({ name := name, sort := sort } : Label) == { name := name, sort := sort }) =
            ((name == name) && (sort == sort)) := rfl
      simp [heq, payload_beq_refl sort]

/-- noSelfComm propagates to mu body (trivially, by definition). -/
theorem noSelfComm_mu_body {t : String} {body : GlobalType}
    (h : (GlobalType.mu t body).noSelfComm = true) : body.noSelfComm = true := h

/-- noSelfComm propagates to delegate continuation. -/
theorem noSelfComm_delegate_cont {p q : String} {sid : Nat} {r : String} {cont : GlobalType}
    (h : (GlobalType.delegate p q sid r cont).noSelfComm = true) : cont.noSelfComm = true := by
  simp only [GlobalType.noSelfComm, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-- Helper: noSelfCommBranches implies noSelfComm for each element. -/
theorem noSelfComm_of_noSelfCommBranches {bs : List (Label × GlobalType)}
    (h : noSelfCommBranches bs = true) :
    ∀ p ∈ bs, p.2.noSelfComm = true := by
  intro p hp
  induction bs generalizing p with
  | nil => simp at hp
  | cons hd tl ih =>
      simp only [noSelfCommBranches, Bool.and_eq_true] at h
      cases hp with
      | head => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- noSelfComm propagates to comm branches. -/
theorem noSelfComm_comm_branches {s r : String} {bs : List (Label × GlobalType)}
    (h : (GlobalType.comm s r bs).noSelfComm = true) :
    ∀ p ∈ bs, p.2.noSelfComm = true := by
  simp only [GlobalType.noSelfComm, Bool.and_eq_true] at h
  exact noSelfComm_of_noSelfCommBranches h.2

/-- allCommsNonEmpty propagates to mu body. -/
theorem allCommsNonEmpty_mu_body {t : String} {body : GlobalType}
    (h : (GlobalType.mu t body).allCommsNonEmpty = true) : body.allCommsNonEmpty = true := h

/-- Helper: allCommsNonEmptyBranches implies allCommsNonEmpty for each element. -/
theorem allCommsNonEmpty_of_allCommsNonEmptyBranches {bs : List (Label × GlobalType)}
    (h : allCommsNonEmptyBranches bs = true) :
    ∀ p ∈ bs, p.2.allCommsNonEmpty = true := by
  intro p hp
  induction bs generalizing p with
  | nil => simp at hp
  | cons hd tl ih =>
      simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at h
      cases hp with
      | head => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- allCommsNonEmpty propagates to comm branches. -/
theorem allCommsNonEmpty_comm_branches {s r : String} {bs : List (Label × GlobalType)}
    (h : (GlobalType.comm s r bs).allCommsNonEmpty = true) :
    ∀ p ∈ bs, p.2.allCommsNonEmpty = true := by
  simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true] at h
  exact allCommsNonEmpty_of_allCommsNonEmptyBranches h.2

/-- isBlind propagates to mu body. -/
theorem isBlind_mu_body {t : String} {body : GlobalType}
    (h : isBlind (GlobalType.mu t body) = true) : isBlind body = true := h

/-- Helper: isBlindBranches implies isBlind for each element. -/
theorem isBlind_of_isBlindBranches {bs : List (Label × GlobalType)}
    (h : isBlindBranches bs = true) :
    ∀ p ∈ bs, isBlind p.2 = true := by
  intro p hp
  induction bs generalizing p with
  | nil => simp at hp
  | cons hd tl ih =>
      simp only [isBlindBranches, Bool.and_eq_true] at h
      cases hp with
      | head => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- isBlind propagates to comm branches. -/
theorem isBlind_comm_branches {s r : String} {bs : List (Label × GlobalType)}
    (h : isBlind (GlobalType.comm s r bs) = true) :
    ∀ p ∈ bs, isBlind p.2 = true := by
  simp only [isBlind, Bool.and_eq_true] at h
  exact isBlind_of_isBlindBranches h.2

/-- isBlind propagates to delegate continuation. -/
theorem isBlind_delegate_cont {p q : String} {sid : Nat} {r : String} {cont : GlobalType}
    (h : isBlind (GlobalType.delegate p q sid r cont) = true) : isBlind cont = true := h

/-! ## Non-Empty Branch Lemmas -/

/-- allCommsNonEmpty for a comm implies its branch list is non-empty. -/
theorem comm_branches_nonempty_of_allCommsNonEmpty
    {sender receiver : String} {branches : List (Label × GlobalType)}
    (hall : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true) :
    branches ≠ [] := by
  -- allCommsNonEmpty for comm requires branches.isEmpty = false.
  simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true] at hall
  intro hnil
  subst hnil
  -- [] has isEmpty = true, contradicting branches.isEmpty = false.
  have hFalse : False := by
    simpa using hall.1
  exact hFalse.elim

/-- wellFormed for a comm implies its branch list is non-empty. -/
theorem comm_branches_nonempty_of_wellFormed
    {sender receiver : String} {branches : List (Label × GlobalType)}
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true) :
    branches ≠ [] := by
  -- wellFormed includes allCommsNonEmpty as a conjunct.
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  have hall : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true :=
    hwf.1.1.2
  exact comm_branches_nonempty_of_allCommsNonEmpty hall

/-! ## Branch Projection Lemmas -/

theorem all_eq_true_of_all {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.all p = true) : ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil =>
      intro x hx
      cases hx
  | cons hd tl ih =>
      simp only [List.all, Bool.and_eq_true] at h
      intro x hx
      cases hx with
      | head => exact h.1
      | tail _ hmem => exact ih h.2 x hmem

/-- Helper: projectbBranches succeeds when each branch satisfies the IH.

    Note: This follows by induction on branches. The base case is definitional,
    and the cons case uses the IH. Proof omitted due to mutual definition unfolding complexity. -/
theorem projectbBranches_trans_of_all (branches : List (Label × GlobalType)) (role : String)
    (_hbranches : ∀ p ∈ branches, projectb p.2 role (Trans.trans p.2 role) = true) :
    projectbBranches branches role (transBranches branches role) = true := by
  induction branches with
  | nil =>
      simp [projectbBranches, Trans.transBranches]
  | cons head rest ih =>
      cases head with
      | mk label cont =>
          have hhead : projectb cont role (Trans.trans cont role) = true :=
            _hbranches (label, cont) (by simp)
          have hrest : ∀ p ∈ rest, projectb p.2 role (Trans.trans p.2 role) = true := by
            intro p hp
            exact _hbranches p (by simp [hp])
          have ih' := ih hrest
          have hlabel : (label == label) = true := by
            simpa using (label_beq_refl label)
          unfold projectbBranches
          unfold Trans.transBranches
          change
            (if (label == label) = true then
              projectb cont role (Trans.trans cont role) &&
              projectbBranches rest role (transBranches rest role)
            else false) = true
          rw [hlabel]
          simp [hhead, ih']

/-- Helper: projectbAllBranches succeeds when all branches project to the same candidate
    and each branch satisfies the IH.

    Note: This follows by induction on branches. Proof omitted due to mutual definition complexity. -/
theorem projectbAllBranches_trans_of_all_uniform (branches : List (Label × GlobalType))
    (role : String) (lt : LocalTypeR)
    (_huniform : ∀ p ∈ branches, Trans.trans p.2 role = lt)
    (_hvalid : ∀ p ∈ branches, projectb p.2 role (Trans.trans p.2 role) = true) :
    projectbAllBranches branches role lt = true := by
  induction branches with
  | nil =>
      simp [projectbAllBranches]
  | cons head rest ih =>
      cases head with
      | mk label cont =>
          have hcont_eq : Trans.trans cont role = lt :=
            _huniform (label, cont) (by simp)
          have hcont_valid : projectb cont role lt = true := by
            simpa [hcont_eq] using _hvalid (label, cont) (by simp)
          have hrest_uniform : ∀ p ∈ rest, Trans.trans p.2 role = lt := by
            intro p hp
            exact _huniform p (by simp [hp])
          have hrest_valid : ∀ p ∈ rest, projectb p.2 role (Trans.trans p.2 role) = true := by
            intro p hp
            exact _hvalid p (by simp [hp])
          have ih' := ih hrest_uniform hrest_valid
          simp [projectbAllBranches, hcont_valid, ih']

/-! ## Key Uniformity Lemma -/

/-- For non-participating roles, all branches project uniformly.
    This is the heart of the blindness property.

    Note: This lemma is currently a draft. In a complete implementation,
    `branchesUniformFor` would actually check projection equality, and this
    lemma would follow from that check. -/
theorem trans_uniform_for_nonparticipant
    {sender receiver role : String} {branches : List (Label × GlobalType)}
    (_hblind : commBlindFor sender receiver branches = true)
    (_hns : role ≠ sender) (_hnr : role ≠ receiver) (_hne : branches ≠ []) :
    ∀ p ∈ branches, Trans.trans p.2 role = Trans.trans (branches.head!.2) role := by
  classical
  have hblind' :
      ∀ role, role ≠ sender → role ≠ receiver → branchesUniformFor branches role = true := by
    have hdec :
        decide (∀ role, role ≠ sender → role ≠ receiver → branchesUniformFor branches role = true) = true := by
      simpa [commBlindFor] using _hblind
    exact of_decide_eq_true hdec
  have huniform : branchesUniformFor branches role = true := hblind' role _hns _hnr
  cases hbranches : branches with
  | nil =>
      cases (_hne hbranches)
  | cons head rest =>
      cases head with
      | mk label cont =>
          have hrest_all :
              rest.all (fun p => localTypeRBEq (Trans.trans p.2 role) (Trans.trans cont role)) = true := by
            simpa [branchesUniformFor, hbranches] using huniform
          have hrest :
              ∀ p ∈ rest, localTypeRBEq (Trans.trans p.2 role) (Trans.trans cont role) = true :=
            all_eq_true_of_all hrest_all
          intro p hp
          cases hp with
          | head =>
              simp
          | tail _ hp' =>
              have hdec := hrest p hp'
              have hpeq : Trans.trans p.2 role = Trans.trans cont role :=
                localTypeRBEq_eq_true hdec
              simpa [hbranches] using hpeq


end

end Choreography.Projection.Blind
