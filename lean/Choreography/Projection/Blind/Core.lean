import Choreography.Projection.Trans.Core
import Choreography.Projection.Projectb
import Choreography.Projection.ProjSubst

/-! # Choreography.Projection.Blind

Blindness predicate for V2 projection. -/

/-
The Problem. Define a "blindness" predicate that captures when non-participants
see the same projection in all branches of a choice. This bridges the gap between
structural well-formedness and projectability.

Solution Structure. The key theorem `projectable_of_wellFormedBlind` shows that
if a global type is: (1) closed, (2) well-formed, and (3) blind, then it is
projectable. The proof proceeds by:
1. Defining `isBlind` as a decidable predicate on global types
2. Proving uniformity: blindness implies all branches project identically for non-participants
3. Case analysis on comm constructors to build CProject witnesses
-/

namespace Choreography.Projection.Blind

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb

/-! ## Blindness Predicate -/

section
open Classical

/-! ### Local-Type Equality Checker -/

mutual
  /-- Boolean equality for recursive local types. -/
  def localTypeRBEq : LocalTypeR → LocalTypeR → Bool
    | .end, .end => true
    | .var t₁, .var t₂ => decide (t₁ = t₂)
    | .mu t₁ b₁, .mu t₂ b₂ => decide (t₁ = t₂) && localTypeRBEq b₁ b₂
    | .send r₁ bs₁, .send r₂ bs₂ => decide (r₁ = r₂) && branchRListBEq bs₁ bs₂
    | .recv r₁ bs₁, .recv r₂ bs₂ => decide (r₁ = r₂) && branchRListBEq bs₁ bs₂
    | _, _ => false

  /-- Boolean equality for branch lists. -/
  def branchRListBEq : List BranchR → List BranchR → Bool
    | [], [] => true
    | (l₁, t₁, c₁) :: xs, (l₂, t₂, c₂) :: ys =>
        decide (l₁ = l₂) && decide (t₁ = t₂) && localTypeRBEq c₁ c₂ && branchRListBEq xs ys
    | _, _ => false
end

mutual
  /-- Reflexivity of the local-type equality checker. -/
  theorem localTypeRBEq_refl : ∀ x : LocalTypeR, localTypeRBEq x x = true
    | .end => rfl
    | .var _ => by simp [localTypeRBEq]
    | .mu _ body => by simp [localTypeRBEq, localTypeRBEq_refl body]
    | .send _ bs => by simp [localTypeRBEq, branchRListBEq_refl bs]
    | .recv _ bs => by simp [localTypeRBEq, branchRListBEq_refl bs]

  /-- Reflexivity of branch-list checker. -/
  private theorem branchRListBEq_refl : ∀ xs : List BranchR, branchRListBEq xs xs = true
    | [] => rfl
    | (l, t, c) :: xs => by
        simp [branchRListBEq, localTypeRBEq_refl c, branchRListBEq_refl xs]
end

mutual
  /-- Soundness: local type equality checker returning `true` implies equality. -/
  theorem localTypeRBEq_eq_true :
      ∀ {x y : LocalTypeR}, localTypeRBEq x y = true → x = y
    | .end, .end, _ => rfl
    | .var t₁, .var t₂, h => by
        simpa [localTypeRBEq] using (of_decide_eq_true h)
    | .mu t₁ b₁, .mu t₂ b₂, h => by
        simp only [localTypeRBEq, Bool.and_eq_true] at h
        have ht : t₁ = t₂ := of_decide_eq_true h.1
        have hb : b₁ = b₂ := localTypeRBEq_eq_true h.2
        subst ht hb
        rfl
    | .send r₁ bs₁, .send r₂ bs₂, h => by
        simp only [localTypeRBEq, Bool.and_eq_true] at h
        have hr : r₁ = r₂ := of_decide_eq_true h.1
        have hbs : bs₁ = bs₂ := branchRListBEq_eq_true h.2
        subst hr hbs
        rfl
    | .recv r₁ bs₁, .recv r₂ bs₂, h => by
        simp only [localTypeRBEq, Bool.and_eq_true] at h
        have hr : r₁ = r₂ := of_decide_eq_true h.1
        have hbs : bs₁ = bs₂ := branchRListBEq_eq_true h.2
        subst hr hbs
        rfl
    | .end, .var _, h => by cases h
    | .end, .mu _ _, h => by cases h
    | .end, .send _ _, h => by cases h
    | .end, .recv _ _, h => by cases h
    | .var _, .end, h => by cases h
    | .var _, .mu _ _, h => by cases h
    | .var _, .send _ _, h => by cases h
    | .var _, .recv _ _, h => by cases h
    | .mu _ _, .end, h => by cases h
    | .mu _ _, .var _, h => by cases h
    | .mu _ _, .send _ _, h => by cases h
    | .mu _ _, .recv _ _, h => by cases h
    | .send _ _, .end, h => by cases h
    | .send _ _, .var _, h => by cases h
    | .send _ _, .mu _ _, h => by cases h
    | .send _ _, .recv _ _, h => by cases h
    | .recv _ _, .end, h => by cases h
    | .recv _ _, .var _, h => by cases h
    | .recv _ _, .mu _ _, h => by cases h
    | .recv _ _, .send _ _, h => by cases h

  /-- Soundness: branch-list checker returning `true` implies equality. -/
  private theorem branchRListBEq_eq_true :
      ∀ {xs ys : List BranchR}, branchRListBEq xs ys = true → xs = ys
    | [], [], _ => rfl
    | (l₁, t₁, c₁) :: xs, (l₂, t₂, c₂) :: ys, h => by
        simp only [branchRListBEq, Bool.and_eq_true] at h
        rcases h with ⟨⟨⟨hl', ht'⟩, hc⟩, hrestBool⟩
        have hlEq : l₁ = l₂ := of_decide_eq_true hl'
        have htEq : t₁ = t₂ := of_decide_eq_true ht'
        have hc' : c₁ = c₂ := localTypeRBEq_eq_true hc
        have hrest' : xs = ys := branchRListBEq_eq_true hrestBool
        subst hlEq htEq hc' hrest'
        rfl
    | [], _ :: _, h => by cases h
    | _ :: _, [], h => by cases h
end

theorem localTypeRBEq_eq_true_iff (x y : LocalTypeR) :
    localTypeRBEq x y = true ↔ x = y := by
  constructor
  · exact localTypeRBEq_eq_true
  · intro h
    subst h
    exact localTypeRBEq_refl x

/-! ### Branch Role Collection -/

mutual
  /-- Raw role mentions (without deduplication) used by projection branching. -/
  private def roleMentions : GlobalType → List String
    | .end => []
    | .var _ => []
    | .mu _ body => roleMentions body
    | .comm sender receiver branches => sender :: receiver :: rolesFromBranches branches
    | .delegate p q _ _ cont => p :: q :: roleMentions cont

  /-- Collect role mentions from branch continuations. -/
  def rolesFromBranches : List (Label × GlobalType) → List String
    | [] => []
    | (_, cont) :: rest => roleMentions cont ++ rolesFromBranches rest
end

/-! ### Uniformity Predicate (Computable) -/

/-- Check if all branches project identically for a given role. -/
def branchesUniformFor (branches : List (Label × GlobalType)) (role : String) : Bool :=
  match branches with
  | [] => true
  | (_, cont) :: rest =>
      let lt := Trans.trans cont role
      rest.all fun p => localTypeRBEq (Trans.trans p.2 role) lt

/-! ### Finite Decision Procedure for `commBlindFor` -/

/-- Max role-name length in a finite list. -/
private def maxRoleLen : List String → Nat
  | [] => 0
  | s :: rest => max s.length (maxRoleLen rest)

/-- Generate a role name not present in the given finite list. -/
private def freshRole (taken : List String) : String :=
  String.ofList (List.replicate (maxRoleLen taken + 1) 'a')

private theorem role_len_le_maxRoleLen {taken : List String} {r : String}
    (hmem : r ∈ taken) : r.length ≤ maxRoleLen taken := by
  induction taken with
  | nil => cases hmem
  | cons hd tl ih =>
      simp only [maxRoleLen] at *
      cases hmem with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ htl =>
          exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

private theorem freshRole_not_mem (taken : List String) : freshRole taken ∉ taken := by
  intro hmem
  have hlen_le : (freshRole taken).length ≤ maxRoleLen taken := role_len_le_maxRoleLen hmem
  have hlen_fresh : (freshRole taken).length = maxRoleLen taken + 1 := by
    simp [freshRole, String.length_ofList, List.length_replicate]
  omega

private theorem roleMentions_notin_implies_trans_eq
    (g : GlobalType) (role₁ role₂ : String)
    (h₁ : role₁ ∉ roleMentions g) (h₂ : role₂ ∉ roleMentions g) :
    Trans.trans g role₁ = Trans.trans g role₂ := by
  match g with
  | .end =>
      simp [Trans.trans]
  | .var _ =>
      simp [Trans.trans]
  | .mu _ body =>
      have h₁_body : role₁ ∉ roleMentions body := by
        simpa [roleMentions] using h₁
      have h₂_body : role₂ ∉ roleMentions body := by
        simpa [roleMentions] using h₂
      have hbody := roleMentions_notin_implies_trans_eq body role₁ role₂ h₁_body h₂_body
      simp [Trans.trans, hbody]
  | .comm sender receiver branches =>
      have hs₁ : role₁ ≠ sender := by
        intro heq
        exact h₁ (by simp [roleMentions, heq])
      have hr₁ : role₁ ≠ receiver := by
        intro heq
        exact h₁ (by simp [roleMentions, heq])
      have hs₂ : role₂ ≠ sender := by
        intro heq
        exact h₂ (by simp [roleMentions, heq])
      have hr₂ : role₂ ≠ receiver := by
        intro heq
        exact h₂ (by simp [roleMentions, heq])
      cases branches with
      | nil =>
          simp [Trans.trans, beq_false_of_ne hs₁, beq_false_of_ne hr₁,
            beq_false_of_ne hs₂, beq_false_of_ne hr₂]
      | cons head rest =>
          cases head with
          | mk label cont =>
              have h₁_cont : role₁ ∉ roleMentions cont := by
                intro hmem
                exact h₁ (by simp [roleMentions, rolesFromBranches, hmem])
              have h₂_cont : role₂ ∉ roleMentions cont := by
                intro hmem
                exact h₂ (by simp [roleMentions, rolesFromBranches, hmem])
              have hcont := roleMentions_notin_implies_trans_eq cont role₁ role₂ h₁_cont h₂_cont
              simp [Trans.trans, beq_false_of_ne hs₁, beq_false_of_ne hr₁,
                beq_false_of_ne hs₂, beq_false_of_ne hr₂, hcont]
  | .delegate p q _ _ cont =>
      have hp₁ : role₁ ≠ p := by
        intro heq
        exact h₁ (by simp [roleMentions, heq])
      have hq₁ : role₁ ≠ q := by
        intro heq
        exact h₁ (by simp [roleMentions, heq])
      have hp₂ : role₂ ≠ p := by
        intro heq
        exact h₂ (by simp [roleMentions, heq])
      have hq₂ : role₂ ≠ q := by
        intro heq
        exact h₂ (by simp [roleMentions, heq])
      have h₁_cont : role₁ ∉ roleMentions cont := by
        intro hmem
        exact h₁ (by simp [roleMentions, hmem])
      have h₂_cont : role₂ ∉ roleMentions cont := by
        intro hmem
        exact h₂ (by simp [roleMentions, hmem])
      have hcont := roleMentions_notin_implies_trans_eq cont role₁ role₂ h₁_cont h₂_cont
      simp [Trans.trans, beq_false_of_ne hp₁, beq_false_of_ne hq₁,
        beq_false_of_ne hp₂, beq_false_of_ne hq₂, hcont]
termination_by sizeOf g
decreasing_by
  all_goals
    first
    | (subst_vars; exact sizeOf_body_lt_mu _ _)
    | (subst_vars; simp only [sizeOf, GlobalType._sizeOf_1]; omega)

private theorem branchesUniformTail_notin_eq
    (rest : List (Label × GlobalType)) (cont : GlobalType) (role₁ role₂ : String)
    (hcont_eq : Trans.trans cont role₁ = Trans.trans cont role₂)
    (h₁ : role₁ ∉ rolesFromBranches rest)
    (h₂ : role₂ ∉ rolesFromBranches rest) :
    rest.all (fun p => localTypeRBEq (Trans.trans p.2 role₁) (Trans.trans cont role₁)) =
      rest.all (fun p => localTypeRBEq (Trans.trans p.2 role₂) (Trans.trans cont role₂)) := by
  induction rest with
  | nil =>
      rfl
  | cons hd tl ih =>
      cases hd with
      | mk l g =>
          have h₁_g : role₁ ∉ roleMentions g := by
            intro hmem
            exact h₁ (by simp [rolesFromBranches, hmem])
          have h₂_g : role₂ ∉ roleMentions g := by
            intro hmem
            exact h₂ (by simp [rolesFromBranches, hmem])
          have hg_eq :
              Trans.trans g role₁ = Trans.trans g role₂ :=
            roleMentions_notin_implies_trans_eq g role₁ role₂ h₁_g h₂_g
          have h₁_tl : role₁ ∉ rolesFromBranches tl := by
            intro hmem
            exact h₁ (by simp [rolesFromBranches, hmem])
          have h₂_tl : role₂ ∉ rolesFromBranches tl := by
            intro hmem
            exact h₂ (by simp [rolesFromBranches, hmem])
          have hprop :
              (Trans.trans g role₁ = Trans.trans cont role₁) ↔
                (Trans.trans g role₂ = Trans.trans cont role₂) := by
            constructor <;> intro hEq
            · simpa [hg_eq, hcont_eq] using hEq
            · simpa [hg_eq, hcont_eq] using hEq
          have hdec :
              localTypeRBEq (Trans.trans g role₁) (Trans.trans cont role₁) =
                localTypeRBEq (Trans.trans g role₂) (Trans.trans cont role₂) := by
            cases hL : localTypeRBEq (Trans.trans g role₁) (Trans.trans cont role₁) <;>
              cases hR : localTypeRBEq (Trans.trans g role₂) (Trans.trans cont role₂) <;>
              try rfl
            · exfalso
              have hEqR : Trans.trans g role₂ = Trans.trans cont role₂ :=
                (localTypeRBEq_eq_true_iff _ _).1 hR
              have hEqL : Trans.trans g role₁ = Trans.trans cont role₁ := hprop.mpr hEqR
              have hLtrue : localTypeRBEq (Trans.trans g role₁) (Trans.trans cont role₁) = true :=
                (localTypeRBEq_eq_true_iff _ _).2 hEqL
              simp [hL] at hLtrue
            · exfalso
              have hEqL : Trans.trans g role₁ = Trans.trans cont role₁ :=
                (localTypeRBEq_eq_true_iff _ _).1 hL
              have hEqR : Trans.trans g role₂ = Trans.trans cont role₂ := hprop.mp hEqL
              have hRtrue : localTypeRBEq (Trans.trans g role₂) (Trans.trans cont role₂) = true :=
                (localTypeRBEq_eq_true_iff _ _).2 hEqR
              simp [hR] at hRtrue
          simp [hdec, ih h₁_tl h₂_tl]

private theorem branchesUniformFor_notin_eq
    (branches : List (Label × GlobalType)) (role₁ role₂ : String)
    (h₁ : role₁ ∉ rolesFromBranches branches)
    (h₂ : role₂ ∉ rolesFromBranches branches) :
    branchesUniformFor branches role₁ = branchesUniformFor branches role₂ := by
  match branches with
  | [] =>
      simp [branchesUniformFor]
  | (label, cont) :: rest =>
      have h₁_cont : role₁ ∉ roleMentions cont := by
        intro hmem
        exact h₁ (by simp [rolesFromBranches, hmem])
      have h₂_cont : role₂ ∉ roleMentions cont := by
        intro hmem
        exact h₂ (by simp [rolesFromBranches, hmem])
      have hcont_eq :
          Trans.trans cont role₁ = Trans.trans cont role₂ :=
        roleMentions_notin_implies_trans_eq cont role₁ role₂ h₁_cont h₂_cont
      have h₁_rest : role₁ ∉ rolesFromBranches rest := by
        intro hmem
        exact h₁ (by simp [rolesFromBranches, hmem])
      have h₂_rest : role₂ ∉ rolesFromBranches rest := by
        intro hmem
        exact h₂ (by simp [rolesFromBranches, hmem])
      unfold branchesUniformFor
      simpa using
        branchesUniformTail_notin_eq rest cont role₁ role₂ hcont_eq h₁_rest h₂_rest

/-- Finite checker for comm blindness over syntactically relevant roles. -/
private def commBlindForCheck (sender receiver : String)
    (branches : List (Label × GlobalType)) : Bool :=
  let witnesses := sender :: receiver :: rolesFromBranches branches
  let outsider := freshRole witnesses
  let witnessCheck := witnesses.all fun role =>
    if role == sender || role == receiver then true else branchesUniformFor branches role
  witnessCheck && branchesUniformFor branches outsider

private theorem list_all_true_of_all_eq_true {α : Type} {p : α → Bool} {xs : List α}
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

private theorem commBlindForCheck_implies_uniform
    {sender receiver : String} {branches : List (Label × GlobalType)}
    (hcheck : commBlindForCheck sender receiver branches = true) :
    ∀ role, role ≠ sender → role ≠ receiver → branchesUniformFor branches role = true := by
  intro role hns hnr
  unfold commBlindForCheck at hcheck
  simp only [Bool.and_eq_true] at hcheck
  set witnesses := sender :: receiver :: rolesFromBranches branches with hw
  set outsider := freshRole witnesses with ho
  have hWitness : witnesses.all
      (fun role =>
        if role == sender || role == receiver then true
        else branchesUniformFor branches role) = true := by
    simpa [hw, ho] using hcheck.1
  have hOut : branchesUniformFor branches outsider = true := by
    simpa [hw, ho] using hcheck.2
  by_cases hmem : role ∈ witnesses
  · have hRole :
        (if role == sender || role == receiver then true
         else branchesUniformFor branches role) = true :=
      list_all_true_of_all_eq_true hWitness role hmem
    have hFalse : (role == sender || role == receiver) = false := by
      simp [beq_false_of_ne hns, beq_false_of_ne hnr]
    simpa [hFalse] using hRole
  · have hRoleBranches : role ∉ rolesFromBranches branches := by
      intro hm
      exact hmem (by simp [hw, hm])
    have hOutWitness : outsider ∉ witnesses := by
      have hFresh : freshRole witnesses ∉ witnesses := freshRole_not_mem witnesses
      simpa [ho] using hFresh
    have hOutBranches : outsider ∉ rolesFromBranches branches := by
      intro hm
      exact hOutWitness (by simp [hw, hm])
    have hEq :
        branchesUniformFor branches role = branchesUniformFor branches outsider :=
      branchesUniformFor_notin_eq branches role outsider hRoleBranches hOutBranches
    simpa [hEq] using hOut

private theorem commBlindForCheck_of_uniform
    {sender receiver : String} {branches : List (Label × GlobalType)}
    (huniform : ∀ role, role ≠ sender → role ≠ receiver →
      branchesUniformFor branches role = true) :
    commBlindForCheck sender receiver branches = true := by
  unfold commBlindForCheck
  set witnesses := sender :: receiver :: rolesFromBranches branches with hw
  set outsider := freshRole witnesses with ho
  have hWitness :
      witnesses.all
        (fun role =>
          if role == sender || role == receiver then true
          else branchesUniformFor branches role) = true := by
    refine List.all_eq_true.2 ?_
    intro role hmem
    by_cases hs : role = sender
    · simp [hs]
    · by_cases hr : role = receiver
      · simp [hr]
      · simp [hs, hr, huniform role hs hr]
  have hOutNeSender : outsider ≠ sender := by
    intro hEq
    have hOutWitness : outsider ∉ witnesses := by
      have hFresh : freshRole witnesses ∉ witnesses := freshRole_not_mem witnesses
      simpa [ho] using hFresh
    exact hOutWitness (by simp [hw, hEq])
  have hOutNeReceiver : outsider ≠ receiver := by
    intro hEq
    have hOutWitness : outsider ∉ witnesses := by
      have hFresh : freshRole witnesses ∉ witnesses := freshRole_not_mem witnesses
      simpa [ho] using hFresh
    exact hOutWitness (by simp [hw, hEq])
  have hOut : branchesUniformFor branches outsider = true :=
    huniform outsider hOutNeSender hOutNeReceiver
  exact by
    simpa [Bool.and_eq_true] using
      (And.intro hWitness (by simpa [hw, ho] using hOut))

private instance commBlindForPropDecidable
    (sender receiver : String) (branches : List (Label × GlobalType)) :
    Decidable (∀ role, role ≠ sender → role ≠ receiver →
      branchesUniformFor branches role = true) :=
  decidable_of_iff
    (commBlindForCheck sender receiver branches = true)
    ⟨commBlindForCheck_implies_uniform, commBlindForCheck_of_uniform⟩

/-- Check blindness for a communication: non-participants see same projection. -/
def commBlindFor (sender receiver : String) (branches : List (Label × GlobalType)) : Bool :=
  decide (∀ role, role ≠ sender → role ≠ receiver → branchesUniformFor branches role = true)

mutual
  /-- A global type is blind if non-participants see the same projection
      in all branches of every communication. -/
  def isBlind : GlobalType → Bool
    | .end => true
    | .var _ => true
    | .mu _ body => isBlind body
    | .comm sender receiver branches =>
        commBlindFor sender receiver branches && isBlindBranches branches
    | .delegate _ _ _ _ cont => isBlind cont

  /-- Helper for checking blindness in branches. -/
  def isBlindBranches : List (Label × GlobalType) → Bool
    | [] => true
    | (_, cont) :: rest => isBlind cont && isBlindBranches rest
end

/-! ## Combined Well-Formedness Predicate -/

/-- Well-formed and blind: the full predicate needed for projectability. -/
def WellFormedBlind (g : GlobalType) : Bool :=
  g.isClosed && g.wellFormed && isBlind g

/-! ## Propagation Lemmas -/

private theorem payload_beq_refl (p : PayloadSort) : (p == p) = true := by
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

private theorem label_beq_refl (lbl : Label) : (lbl == lbl) = true := by
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
private theorem noSelfComm_of_noSelfCommBranches {bs : List (Label × GlobalType)}
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
private theorem allCommsNonEmpty_of_allCommsNonEmptyBranches {bs : List (Label × GlobalType)}
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
private theorem isBlind_of_isBlindBranches {bs : List (Label × GlobalType)}
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

private theorem all_eq_true_of_all {α : Type} {p : α → Bool} {xs : List α}
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

/-! ## Main Theorem -/

/-- Core lemma: projectb succeeds on trans output when noSelfComm and isBlind hold.

    This is the heart of the proof - we only need noSelfComm (for comm cases)
    and isBlind (for non-participant uniformity). We don't need isClosed or
    the full wellFormed predicate. -/
theorem projectb_trans_of_noSelfComm_blind (g : GlobalType) (role : String)
    (hnoself : g.noSelfComm = true)
    (hblind : isBlind g = true) :
    projectb g role (Trans.trans g role) = true := by
  match g with
  | .end =>
      -- end case: trivial
      simp only [Trans.trans, projectb]
  | .var t =>
      -- var case: projectb matches var with var (always true)
      simp only [Trans.trans, projectb, beq_self_eq_true]
  | .mu t body =>
      -- mu case: recurse on body
      unfold Trans.trans
      have hnoself' := noSelfComm_mu_body hnoself
      have hblind' := isBlind_mu_body hblind
      by_cases hguard : (Trans.trans body role).isGuarded t
      · -- Guarded: mu preserved
        simp only [hguard, ↓reduceIte, projectb, beq_self_eq_true]
        exact projectb_trans_of_noSelfComm_blind body role hnoself' hblind'
      · -- Unguarded: collapses to end
        simp only [hguard, Bool.false_eq_true, ↓reduceIte, projectb]
        exact projectb_trans_of_noSelfComm_blind body role hnoself' hblind'
  | .comm sender receiver branches =>
      -- comm case: split on role participation
      -- Extract sender ≠ receiver from noSelfComm
      have hne_sr : sender ≠ receiver := by
        -- noSelfComm for comm = (sender != receiver) && noSelfCommBranches
        have hnoself' := hnoself
        simp only [GlobalType.noSelfComm, Bool.and_eq_true, bne_iff_ne, ne_eq] at hnoself'
        exact hnoself'.1
      -- Note: We have noSelfComm and isBlind for branches, which would allow
      -- recursive calls via hnoself_branches := noSelfComm_comm_branches hnoself
      -- and hblind_branches := isBlind_comm_branches hblind
      have hnoself_branches : ∀ p ∈ branches, p.2.noSelfComm = true :=
        noSelfComm_comm_branches (s := sender) (r := receiver) (bs := branches) hnoself
      have hblind_branches : ∀ p ∈ branches, isBlind p.2 = true :=
        isBlind_comm_branches (s := sender) (r := receiver) (bs := branches) hblind
      have hblind_comm : commBlindFor sender receiver branches = true := by
        have hblind' := hblind
        simp [isBlind, Bool.and_eq_true] at hblind'
        exact hblind'.1
      have hbranches_proj :
          ∀ p ∈ branches, projectb p.2 role (Trans.trans p.2 role) = true := by
        intro p hp
        exact projectb_trans_of_noSelfComm_blind p.2 role (hnoself_branches p hp) (hblind_branches p hp)
      by_cases hs : role = sender
      · -- Sender case: role = sender
        -- The result is .send receiver (transBranches branches role)
        -- projectb checks that projectbBranches matches
        have hproj_branches :=
          projectbBranches_trans_of_all branches role hbranches_proj
        have hproj_branches' :
            projectbBranches branches sender (transBranches branches sender) = true := by
          simpa [hs] using hproj_branches
        have htrans' :
            Trans.trans (GlobalType.comm sender receiver branches) sender =
              .send receiver (transBranches branches sender) := by
          simpa using trans_comm_sender sender receiver sender branches rfl
        simp [hs, htrans', projectb, hproj_branches']
      · by_cases hr : role = receiver
        · -- Receiver case: role = receiver
          -- The result is .recv sender (transBranches branches role)
          -- projectb checks that projectbBranches matches
          have hproj_branches :=
            projectbBranches_trans_of_all branches role hbranches_proj
          have hproj_branches' :
              projectbBranches branches receiver (transBranches branches receiver) = true := by
            simpa [hr] using hproj_branches
          have hns : receiver ≠ sender := Ne.symm hne_sr
          have htrans' :
              Trans.trans (GlobalType.comm sender receiver branches) receiver =
                .recv sender (transBranches branches receiver) := by
            simpa using trans_comm_receiver sender receiver receiver branches rfl hns
          simp [hr, hns, htrans', projectb, hproj_branches']
        · -- Non-participant case: role ≠ sender, role ≠ receiver
          -- The result is trans of the first branch continuation
          -- All branches must project uniformly (from blindness)
          cases hbranches : branches with
          | nil =>
              simp [projectbAllBranches, projectb, Trans.trans, hs, hr]
          | cons head rest =>
              cases head with
              | mk label cont =>
                  have hne : (label, cont) :: rest ≠ [] := by simp
                  have hblind_comm' :
                      commBlindFor sender receiver ((label, cont) :: rest) = true := by
                    simpa [hbranches] using hblind_comm
                  have huniform :
                      ∀ p ∈ ((label, cont) :: rest),
                        Trans.trans p.2 role = Trans.trans cont role := by
                    have huniform' :=
                      trans_uniform_for_nonparticipant (sender := sender) (receiver := receiver)
                        (role := role) (branches := (label, cont) :: rest) hblind_comm' hs hr hne
                    intro p hp
                    have h := huniform' p hp
                    simpa using h
                  have hproj_all :=
                    projectbAllBranches_trans_of_all_uniform ((label, cont) :: rest) role
                      (Trans.trans cont role) huniform (by
                        intro p hp
                        exact hbranches_proj p (by simpa [hbranches] using hp))
                  have hbs : (role == sender) = false := by
                    simpa using (beq_false_of_ne hs)
                  have hbr : (role == receiver) = false := by
                    simpa using (beq_false_of_ne hr)
                  have htrans_comm :
                      Trans.trans (GlobalType.comm sender receiver ((label, cont) :: rest)) role =
                        Trans.trans cont role := by
                    simp [Trans.trans, hbs, hbr]
                  have hproj_all' :
                      projectbAllBranches ((label, cont) :: rest) role
                        (Trans.trans (GlobalType.comm sender receiver ((label, cont) :: rest)) role) = true := by
                    simpa [htrans_comm] using hproj_all
                  unfold projectb
                  simp [hbs, hbr]
                  exact hproj_all'
  | .delegate p q sid r cont =>
      -- Delegate case: split on role participation
      -- Extract noSelfComm and isBlind for continuation
      have hnoself_cont : cont.noSelfComm = true := noSelfComm_delegate_cont hnoself
      have hblind_cont : isBlind cont = true := hblind  -- isBlind delegates to continuation
      have hcont_proj := projectb_trans_of_noSelfComm_blind cont role hnoself_cont hblind_cont
      by_cases hp : role = p
      · -- Delegator case: role = p
        -- trans gives .send q [(_delegate, some (.chan sid r), trans cont role)]
        -- projectb matches this exact shape
        have htrans : Trans.trans (GlobalType.delegate p q sid r cont) p =
            .send q [(⟨"_delegate", .unit⟩, some (.chan sid r), Trans.trans cont p)] := by
          -- Compute the candidate projection for the delegator.
          simp [Trans.trans]
        have hcont_proj' : projectb cont p (Trans.trans cont p) = true := by
          -- Specialize the IH to the delegator role.
          simpa [hp] using hcont_proj
        -- Reduce projectb to the continuation goal.
        calc
          projectb (GlobalType.delegate p q sid r cont) role
              (Trans.trans (GlobalType.delegate p q sid r cont) role)
              = projectb (GlobalType.delegate p q sid r cont) p
                  (Trans.trans (GlobalType.delegate p q sid r cont) p) := by
                    simp [hp]
          _ = projectb cont p (Trans.trans cont p) := by
                simp [projectb, htrans, reduceBEq]
          _ = true := hcont_proj'
      · by_cases hq : role = q
        · -- Delegatee case: role = q
          -- trans gives .recv p [(_delegate, some (.chan sid r), trans cont role)]
          -- projectb matches this exact shape
          have hqp : q ≠ p := by
            -- Non-participation on p follows from the outer case split.
            intro hqp
            apply hp
            simp [hq, hqp]
          have hpne : (q == p) = false := by
            simpa [beq_eq_false_iff_ne, ne_eq] using hqp
          have htrans : Trans.trans (GlobalType.delegate p q sid r cont) q =
              .recv p [(⟨"_delegate", .unit⟩, some (.chan sid r), Trans.trans cont q)] := by
            -- Compute the candidate projection for the delegatee.
            simp [Trans.trans, hpne]
          have hcont_proj' : projectb cont q (Trans.trans cont q) = true := by
            -- Specialize the IH to the delegatee role.
            simpa [hq] using hcont_proj
          have hrole_p' : (q == p) = false := by
            -- Convert role inequality into BEq for the delegatee.
            simpa [beq_eq_false_iff_ne, ne_eq] using hqp
          -- Reduce projectb to the continuation goal.
          calc
          projectb (GlobalType.delegate p q sid r cont) role
              (Trans.trans (GlobalType.delegate p q sid r cont) role)
              = projectb (GlobalType.delegate p q sid r cont) q
                  (Trans.trans (GlobalType.delegate p q sid r cont) q) := by
                      simp [hq]
          _ = projectb cont q (Trans.trans cont q) := by
                  simp [projectb, htrans, hrole_p', reduceBEq]
          _ = true := hcont_proj'
        · -- Non-participant case: role ≠ p, role ≠ q
          -- trans gives trans cont role, projectb does projectb cont role cand
          have hpne : (role == p) = false := by
            simpa [beq_eq_false_iff_ne, ne_eq] using hp
          have hqne : (role == q) = false := by
            simpa [beq_eq_false_iff_ne, ne_eq] using hq
          have htrans : Trans.trans (GlobalType.delegate p q sid r cont) role =
              Trans.trans cont role := by
            -- Compute the candidate projection for a non-participant.
            simp [Trans.trans, hpne, hqne]
          -- Reduce projectb to the continuation goal.
          calc
            projectb (GlobalType.delegate p q sid r cont) role
                (Trans.trans (GlobalType.delegate p q sid r cont) role)
                = projectb cont role (Trans.trans cont role) := by
                    -- Unfold only the LHS and pick the non-participant branch.
                    conv_lhs => unfold Choreography.Projection.Projectb.projectb
                    simp [hpne, hqne, htrans]
            _ = true := hcont_proj
termination_by g
decreasing_by
  all_goals
    first
    | exact sizeOf_body_lt_mu _ _
    | apply sizeOf_elem_snd_lt_comm; assumption
    | simp only [sizeOf, GlobalType._sizeOf_1]; omega

end

/-! ## wellFormed implies noSelfComm -/

/-- wellFormed implies noSelfComm. -/
theorem noSelfComm_of_wellFormed (g : GlobalType)
    (hwf : g.wellFormed = true) : g.noSelfComm = true := by
  -- wellFormed = allVarsBound && allCommsNonEmpty && noSelfComm && isProductive
  -- This is left-associative: ((allVarsBound && allCommsNonEmpty) && noSelfComm) && isProductive
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact hwf.1.2

/-! ## Final Theorems -/

/-- Wrapper: projectb succeeds on trans output for WellFormedBlind types. -/
theorem projectb_trans_of_wellFormedBlind (g : GlobalType) (role : String)
    (_hclosed : g.isClosed = true)
    (hwf : g.wellFormed = true)
    (hblind : isBlind g = true) :
    projectb g role (Trans.trans g role) = true :=
  projectb_trans_of_noSelfComm_blind g role (noSelfComm_of_wellFormed g hwf) hblind

/-- Projectable from WellFormedBlind: removes the extra postulate.

    If a global type is closed, well-formed, and blind, then it is projectable. -/
theorem projectable_of_wellFormedBlind (g : GlobalType)
    (h : WellFormedBlind g = true) :
    ∀ role, ∃ lt, CProject g role lt := by
  intro role
  -- WellFormedBlind g = g.isClosed && g.wellFormed && isBlind g
  simp only [WellFormedBlind, Bool.and_eq_true] at h
  -- h : (g.isClosed = true ∧ g.wellFormed = true) ∧ isBlind g = true
  have hclosed : g.isClosed = true := h.1.1
  have hwf : g.wellFormed = true := h.1.2
  have hblind : isBlind g = true := h.2
  use Trans.trans g role
  have hproj := projectb_trans_of_wellFormedBlind g role hclosed hwf hblind
  exact projectb_sound g role (Trans.trans g role) hproj

end Choreography.Projection.Blind
