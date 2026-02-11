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
def maxRoleLen : List String → Nat
  | [] => 0
  | s :: rest => max s.length (maxRoleLen rest)

/-- Generate a role name not present in the given finite list. -/
def freshRole (taken : List String) : String :=
  String.ofList (List.replicate (maxRoleLen taken + 1) 'a')

theorem role_len_le_maxRoleLen {taken : List String} {r : String}
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

theorem freshRole_not_mem (taken : List String) : freshRole taken ∉ taken := by
  intro hmem
  have hlen_le : (freshRole taken).length ≤ maxRoleLen taken := role_len_le_maxRoleLen hmem
  have hlen_fresh : (freshRole taken).length = maxRoleLen taken + 1 := by
    simp [freshRole, String.length_ofList, List.length_replicate]
  omega

theorem roleMentions_notin_implies_trans_eq
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

theorem branchesUniformTail_notin_eq
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

theorem branchesUniformFor_notin_eq
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
def commBlindForCheck (sender receiver : String)
    (branches : List (Label × GlobalType)) : Bool :=
  let witnesses := sender :: receiver :: rolesFromBranches branches
  let outsider := freshRole witnesses
  let witnessCheck := witnesses.all fun role =>
    if role == sender || role == receiver then true else branchesUniformFor branches role
  witnessCheck && branchesUniformFor branches outsider

theorem list_all_true_of_all_eq_true {α : Type} {p : α → Bool} {xs : List α}
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

theorem commBlindForCheck_implies_uniform
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

theorem commBlindForCheck_of_uniform
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


end

end Choreography.Projection.Blind
