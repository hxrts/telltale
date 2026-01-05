import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup

/-! # RumpsteakV2.Protocol.GlobalType

Global types for the V2 development.

## Expose

The following definitions form the semantic interface for proofs:

- `PayloadSort`: payload type annotations
- `Label`: message labels with payload sorts
- `GlobalType`: global protocol types
- `GlobalType.wellFormed`: well-formedness predicate
- `GlobalType.roles`: extract role names
- `GlobalType.freeVars`: extract free type variables
- `GlobalType.substitute`: type variable substitution
- `GlobalActionR`: global action with sender, receiver, label
- `canStep`: global enabledness predicate
- `BranchesStep`: branch-wise step relation
- `step`: global async step relation
-/

namespace RumpsteakV2.Protocol.GlobalType

/-- Payload sort types for message payloads. -/
inductive PayloadSort where
  | unit : PayloadSort
  | nat : PayloadSort
  | bool : PayloadSort
  | string : PayloadSort
  | prod : PayloadSort → PayloadSort → PayloadSort
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A message label with its payload sort. -/
structure Label where
  name : String
  sort : PayloadSort := PayloadSort.unit
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Global types describe protocols from the bird's-eye view. -/
inductive GlobalType where
  | end : GlobalType
  | comm : String → String → List (Label × GlobalType) → GlobalType
  | mu : String → GlobalType → GlobalType
  | var : String → GlobalType
  deriving Repr, Inhabited

/- Extract all role names from a global type. -/
mutual
  def GlobalType.roles : GlobalType → List String
    | .end => []
    | .comm sender receiver branches =>
        let branchRoles := rolesOfBranches branches
        ([sender, receiver] ++ branchRoles).eraseDups
    | .mu _ body => body.roles
    | .var _ => []

  def rolesOfBranches : List (Label × GlobalType) → List String
    | [] => []
    | (_, g) :: rest => g.roles ++ rolesOfBranches rest
end

/- Extract free type variables from a global type. -/
mutual
  def GlobalType.freeVars : GlobalType → List String
    | .end => []
    | .comm _ _ branches => freeVarsOfBranches branches
    | .mu t body => body.freeVars.filter (· != t)
    | .var t => [t]

  def freeVarsOfBranches : List (Label × GlobalType) → List String
    | [] => []
    | (_, g) :: rest => g.freeVars ++ freeVarsOfBranches rest
end

theorem freeVarsOfBranches_eq_flatMap (branches : List (Label × GlobalType)) :
    freeVarsOfBranches branches = branches.flatMap (fun (_, g) => g.freeVars) := by
  induction branches with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk label g =>
          simp [freeVarsOfBranches, ih, List.flatMap]

/- Substitute a global type for a variable. -/
mutual
  def GlobalType.substitute : GlobalType → String → GlobalType → GlobalType
    | .end, _, _ => .end
    | .comm sender receiver branches, varName, replacement =>
        .comm sender receiver (substituteBranches branches varName replacement)
    | .mu t body, varName, replacement =>
        if t == varName then
          .mu t body
        else
          .mu t (body.substitute varName replacement)
    | .var t, varName, replacement =>
        if t == varName then replacement else .var t

  def substituteBranches : List (Label × GlobalType) → String → GlobalType → List (Label × GlobalType)
    | [], _, _ => []
    | (label, cont) :: rest, varName, replacement =>
        (label, cont.substitute varName replacement) ::
          substituteBranches rest varName replacement
end

/- Check if all recursion variables are bound. -/
mutual
  def GlobalType.allVarsBound (g : GlobalType) (bound : List String := []) : Bool :=
    match g with
    | .end => true
    | .var t => bound.contains t
    | .mu t body => body.allVarsBound (t :: bound)
    | .comm _ _ branches => allVarsBoundBranches branches bound

  def allVarsBoundBranches (branches : List (Label × GlobalType)) (bound : List String) : Bool :=
    match branches with
    | [] => true
    | (_, g) :: rest => g.allVarsBound bound && allVarsBoundBranches rest bound
end

/- Check that all communications have at least one branch. -/
mutual
  def GlobalType.allCommsNonEmpty : GlobalType → Bool
    | .end => true
    | .var _ => true
    | .mu _ body => body.allCommsNonEmpty
    | .comm _ _ branches =>
        branches.isEmpty = false && allCommsNonEmptyBranches branches

  def allCommsNonEmptyBranches : List (Label × GlobalType) → Bool
    | [] => true
    | (_, g) :: rest => g.allCommsNonEmpty && allCommsNonEmptyBranches rest
end

/- Disallow self-communication in all subterms. -/
mutual
  def GlobalType.noSelfComm : GlobalType → Bool
    | .end => true
    | .var _ => true
    | .mu _ body => body.noSelfComm
    | .comm sender receiver branches =>
        sender != receiver && noSelfCommBranches branches

  def noSelfCommBranches : List (Label × GlobalType) → Bool
    | [] => true
    | (_, g) :: rest => g.noSelfComm && noSelfCommBranches rest
end

/-- Well-formedness predicate for global types. -/
def GlobalType.wellFormed (g : GlobalType) : Bool :=
  g.allVarsBound && g.allCommsNonEmpty && g.noSelfComm

/-- Global action with payload label (sender, receiver, label). -/
structure GlobalActionR where
  sender : String
  receiver : String
  label : Label
  deriving Repr, DecidableEq, Inhabited

/-- Global enabledness: an action is available in the global type. -/
inductive canStep : GlobalType → GlobalActionR → Prop where
  | comm_head (sender receiver : String) (branches : List (Label × GlobalType))
      (label : Label) (cont : GlobalType) :
      (label, cont) ∈ branches →
      canStep (.comm sender receiver branches) { sender := sender, receiver := receiver, label := label }
  | comm_async (sender receiver : String) (branches : List (Label × GlobalType))
      (act : GlobalActionR) (label : Label) (cont : GlobalType) :
      act.sender ≠ receiver →
      (act.sender = sender → act.receiver ≠ receiver) →
      (label, cont) ∈ branches →
      canStep cont act →
      canStep (.comm sender receiver branches) act
  | mu (t : String) (body : GlobalType) (act : GlobalActionR) :
      canStep (body.substitute t (.mu t body)) act →
      canStep (.mu t body) act

/-- Branch-wise step for async commutation. -/
inductive BranchesStep (stepFn : GlobalType → GlobalActionR → GlobalType → Prop) :
    List (Label × GlobalType) → GlobalActionR → List (Label × GlobalType) → Prop where
  | nil (act : GlobalActionR) : BranchesStep stepFn [] act []
  | cons (label : Label) (g g' : GlobalType) (rest rest' : List (Label × GlobalType))
      (act : GlobalActionR) :
      stepFn g act g' →
      BranchesStep stepFn rest act rest' →
      BranchesStep stepFn ((label, g) :: rest) act ((label, g') :: rest')

/-- Global async step relation (allows skipping unrelated prefixes). -/
inductive step : GlobalType → GlobalActionR → GlobalType → Prop where
  | comm_head (sender receiver : String) (branches : List (Label × GlobalType))
      (label : Label) (cont : GlobalType) :
      (label, cont) ∈ branches →
      step (.comm sender receiver branches) { sender := sender, receiver := receiver, label := label } cont
  | comm_async (sender receiver : String) (branches branches' : List (Label × GlobalType))
      (act : GlobalActionR) (label : Label) (cont : GlobalType) :
      act.sender ≠ receiver →
      (act.sender = sender → act.receiver ≠ receiver) →
      (label, cont) ∈ branches →
      canStep cont act →
      BranchesStep step branches act branches' →
      step (.comm sender receiver branches) act (.comm sender receiver branches')
  | mu (t : String) (body : GlobalType) (act : GlobalActionR) (g' : GlobalType) :
      step (body.substitute t (.mu t body)) act g' →
      step (.mu t body) act g'

/-! ## Helper lemmas for eraseDups membership

These use well-founded recursion on list length since `eraseDups_cons` expands to
use `filter`, which shrinks the list. -/

/-- Helper for mem_of_mem_eraseDups using termination_by. -/
private def mem_of_mem_eraseDups_aux {α : Type*} [BEq α] (a : α) (l : List α)
    (h : a ∈ l.eraseDups) : a ∈ l :=
  match l with
  | [] => by simp [List.eraseDups] at h
  | x :: xs => by
      rw [List.eraseDups_cons] at h
      simp only [List.mem_cons] at h ⊢
      cases h with
      | inl hax => left; exact hax
      | inr hrest =>
          right
          have := mem_of_mem_eraseDups_aux a (xs.filter (fun b => !b == x)) hrest
          exact List.mem_filter.mp this |>.1
termination_by l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ xs)

/-- Elements of eraseDups are elements of the original list. -/
theorem mem_of_mem_eraseDups {a : String} {l : List String}
    (h : a ∈ l.eraseDups) : a ∈ l :=
  mem_of_mem_eraseDups_aux a l h

/-- Helper for mem_eraseDups_of_mem using termination_by. -/
private def mem_eraseDups_of_mem_aux {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) (l : List α) (h : a ∈ l) : a ∈ l.eraseDups :=
  match l with
  | [] => by simp at h
  | x :: xs => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons] at h ⊢
      cases h with
      | inl hax =>
          left; exact hax
      | inr hxs =>
          by_cases heq : a = x
          · left; exact heq
          · right
            have hfilter : a ∈ xs.filter (fun b => !b == x) := by
              rw [List.mem_filter]
              constructor
              · exact hxs
              · simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
                exact heq
            exact mem_eraseDups_of_mem_aux a (xs.filter (fun b => !b == x)) hfilter
termination_by l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ xs)

/-- Elements of the original list are in eraseDups. -/
theorem mem_eraseDups_of_mem {a : String} {l : List String}
    (h : a ∈ l) : a ∈ l.eraseDups :=
  mem_eraseDups_of_mem_aux a l h

/-- Helper for nodup_eraseDups using termination_by. -/
private def nodup_eraseDups_aux {α : Type*} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup :=
  match l with
  | [] => by simp [List.eraseDups, List.Nodup]
  | x :: xs => by
      rw [List.eraseDups_cons]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have hfilt : x ∈ xs.filter (fun b => !b == x) := mem_of_mem_eraseDups_aux x _ hmem
        rw [List.mem_filter] at hfilt
        have heq : (!x == x) = false := by simp
        rw [heq] at hfilt
        exact Bool.false_ne_true hfilt.2
      · exact nodup_eraseDups_aux (xs.filter (fun b => !b == x))
termination_by l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ xs)

/-- eraseDups produces a list with no duplicates. -/
theorem nodup_eraseDups {α : Type*} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup :=
  nodup_eraseDups_aux l

/-- GlobalType.roles always produces a Nodup list. -/
def GlobalType.roles_nodup : (g : GlobalType) → g.roles.Nodup
  | .end => List.Pairwise.nil
  | .var _ => List.Pairwise.nil
  | .mu _ body => GlobalType.roles_nodup body
  | .comm _ _ _ => nodup_eraseDups _

/-! ## Substitution preserves role containment

These lemmas show that substituting a mu-type for its variable doesn't add new roles. -/

mutual
  /-- Substitution can only introduce roles from the replacement type. -/
  theorem substitute_roles_subset (g : GlobalType) (t : String) (repl : GlobalType) :
      ∀ p, p ∈ (g.substitute t repl).roles → p ∈ g.roles ∨ p ∈ repl.roles :=
    match g with
    | .end => fun _ hp => by simp [GlobalType.substitute, GlobalType.roles] at hp
    | .var s => fun p hp => by
        simp only [GlobalType.substitute] at hp
        split at hp
        · right; exact hp
        · simp [GlobalType.roles] at hp
    | .mu s inner => fun p hp => by
        simp only [GlobalType.substitute, GlobalType.roles] at hp ⊢
        split at hp
        · left; exact hp
        · have ih := substitute_roles_subset inner t repl p hp
          cases ih with
          | inl hl => left; exact hl
          | inr hr => right; exact hr
    | .comm sender receiver branches => fun p hp => by
        simp only [GlobalType.substitute, GlobalType.roles] at hp ⊢
        have hp' := mem_of_mem_eraseDups hp
        simp only [List.mem_append] at hp'
        cases hp' with
        | inl hsr =>
            left
            exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inl hsr))
        | inr hbranches =>
            have ih := substituteBranches_roles_subset branches t repl p hbranches
            cases ih with
            | inl horiginal =>
                left
                exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inr horiginal))
            | inr hrepl => right; exact hrepl

  /-- Branch substitution preserves role containment. -/
  theorem substituteBranches_roles_subset (branches : List (Label × GlobalType))
      (t : String) (repl : GlobalType) :
      ∀ p, p ∈ rolesOfBranches (substituteBranches branches t repl) →
           p ∈ rolesOfBranches branches ∨ p ∈ repl.roles :=
    match branches with
    | [] => fun _ hp => by simp [substituteBranches, rolesOfBranches] at hp
    | (label, cont) :: rest => fun p hp => by
        simp only [substituteBranches, rolesOfBranches, List.mem_append] at hp ⊢
        cases hp with
        | inl hl =>
            have ih := substitute_roles_subset cont t repl p hl
            cases ih with
            | inl hcont => left; left; exact hcont
            | inr hrepl => right; exact hrepl
        | inr hr =>
            have ih := substituteBranches_roles_subset rest t repl p hr
            cases ih with
            | inl hrest => left; right; exact hrest
            | inr hrepl => right; exact hrepl
end

/-- Substituting mu t body for var t in body doesn't add new roles. -/
theorem substitute_mu_roles_subset (body : GlobalType) (t : String) :
    ∀ p, p ∈ (body.substitute t (.mu t body)).roles → p ∈ body.roles := by
  intro p hp
  have h := substitute_roles_subset body t (.mu t body) p hp
  cases h with
  | inl hl => exact hl
  | inr hr =>
      simp only [GlobalType.roles] at hr
      exact hr

end RumpsteakV2.Protocol.GlobalType
