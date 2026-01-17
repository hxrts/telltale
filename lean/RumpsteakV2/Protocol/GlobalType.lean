import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup

set_option linter.dupNamespace false

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

mutual
  /-- Extract all role names from a global type. -/
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

mutual
  /-- Extract free type variables from a global type. -/
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

mutual
  /-- Substitute a global type for a variable: `g.substitute v repl` replaces free occurrences of `v` in `g` with `repl`. -/
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

mutual
  /-- Check if all recursion variables are bound. -/
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

/-- Extract allVarsBound for individual branches from comm. -/
theorem allVarsBound_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (h : (GlobalType.comm sender receiver branches).allVarsBound = true) :
    ∀ b ∈ branches, b.2.allVarsBound = true := by
  intro b hmem
  simp only [GlobalType.allVarsBound] at h
  induction branches generalizing b with
  | nil => cases hmem
  | cons hd tl ih =>
      simp only [allVarsBoundBranches, Bool.and_eq_true] at h
      cases hmem with
      | head _ => exact h.1
      | tail _ hmem' => exact ih h.2 b hmem'

mutual
  /-- Check that all communications have at least one branch. -/
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

mutual
  /-- Disallow self-communication in all subterms. -/
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

mutual
  /-- Productivity: every recursion cycle has a communication.

      A global type is productive if between any mu binder and its recursive
      variable usage, there is at least one communication. This prevents
      non-productive protocols like `mu X. X` that loop forever silently.

      The `unguarded` parameter tracks mu variables that have NOT yet seen
      a communication since their binding. When we see a comm, all variables
      become guarded (reset to empty). When we see a var, it must not be
      in the unguarded set. -/
  def GlobalType.isProductive (g : GlobalType) (unguarded : List String := []) : Bool :=
    match g with
    | .end => true
    | .var t => !unguarded.contains t  -- var in unguarded mu is non-productive
    | .mu t body => body.isProductive (t :: unguarded)  -- add t to unguarded
    | .comm _ _ branches =>
        -- After comm, all vars become guarded (reset unguarded to [])
        isProductiveBranches branches []

  def isProductiveBranches (branches : List (Label × GlobalType)) (unguarded : List String) : Bool :=
    match branches with
    | [] => true
    | (_, g) :: rest => g.isProductive unguarded && isProductiveBranches rest unguarded
end

/-- Extract labels from a list of branches. -/
def branchLabels (branches : List (Label × GlobalType)) : List Label :=
  branches.map Prod.fst

mutual
  /-- Check that all branch labels in communications are unique (no duplicates). -/
  def GlobalType.uniqueBranchLabels : GlobalType → Bool
    | .end => true
    | .var _ => true
    | .mu _ body => body.uniqueBranchLabels
    | .comm _ _ branches =>
        let labels := branchLabels branches
        labels.Nodup && uniqueBranchLabelsBranches branches

  def uniqueBranchLabelsBranches : List (Label × GlobalType) → Bool
    | [] => true
    | (_, g) :: rest => g.uniqueBranchLabels && uniqueBranchLabelsBranches rest
end

/-- Unique branch labels implies membership with same label gives same continuation. -/
theorem mem_branch_unique_label {branches : List (Label × GlobalType)}
    {label : Label} {cont cont' : GlobalType}
    (huniq : (branchLabels branches).Nodup)
    (hmem1 : (label, cont) ∈ branches)
    (hmem2 : (label, cont') ∈ branches) :
    cont = cont' := by
  induction branches with
  | nil => simp at hmem1
  | cons head tail ih =>
      simp only [branchLabels, List.map_cons, List.nodup_cons] at huniq
      obtain ⟨hnotmem, htail_nodup⟩ := huniq
      simp only [List.mem_cons] at hmem1 hmem2
      rcases hmem1 with rfl | hmem1_tail
      · -- hmem1: head = (label, cont)
        rcases hmem2 with heq | hmem2_tail
        · -- hmem2: (label, cont') = (label, cont), so cont = cont'
          exact ((Prod.mk.injEq _ _ _ _).mp heq |>.2).symm
        · -- hmem2_tail: (label, cont') ∈ tail
          -- But head.1 = label, so label ∈ branchLabels tail, contradicting hnotmem
          have hlabel_in_tail : label ∈ branchLabels tail := by
            simp only [branchLabels, List.mem_map]
            exact ⟨(label, cont'), hmem2_tail, rfl⟩
          exact absurd hlabel_in_tail hnotmem
      · -- hmem1_tail: (label, cont) ∈ tail
        rcases hmem2 with heq | hmem2_tail
        · -- heq: (label, cont') = head
          -- So head.fst = label
          -- hnotmem: ¬head.fst ∈ branchLabels tail
          -- But (label, cont) ∈ tail implies label ∈ branchLabels tail
          have heq_fst : head.fst = label := congrArg Prod.fst heq.symm
          rw [heq_fst] at hnotmem
          have hlabel_in_tail : label ∈ branchLabels tail := by
            simp only [branchLabels, List.mem_map]
            exact ⟨(label, cont), hmem1_tail, rfl⟩
          exact absurd hlabel_in_tail hnotmem
        · -- Both in tail
          exact ih htail_nodup hmem1_tail hmem2_tail

/-- Substitution preserves branch labels: the labels of substituted branches are the same as original. -/
theorem branchLabels_substituteBranches (branches : List (Label × GlobalType))
    (varName : String) (replacement : GlobalType) :
    branchLabels (substituteBranches branches varName replacement) = branchLabels branches := by
  induction branches with
  | nil => rfl
  | cons head tail ih =>
      simp only [substituteBranches, branchLabels, List.map_cons]
      exact congrArg (head.1 :: ·) ih

mutual
  /-- uniqueBranchLabels is preserved by substitution on a global type.

  **Requires:** Both the original type `g` and the replacement have unique branch labels. -/
  theorem GlobalType.uniqueBranchLabels_substitute (g : GlobalType)
      (varName : String) (replacement : GlobalType)
      (huniq : g.uniqueBranchLabels = true)
      (huniq_repl : replacement.uniqueBranchLabels = true) :
      (g.substitute varName replacement).uniqueBranchLabels = true := by
    match g with
    | .end => simp only [GlobalType.substitute, GlobalType.uniqueBranchLabels]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · exact huniq_repl
        · simp only [GlobalType.uniqueBranchLabels]
    | .mu t body =>
        simp only [GlobalType.substitute]
        split
        · exact huniq
        · simp only [GlobalType.uniqueBranchLabels] at huniq ⊢
          exact GlobalType.uniqueBranchLabels_substitute body varName replacement huniq huniq_repl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.uniqueBranchLabels, Bool.and_eq_true,
                   branchLabels_substituteBranches] at huniq ⊢
        exact ⟨huniq.1, uniqueBranchLabelsBranches_substitute branches varName replacement huniq.2 huniq_repl⟩

  /-- uniqueBranchLabels is preserved by substitution on branches. -/
  theorem uniqueBranchLabelsBranches_substitute (branches : List (Label × GlobalType))
      (varName : String) (replacement : GlobalType)
      (huniq : uniqueBranchLabelsBranches branches = true)
      (huniq_repl : replacement.uniqueBranchLabels = true) :
      uniqueBranchLabelsBranches (substituteBranches branches varName replacement) = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq ⊢
        exact ⟨GlobalType.uniqueBranchLabels_substitute cont varName replacement huniq.1 huniq_repl,
               uniqueBranchLabelsBranches_substitute rest varName replacement huniq.2 huniq_repl⟩
end

/-- Well-formedness predicate for global types. -/
def GlobalType.wellFormed (g : GlobalType) : Bool :=
  g.allVarsBound && g.allCommsNonEmpty && g.noSelfComm && g.isProductive

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

/-! ## Well-formedness Preservation under Mu-Unfolding

These lemmas show that unfolding a mu-type preserves well-formedness.
Key property: if `mu t body` is well-formed, then `body.substitute t (mu t body)` is well-formed. -/

-- Helper lemmas for allVarsBound

/-- If t is in (x :: xs) and t ≠ x, then t is in xs. -/
theorem contains_cons_ne' {t x : String} {xs : List String}
    (hcontains : (x :: xs).contains t = true)
    (hne : t ≠ x) :
    xs.contains t = true := by
  rw [List.contains_cons] at hcontains
  simp only [Bool.or_eq_true] at hcontains
  cases hcontains with
  | inl heq =>
      simp only [beq_iff_eq] at heq
      exact absurd heq hne
  | inr hmem => exact hmem

-- allVarsBound is monotonic: if vars are bound with bound1, they're bound with any superset.
mutual
  theorem allVarsBound_mono (g : GlobalType) (bound₁ bound₂ : List String)
      (hsub : ∀ x, bound₁.contains x = true → bound₂.contains x = true)
      (hbound : g.allVarsBound bound₁ = true) :
      g.allVarsBound bound₂ = true := by
    match g with
    | .end => simp [GlobalType.allVarsBound]
    | .var t =>
        simp only [GlobalType.allVarsBound] at hbound ⊢
        exact hsub t hbound
    | .mu t body =>
        simp only [GlobalType.allVarsBound] at hbound ⊢
        apply allVarsBound_mono body (t :: bound₁) (t :: bound₂)
        · intro x hx
          rw [List.contains_cons] at hx ⊢
          simp only [Bool.or_eq_true] at hx ⊢
          cases hx with
          | inl heq => left; exact heq
          | inr hmem => right; exact hsub x hmem
        · exact hbound
    | .comm _ _ branches =>
        simp only [GlobalType.allVarsBound] at hbound ⊢
        exact allVarsBoundBranches_mono branches bound₁ bound₂ hsub hbound

  theorem allVarsBoundBranches_mono (branches : List (Label × GlobalType))
      (bound₁ bound₂ : List String)
      (hsub : ∀ x, bound₁.contains x = true → bound₂.contains x = true)
      (hbound : allVarsBoundBranches branches bound₁ = true) :
      allVarsBoundBranches branches bound₂ = true := by
    match branches with
    | [] => rfl
    | (_, g) :: rest =>
        simp only [allVarsBoundBranches, Bool.and_eq_true] at hbound ⊢
        exact ⟨allVarsBound_mono g bound₁ bound₂ hsub hbound.1,
               allVarsBoundBranches_mono rest bound₁ bound₂ hsub hbound.2⟩
end

/-- Adding a duplicate element to bound doesn't change allVarsBound. -/
theorem allVarsBound_cons_dup (g : GlobalType) (x : String) (bound : List String)
    (hbound : g.allVarsBound (x :: bound) = true) :
    g.allVarsBound (x :: x :: bound) = true := by
  apply allVarsBound_mono g (x :: bound) (x :: x :: bound)
  · intro y hy
    rw [List.contains_cons] at hy ⊢
    simp only [Bool.or_eq_true] at hy ⊢
    cases hy with
    | inl heq => left; exact heq
    | inr hmem =>
        right
        rw [List.contains_cons]
        simp only [Bool.or_eq_true]
        right; exact hmem
  · exact hbound

/-- Removing a duplicate from bound preserves allVarsBound. -/
theorem allVarsBound_cons_dedup (g : GlobalType) (x : String) (bound : List String)
    (hbound : g.allVarsBound (x :: x :: bound) = true) :
    g.allVarsBound (x :: bound) = true := by
  apply allVarsBound_mono g (x :: x :: bound) (x :: bound)
  · intro y hy
    rw [List.contains_cons] at hy ⊢
    simp only [Bool.or_eq_true] at hy ⊢
    cases hy with
    | inl heq => left; exact heq
    | inr hmem =>
        rw [List.contains_cons] at hmem
        simp only [Bool.or_eq_true] at hmem
        cases hmem with
        | inl heq => left; exact heq
        | inr hmem' => right; exact hmem'
  · exact hbound

/-- Swapping adjacent elements in bound preserves allVarsBound. -/
theorem allVarsBound_swap (g : GlobalType) (x y : String) (bound : List String)
    (hbound : g.allVarsBound (x :: y :: bound) = true) :
    g.allVarsBound (y :: x :: bound) = true := by
  apply allVarsBound_mono g (x :: y :: bound) (y :: x :: bound)
  · intro z hz
    rw [List.contains_cons] at hz ⊢
    simp only [Bool.or_eq_true] at hz ⊢
    cases hz with
    | inl heq =>
        -- z == x, so z is in (y :: x :: bound) via second element
        right
        rw [List.contains_cons]
        simp only [Bool.or_eq_true]
        left; exact heq
    | inr hmem =>
        rw [List.contains_cons] at hmem
        simp only [Bool.or_eq_true] at hmem
        cases hmem with
        | inl heq =>
            -- z == y, so z is at the head
            left; exact heq
        | inr hmem' =>
            -- z in bound
            right
            rw [List.contains_cons]
            simp only [Bool.or_eq_true]
            right; exact hmem'
  · exact hbound

mutual
  /-- allVarsBound is preserved when substituting a closed type for a bound variable.

  **Key insight**: When we substitute `mu t body` for occurrences of `var t` in body,
  the result is still closed because `mu t body` binds t. -/
  theorem allVarsBound_substitute (g : GlobalType) (varName : String) (repl : GlobalType)
      (bound : List String)
      (hg : g.allVarsBound (varName :: bound) = true)
      (hrepl : repl.allVarsBound bound = true) :
      (g.substitute varName repl).allVarsBound bound = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.allVarsBound]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · -- t = varName, so we substitute repl
          exact hrepl
        · -- t ≠ varName, so var t stays
          rename_i hne
          simp only [GlobalType.allVarsBound] at hg ⊢
          -- hne: (t == varName) = false, which means t ≠ varName
          have hne' : t ≠ varName := by
            intro heq
            simp only [heq, beq_self_eq_true] at hne
            exact absurd trivial hne
          exact contains_cons_ne' hg hne'
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · -- t = varName, shadowed, so no substitution in inner
          rename_i heq
          simp only [GlobalType.allVarsBound] at hg ⊢
          -- heq: (t == varName) = true, so t = varName
          have heq' : t = varName := by simp only [beq_iff_eq] at heq; exact heq
          -- hg: inner.allVarsBound (t :: varName :: bound) = true
          -- Since t = varName, this is inner.allVarsBound (varName :: varName :: bound)
          rw [heq'] at hg ⊢
          -- Now hg: inner.allVarsBound (varName :: varName :: bound) = true
          -- Goal: inner.allVarsBound (varName :: bound) = true
          exact allVarsBound_cons_dedup inner varName bound hg
        · -- t ≠ varName
          simp only [GlobalType.allVarsBound] at hg ⊢
          -- hg: inner.allVarsBound (t :: varName :: bound) = true
          -- Need: (inner.substitute varName repl).allVarsBound (t :: bound) = true
          -- Use IH with bound' = (t :: bound)
          -- Need: inner.allVarsBound (varName :: t :: bound) = true (from swap)
          -- Need: repl.allVarsBound (t :: bound) = true (from mono)
          have hg' : inner.allVarsBound (varName :: t :: bound) = true :=
            allVarsBound_swap inner t varName bound hg
          have hrepl' : repl.allVarsBound (t :: bound) = true := by
            apply allVarsBound_mono repl bound (t :: bound)
            · intro x hx
              rw [List.contains_cons]
              simp only [Bool.or_eq_true]
              right; exact hx
            · exact hrepl
          exact allVarsBound_substitute inner varName repl (t :: bound) hg' hrepl'
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.allVarsBound] at hg ⊢
        exact allVarsBoundBranches_substitute branches varName repl bound hg hrepl

  theorem allVarsBoundBranches_substitute (branches : List (Label × GlobalType))
      (varName : String) (repl : GlobalType) (bound : List String)
      (hg : allVarsBoundBranches branches (varName :: bound) = true)
      (hrepl : repl.allVarsBound bound = true) :
      allVarsBoundBranches (substituteBranches branches varName repl) bound = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, allVarsBoundBranches, Bool.and_eq_true] at hg ⊢
        exact ⟨allVarsBound_substitute cont varName repl bound hg.1 hrepl,
               allVarsBoundBranches_substitute rest varName repl bound hg.2 hrepl⟩
end

mutual
  /-- allCommsNonEmpty is preserved by substitution. -/
  theorem allCommsNonEmpty_substitute (g : GlobalType) (varName : String) (repl : GlobalType)
      (hg : g.allCommsNonEmpty = true)
      (hrepl : repl.allCommsNonEmpty = true) :
      (g.substitute varName repl).allCommsNonEmpty = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.allCommsNonEmpty]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · exact hrepl
        · simp [GlobalType.allCommsNonEmpty]
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · exact hg
        · simp only [GlobalType.allCommsNonEmpty] at hg ⊢
          exact allCommsNonEmpty_substitute inner varName repl hg hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.allCommsNonEmpty, Bool.and_eq_true] at hg ⊢
        constructor
        · -- Need: substituteBranches preserves non-emptiness
          -- substituteBranches preserves length, so if branches is non-empty, result is too
          match hb : branches with
          | [] => simp [List.isEmpty] at hg
          | _ :: _ => simp [substituteBranches, List.isEmpty]
        · exact allCommsNonEmptyBranches_substitute branches varName repl hg.2 hrepl

  theorem allCommsNonEmptyBranches_substitute (branches : List (Label × GlobalType))
      (varName : String) (repl : GlobalType)
      (hg : allCommsNonEmptyBranches branches = true)
      (hrepl : repl.allCommsNonEmpty = true) :
      allCommsNonEmptyBranches (substituteBranches branches varName repl) = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, allCommsNonEmptyBranches, Bool.and_eq_true] at hg ⊢
        exact ⟨allCommsNonEmpty_substitute cont varName repl hg.1 hrepl,
               allCommsNonEmptyBranches_substitute rest varName repl hg.2 hrepl⟩
end

mutual
  /-- noSelfComm is preserved by substitution. -/
  theorem noSelfComm_substitute (g : GlobalType) (varName : String) (repl : GlobalType)
      (hg : g.noSelfComm = true)
      (hrepl : repl.noSelfComm = true) :
      (g.substitute varName repl).noSelfComm = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.noSelfComm]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · exact hrepl
        · simp [GlobalType.noSelfComm]
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · exact hg
        · simp only [GlobalType.noSelfComm] at hg ⊢
          exact noSelfComm_substitute inner varName repl hg hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.noSelfComm, Bool.and_eq_true] at hg ⊢
        exact ⟨hg.1, noSelfCommBranches_substitute branches varName repl hg.2 hrepl⟩

  theorem noSelfCommBranches_substitute (branches : List (Label × GlobalType))
      (varName : String) (repl : GlobalType)
      (hg : noSelfCommBranches branches = true)
      (hrepl : repl.noSelfComm = true) :
      noSelfCommBranches (substituteBranches branches varName repl) = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, noSelfCommBranches, Bool.and_eq_true] at hg ⊢
        exact ⟨noSelfComm_substitute cont varName repl hg.1 hrepl,
               noSelfCommBranches_substitute rest varName repl hg.2 hrepl⟩
end

-- Helper lemmas for isProductive monotonicity with respect to unguarded list

-- isProductive is monotonic: adding elements to unguarded can only make it false, not true.
-- Equivalently, if productive with more elements in unguarded, productive with fewer.
mutual
  theorem isProductive_mono (g : GlobalType) (ug1 ug2 : List String)
      (hsub : ∀ x, ug1.contains x = true → ug2.contains x = true)
      (hprod : g.isProductive ug2 = true) :
      g.isProductive ug1 = true := by
    match g with
    | .end => rfl
    | .var t =>
        simp only [GlobalType.isProductive, Bool.not_eq_true'] at hprod ⊢
        -- hprod: ug2.contains t = false
        -- Goal: ug1.contains t = false
        -- Proof by contrapositive: if ug1.contains t = true, then ug2.contains t = true
        by_contra hug1
        simp only [Bool.not_eq_false] at hug1
        have h := hsub t hug1
        rw [hprod] at h
        exact Bool.false_ne_true h
    | .mu t body =>
        simp only [GlobalType.isProductive] at hprod ⊢
        apply isProductive_mono body (t :: ug1) (t :: ug2)
        · intro x hx
          rw [List.contains_cons] at hx ⊢
          simp only [Bool.or_eq_true] at hx ⊢
          cases hx with
          | inl heq => left; exact heq
          | inr hmem => right; exact hsub x hmem
        · exact hprod
    | .comm _ _ branches =>
        simp only [GlobalType.isProductive] at hprod ⊢
        exact hprod  -- comm resets unguarded to [], so independent of ug1/ug2

  theorem isProductiveBranches_mono (branches : List (Label × GlobalType))
      (ug1 ug2 : List String)
      (hsub : ∀ x, ug1.contains x = true → ug2.contains x = true)
      (hprod : isProductiveBranches branches ug2 = true) :
      isProductiveBranches branches ug1 = true := by
    match branches with
    | [] => rfl
    | (_, g) :: rest =>
        simp only [isProductiveBranches, Bool.and_eq_true] at hprod ⊢
        exact ⟨isProductive_mono g ug1 ug2 hsub hprod.1,
               isProductiveBranches_mono rest ug1 ug2 hsub hprod.2⟩
end

/-- Removing a duplicate from unguarded preserves isProductive. -/
theorem isProductive_cons_dedup (g : GlobalType) (x : String) (unguarded : List String)
    (hprod : g.isProductive (x :: x :: unguarded) = true) :
    g.isProductive (x :: unguarded) = true := by
  apply isProductive_mono g (x :: unguarded) (x :: x :: unguarded)
  · intro y hy
    rw [List.contains_cons] at hy ⊢
    simp only [Bool.or_eq_true] at hy ⊢
    cases hy with
    | inl heq => left; exact heq
    | inr hmem =>
        right
        rw [List.contains_cons]
        simp only [Bool.or_eq_true]
        right; exact hmem
  · exact hprod

/-- Swapping adjacent elements in unguarded preserves isProductive. -/
theorem isProductive_swap (g : GlobalType) (x y : String) (unguarded : List String)
    (hprod : g.isProductive (x :: y :: unguarded) = true) :
    g.isProductive (y :: x :: unguarded) = true := by
  apply isProductive_mono g (y :: x :: unguarded) (x :: y :: unguarded)
  · intro z hz
    rw [List.contains_cons] at hz ⊢
    simp only [Bool.or_eq_true] at hz ⊢
    cases hz with
    | inl heq =>
        right
        rw [List.contains_cons]
        simp only [Bool.or_eq_true]
        left; exact heq
    | inr hmem =>
        rw [List.contains_cons] at hmem
        simp only [Bool.or_eq_true] at hmem
        cases hmem with
        | inl heq => left; exact heq
        | inr hmem' =>
            right
            rw [List.contains_cons]
            simp only [Bool.or_eq_true]
            right; exact hmem'
  · exact hprod

-- isProductive is unaffected by extending unguarded with variables not in the type.
-- If a variable x is not used in g (i.e., x is not in any var constructor), then
-- adding x to unguarded doesn't affect isProductive.

-- Key lemma: if body.allVarsBound bound = true and body.isProductive bound = true,
-- then body.isProductive (bound ++ extra) = true for any extra.
-- This is because extra vars don't appear in body (due to allVarsBound).

mutual
  /-- If a type has all its vars bound and is productive, adding extra elements to
      unguarded preserves productivity (since those vars don't appear in the type). -/
  theorem isProductive_extend (g : GlobalType) (bound extra : List String)
      (hbound : g.allVarsBound bound = true)
      (hprod : g.isProductive bound = true) :
      g.isProductive (bound ++ extra) = true := by
    match g with
    | .end => rfl
    | .var t =>
        simp only [GlobalType.allVarsBound] at hbound
        simp only [GlobalType.isProductive, Bool.not_eq_true'] at hprod ⊢
        -- hbound: bound.contains t = true
        -- hprod: bound.contains t = false
        -- These are contradictory!
        rw [hbound] at hprod
        exact (Bool.false_ne_true hprod.symm).elim
    | .mu t body =>
        simp only [GlobalType.allVarsBound] at hbound
        simp only [GlobalType.isProductive] at hprod ⊢
        -- hbound: body.allVarsBound (t :: bound) = true
        -- hprod: body.isProductive (t :: bound) = true
        -- Goal: body.isProductive (t :: (bound ++ extra)) = true
        have h : t :: (bound ++ extra) = (t :: bound) ++ extra := rfl
        rw [h]
        exact isProductive_extend body (t :: bound) extra hbound hprod
    | .comm _ _ branches =>
        simp only [GlobalType.allVarsBound] at hbound
        simp only [GlobalType.isProductive] at hprod ⊢
        -- Comm resets unguarded to [], so the proof is trivial
        -- Actually, we need to show isProductiveBranches branches [] = true
        -- which is exactly hprod
        exact hprod

  theorem isProductiveBranches_extend (branches : List (Label × GlobalType))
      (bound extra : List String)
      (hbound : allVarsBoundBranches branches bound = true)
      (hprod : isProductiveBranches branches bound = true) :
      isProductiveBranches branches (bound ++ extra) = true := by
    match branches with
    | [] => rfl
    | (_, g) :: rest =>
        simp only [allVarsBoundBranches, Bool.and_eq_true] at hbound
        simp only [isProductiveBranches, Bool.and_eq_true] at hprod ⊢
        exact ⟨isProductive_extend g bound extra hbound.1 hprod.1,
               isProductiveBranches_extend rest bound extra hbound.2 hprod.2⟩
end

/-- Corollary: If (mu t body) is productive, then it's productive for any unguarded list. -/
theorem mu_isProductive_forall (t : String) (body : GlobalType)
    (hbound : body.allVarsBound [t] = true)
    (hprod : body.isProductive [t] = true) :
    ∀ ug, (GlobalType.mu t body).isProductive ug = true := by
  intro ug
  simp only [GlobalType.isProductive]
  -- Goal: body.isProductive (t :: ug) = true
  -- We have: body.allVarsBound [t] = true and body.isProductive [t] = true
  -- Use isProductive_extend with bound = [t] and extra = ug
  have h : [t] ++ ug = t :: ug := rfl
  rw [← h]
  exact isProductive_extend body [t] ug hbound hprod

-- isProductive preservation under substitution
--
-- Key insight: When g.isProductive (varName :: unguarded) = true, any occurrence of
-- var varName in g must be after a comm (which resets unguarded to []). So the replacement
-- only needs to be productive with [].

mutual
  /-- isProductive is preserved under substitution.

  The replacement must be productive for any unguarded list it might encounter.
  This is satisfied when repl.isProductive [] = true, because comm resets unguarded. -/
  theorem isProductive_substitute (g : GlobalType) (varName : String) (repl : GlobalType)
      (unguarded : List String)
      (hg : g.isProductive (varName :: unguarded) = true)
      (hrepl : ∀ ug, repl.isProductive ug = true) :
      (g.substitute varName repl).isProductive unguarded = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.isProductive]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · -- t = varName, substitute repl
          exact hrepl unguarded
        · -- t ≠ varName, keep var t
          rename_i hne
          simp only [GlobalType.isProductive, Bool.not_eq_true'] at hg ⊢
          by_contra hunguarded
          simp only [Bool.not_eq_false] at hunguarded
          have h : (varName :: unguarded).contains t = true := by
            rw [List.contains_cons]
            simp only [Bool.or_eq_true]
            right; exact hunguarded
          rw [hg] at h
          exact Bool.false_ne_true h
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · -- t = varName, shadowed - no substitution
          rename_i heq
          simp only [GlobalType.isProductive] at hg ⊢
          have heq' : t = varName := by simp only [beq_iff_eq] at heq; exact heq
          rw [heq'] at hg ⊢
          exact isProductive_cons_dedup inner varName unguarded hg
        · -- t ≠ varName
          simp only [GlobalType.isProductive] at hg ⊢
          have hg' : inner.isProductive (varName :: t :: unguarded) = true :=
            isProductive_swap inner t varName unguarded hg
          exact isProductive_substitute inner varName repl (t :: unguarded) hg' hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.isProductive] at hg ⊢
        -- comm resets unguarded to [], so hg : isProductiveBranches branches [] = true
        -- Goal: isProductiveBranches (substituteBranches branches varName repl) [] = true
        exact isProductiveBranches_substitute_any branches varName repl [] hg hrepl

  -- For branches, if replacement is always productive, substitution preserves productivity
  -- regardless of whether varName is in unguarded
  theorem isProductiveBranches_substitute_any (branches : List (Label × GlobalType))
      (varName : String) (repl : GlobalType) (unguarded : List String)
      (hg : isProductiveBranches branches unguarded = true)
      (hrepl : ∀ ug, repl.isProductive ug = true) :
      isProductiveBranches (substituteBranches branches varName repl) unguarded = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, isProductiveBranches, Bool.and_eq_true] at hg ⊢
        exact ⟨isProductive_substitute_any cont varName repl unguarded hg.1 hrepl,
               isProductiveBranches_substitute_any rest varName repl unguarded hg.2 hrepl⟩

  -- If replacement is always productive, substitution preserves productivity
  -- This is a more general version that doesn't require varName in unguarded
  theorem isProductive_substitute_any (g : GlobalType) (varName : String) (repl : GlobalType)
      (unguarded : List String)
      (hg : g.isProductive unguarded = true)
      (hrepl : ∀ ug, repl.isProductive ug = true) :
      (g.substitute varName repl).isProductive unguarded = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.isProductive]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · -- t = varName, substitute repl
          exact hrepl unguarded
        · -- t ≠ varName, keep var t
          exact hg
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · -- t = varName, shadowed - no substitution
          exact hg
        · -- t ≠ varName
          simp only [GlobalType.isProductive] at hg ⊢
          exact isProductive_substitute_any inner varName repl (t :: unguarded) hg hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.isProductive] at hg ⊢
        exact isProductiveBranches_substitute_any branches varName repl [] hg hrepl
end

/-- Mu-unfolding preserves well-formedness components that don't depend on variable binding.

This is a simplified version that shows noSelfComm and allCommsNonEmpty are preserved.
The full wellFormed preservation requires more sophisticated reasoning about allVarsBound
and isProductive. -/
theorem wellFormed_mu_unfold_partial (t : String) (body : GlobalType)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    (body.substitute t (GlobalType.mu t body)).noSelfComm = true ∧
    (body.substitute t (GlobalType.mu t body)).allCommsNonEmpty = true := by
  unfold GlobalType.wellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  -- hwf : (((_.allVarsBound ∧ _.allCommsNonEmpty) ∧ _.noSelfComm) ∧ _.isProductive)
  have hne := hwf.1.1.2  -- allCommsNonEmpty
  have hns := hwf.1.2    -- noSelfComm
  simp only [GlobalType.allCommsNonEmpty, GlobalType.noSelfComm] at hne hns
  exact ⟨noSelfComm_substitute body t (GlobalType.mu t body) hns hns,
         allCommsNonEmpty_substitute body t (GlobalType.mu t body) hne hne⟩

/-- Mu-unfolding preserves allVarsBound for closed types.

**Key insight**: If `mu t body` is closed (allVarsBound [] = true),
then `body.substitute t (mu t body)` is also closed.

This works because:
1. body.allVarsBound [t] = true (from mu's definition)
2. Substituting (mu t body) for t in body removes the t dependency
3. (mu t body).allVarsBound [] = true, so substituted vars are still bound -/
theorem allVarsBound_mu_unfold (t : String) (body : GlobalType)
    (hbound : (GlobalType.mu t body).allVarsBound [] = true) :
    (body.substitute t (GlobalType.mu t body)).allVarsBound [] = true := by
  -- hbound: (mu t body).allVarsBound [] = true
  -- which unfolds to: body.allVarsBound [t] = true
  simp only [GlobalType.allVarsBound] at hbound
  -- Now hbound: body.allVarsBound [t] = true
  -- Apply allVarsBound_substitute with bound = []
  -- Need: body.allVarsBound (t :: []) = body.allVarsBound [t] = true ✓
  -- Need: (mu t body).allVarsBound [] = true
  have hrepl : (GlobalType.mu t body).allVarsBound [] = true := by
    simp only [GlobalType.allVarsBound]
    exact hbound
  exact allVarsBound_substitute body t (GlobalType.mu t body) [] hbound hrepl

/-- Mu-unfolding preserves isProductive.

**Key insight**: If `mu t body` is productive AND has all vars bound,
then `body.substitute t (mu t body)` is also productive.

This requires both productivity (for guarded recursion) and allVarsBound
(so we know the replacement (mu t body) is productive for any unguarded list). -/
theorem isProductive_mu_unfold (t : String) (body : GlobalType)
    (hbound : (GlobalType.mu t body).allVarsBound [] = true)
    (hprod : (GlobalType.mu t body).isProductive = true) :
    (body.substitute t (GlobalType.mu t body)).isProductive = true := by
  simp only [GlobalType.allVarsBound] at hbound
  simp only [GlobalType.isProductive] at hprod
  -- hbound: body.allVarsBound [t] = true
  -- hprod: body.isProductive [t] = true
  -- Goal: (body.substitute t (mu t body)).isProductive [] = true
  -- Use isProductive_substitute with hrepl from mu_isProductive_forall
  have hrepl : ∀ ug, (GlobalType.mu t body).isProductive ug = true :=
    mu_isProductive_forall t body hbound hprod
  exact isProductive_substitute body t (GlobalType.mu t body) [] hprod hrepl

/-- Mu-unfolding preserves full well-formedness.

Main theorem: if `mu t body` is well-formed, then unfolding it
(substituting the whole mu-type for its bound variable) is also well-formed. -/
theorem wellFormed_mu_unfold (t : String) (body : GlobalType)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    (body.substitute t (GlobalType.mu t body)).wellFormed = true := by
  unfold GlobalType.wellFormed at hwf ⊢
  simp only [Bool.and_eq_true] at hwf ⊢
  obtain ⟨⟨⟨hbound, hne⟩, hns⟩, hprod⟩ := hwf
  simp only [GlobalType.allVarsBound, GlobalType.allCommsNonEmpty,
             GlobalType.noSelfComm, GlobalType.isProductive] at hbound hne hns hprod ⊢
  constructor
  constructor
  constructor
  · exact allVarsBound_mu_unfold t body hbound
  · exact allCommsNonEmpty_substitute body t (GlobalType.mu t body) hne hne
  · exact noSelfComm_substitute body t (GlobalType.mu t body) hns hns
  · exact isProductive_mu_unfold t body hbound hprod

/-! ## Closedness Predicate (Coq-style)

A global type is closed if it has no free type variables.
This matches Coq's approach and is used for projection preservation. -/

/-- A global type is closed if it has no free type variables. -/
def GlobalType.isClosed (g : GlobalType) : Bool := g.freeVars.isEmpty

/-! ### Closedness Lemmas

These lemmas establish structural properties of closedness, following the Coq approach
in `coGlobal.v` and `coLocal.v`. The key insight is that:
- `freeVars` for `comm` is the concatenation of branch continuations' free vars
- Substitution with a closed term doesn't introduce new free variables -/

/-- Helper: if a list is empty, all appended sublists must be empty. -/
private theorem freeVarsOfBranches_nil_iff (branches : List (Label × GlobalType)) :
    freeVarsOfBranches branches = [] ↔ ∀ p ∈ branches, p.2.freeVars = [] := by
  induction branches with
  | nil =>
      simp only [freeVarsOfBranches, List.not_mem_nil, false_implies, implies_true]
  | cons hd tl ih =>
      simp only [freeVarsOfBranches, List.append_eq_nil_iff, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h
        exact ⟨h.1, ih.mp h.2⟩
      · intro h
        exact ⟨h.1, ih.mpr h.2⟩

/-- A closed comm has closed branch continuations.

If `(comm sender receiver branches).isClosed = true`, then each branch continuation is closed.
This follows directly from the definition: freeVars of comm is the concatenation of branch freeVars.

**Coq reference:** Follows from `gType_fv` definition in `coGlobal.v`. -/
theorem GlobalType.isClosed_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hclosed : (GlobalType.comm sender receiver branches).isClosed = true) :
    ∀ p ∈ branches, p.2.isClosed = true := by
  simp only [GlobalType.isClosed, GlobalType.freeVars, List.isEmpty_iff] at hclosed
  have hbranches := freeVarsOfBranches_nil_iff branches
  intro p hp
  simp only [GlobalType.isClosed, List.isEmpty_iff]
  exact (hbranches.mp hclosed) p hp

/-- Helper: allCommsNonEmptyBranches ensures each branch has allCommsNonEmpty. -/
private theorem allCommsNonEmptyBranches_forall (branches : List (Label × GlobalType))
    (h : allCommsNonEmptyBranches branches = true) :
    ∀ p ∈ branches, p.2.allCommsNonEmpty = true := by
  induction branches with
  | nil => intro p hp; cases hp
  | cons hd tl ih =>
      simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at h
      intro p hp
      cases hp with
      | head _ => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- A comm with allCommsNonEmpty has all branch continuations with allCommsNonEmpty.

If `(comm sender receiver branches).allCommsNonEmpty = true`, then each branch continuation
has `allCommsNonEmpty = true`. This follows from the definition: allCommsNonEmpty of comm
requires allCommsNonEmptyBranches, which recursively checks each branch. -/
theorem GlobalType.allCommsNonEmpty_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hallcomms : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true) :
    ∀ p ∈ branches, p.2.allCommsNonEmpty = true := by
  simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true] at hallcomms
  exact allCommsNonEmptyBranches_forall branches hallcomms.2

private theorem noSelfCommBranches_forall (branches : List (Label × GlobalType))
    (h : noSelfCommBranches branches = true) :
    ∀ p ∈ branches, p.2.noSelfComm = true := by
  induction branches with
  | nil => intro p hp; cases hp
  | cons hd tl ih =>
      simp only [noSelfCommBranches, Bool.and_eq_true] at h
      intro p hp
      cases hp with
      | head _ => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- A comm with noSelfComm has all branch continuations with noSelfComm. -/
theorem GlobalType.noSelfComm_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hns : (GlobalType.comm sender receiver branches).noSelfComm = true) :
    ∀ p ∈ branches, p.2.noSelfComm = true := by
  simp only [GlobalType.noSelfComm, Bool.and_eq_true] at hns
  exact noSelfCommBranches_forall branches hns.2

private theorem isProductiveBranches_forall (branches : List (Label × GlobalType))
    (unguarded : List String)
    (h : isProductiveBranches branches unguarded = true) :
    ∀ p ∈ branches, p.2.isProductive unguarded = true := by
  induction branches with
  | nil => intro p hp; cases hp
  | cons hd tl ih =>
      simp only [isProductiveBranches, Bool.and_eq_true] at h
      intro p hp
      cases hp with
      | head _ => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- A comm that is productive has productive branch continuations. -/
theorem GlobalType.isProductive_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hprod : (GlobalType.comm sender receiver branches).isProductive = true) :
    ∀ p ∈ branches, p.2.isProductive = true := by
  simp only [GlobalType.isProductive] at hprod
  exact isProductiveBranches_forall branches [] hprod

/-- A well-formed comm has well-formed branch continuations. -/
theorem GlobalType.wellFormed_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true) :
    ∀ b ∈ branches, b.2.wellFormed = true := by
  intro b hb
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨hvars, hallcomms⟩, hnoself⟩, hprod⟩ := hwf
  have hvars_b : b.2.allVarsBound = true :=
    allVarsBound_comm_branches sender receiver branches hvars b hb
  have hallcomms_b : b.2.allCommsNonEmpty = true :=
    GlobalType.allCommsNonEmpty_comm_branches sender receiver branches hallcomms b hb
  have hnoself_b : b.2.noSelfComm = true :=
    GlobalType.noSelfComm_comm_branches sender receiver branches hnoself b hb
  have hprod_b : b.2.isProductive = true :=
    GlobalType.isProductive_comm_branches sender receiver branches hprod b hb
  simp [GlobalType.wellFormed, hvars_b, hallcomms_b, hnoself_b, hprod_b]

/-- Helper for freeVars_substitute_subset: branches case with explicit IH.

Free variables of a substituted term are bounded by original free vars (minus t) plus repl's free vars.
This is the key structural lemma for closedness preservation.

**Coq reference:** `gType_fv_subst` in `coGlobal.v` (line 753). -/
private def freeVars_substituteBranches_subset_aux
    {n : Nat} {t : String} {repl : GlobalType}
    (ih : ∀ g' : GlobalType, sizeOf g' < n →
          ∀ v, v ∈ (g'.substitute t repl).freeVars →
          (v ∈ g'.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars)
    (branches : List (Label × GlobalType))
    (hsize : ∀ p ∈ branches, sizeOf p.2 < n)
    (v : String)
    (hv : v ∈ freeVarsOfBranches (substituteBranches branches t repl)) :
    (v ∈ freeVarsOfBranches branches ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  match branches with
  | [] =>
      simp only [substituteBranches, freeVarsOfBranches, List.not_mem_nil] at hv
  | hd :: tl =>
      simp only [substituteBranches, freeVarsOfBranches, List.mem_append] at hv
      cases hv with
      | inl hv_hd =>
          have hsize_hd : sizeOf hd.2 < n := hsize hd List.mem_cons_self
          have hsub := ih hd.2 hsize_hd v hv_hd
          cases hsub with
          | inl h =>
              left
              simp only [freeVarsOfBranches, List.mem_append]
              exact ⟨Or.inl h.1, h.2⟩
          | inr hmem =>
              right
              exact hmem
      | inr hv_tl =>
          have hsize_tl : ∀ p ∈ tl, sizeOf p.2 < n := fun p hp =>
            hsize p (List.mem_cons_of_mem hd hp)
          have hsub := freeVars_substituteBranches_subset_aux ih tl hsize_tl v hv_tl
          cases hsub with
          | inl h =>
              left
              simp only [freeVarsOfBranches, List.mem_append]
              exact ⟨Or.inr h.1, h.2⟩
          | inr hmem =>
              right
              exact hmem

/-- Strong induction principle for freeVars_substitute_subset. -/
private theorem freeVars_substitute_subset_strong (n : Nat) :
    ∀ body : GlobalType, sizeOf body ≤ n →
    ∀ t repl v, v ∈ (body.substitute t repl).freeVars →
    (v ∈ body.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro body hsize t repl v hv
    match body with
    | .end =>
        simp only [GlobalType.substitute, GlobalType.freeVars, List.not_mem_nil] at hv
    | .var w =>
        simp only [GlobalType.substitute] at hv
        split at hv
        · -- w = t: substitute returns repl
          right
          exact hv
        · -- w ≠ t: substitute returns .var w
          simp only [GlobalType.freeVars, List.mem_singleton] at hv
          rename_i hwt
          -- hwt : ¬(w == t) = true, i.e., (w == t) ≠ true
          have hne : w ≠ t := by
            intro heq
            rw [heq] at hwt
            simp at hwt
          left
          exact ⟨hv ▸ List.mem_singleton_self w, hv ▸ hne⟩
    | .mu s inner =>
        simp only [GlobalType.substitute] at hv
        split at hv
        · -- s = t: substitution shadowed, body unchanged
          rename_i hst
          simp only [beq_iff_eq] at hst
          simp only [GlobalType.freeVars, List.mem_filter] at hv
          left
          simp only [GlobalType.freeVars, List.mem_filter]
          constructor
          · exact hv
          · -- v ∈ inner.freeVars.filter (· != s) means v != s
            have hvs := hv.2
            simp only [bne_iff_ne, ne_eq] at hvs
            rw [hst] at hvs
            exact hvs
        · -- s ≠ t: recurse into inner
          rename_i hst
          have hsne : s ≠ t := by
            intro heq
            rw [heq] at hst
            simp at hst
          simp only [GlobalType.freeVars, List.mem_filter] at hv
          have hvs := hv.2
          simp only [bne_iff_ne, ne_eq] at hvs
          -- inner is smaller than .mu s inner
          have hinner_size : sizeOf inner < sizeOf (GlobalType.mu s inner) := by
            simp only [GlobalType.mu.sizeOf_spec]; omega
          have hinner_le : sizeOf inner < n := Nat.lt_of_lt_of_le hinner_size hsize
          have hsub := ih (sizeOf inner) hinner_le inner (Nat.le_refl _) t repl v hv.1
          cases hsub with
          | inl hcase =>
              left
              simp only [GlobalType.freeVars, List.mem_filter, bne_iff_ne, ne_eq]
              exact ⟨⟨hcase.1, hvs⟩, hcase.2⟩
          | inr hmem =>
              right
              exact hmem
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.freeVars] at hv
        -- All branch continuations are smaller than the comm
        have hbranch_sizes : ∀ p ∈ branches, sizeOf p.2 < n := by
          intro p hp
          have h1 : sizeOf p.2 < sizeOf p := by
            cases p with | mk l g => simp only [Prod.mk.sizeOf_spec]; omega
          have h2 : sizeOf p < 1 + sizeOf branches := by
            have := List.sizeOf_lt_of_mem hp
            omega
          -- sizeOf (GlobalType.comm s r bs) = 1 + sizeOf s + sizeOf r + sizeOf bs
          -- We need to show: 1 + sizeOf branches < sizeOf (GlobalType.comm sender receiver branches)
          -- This is equivalent to: 0 < sizeOf sender + sizeOf receiver
          have h3 : 1 + sizeOf branches < sizeOf (GlobalType.comm sender receiver branches) := by
            simp only [GlobalType.comm.sizeOf_spec]
            -- Need: 0 < sizeOf sender + sizeOf receiver
            -- For String s, sizeOf s = 1 + sizeOf s.bytes + sizeOf s.isValidUTF8 ≥ 1
            have hs : 0 < sizeOf sender := by
              have : sizeOf sender = 1 + sizeOf sender.bytes + sizeOf sender.isValidUTF8 := rfl
              omega
            have hr : 0 < sizeOf receiver := by
              have : sizeOf receiver = 1 + sizeOf receiver.bytes + sizeOf receiver.isValidUTF8 := rfl
              omega
            omega
          have h4 : sizeOf p.2 < sizeOf (GlobalType.comm sender receiver branches) := by omega
          exact Nat.lt_of_lt_of_le h4 hsize
        -- Build the induction hypothesis for the helper
        have ih' : ∀ g' : GlobalType, sizeOf g' < n →
              ∀ v', v' ∈ (g'.substitute t repl).freeVars →
              (v' ∈ g'.freeVars ∧ v' ≠ t) ∨ v' ∈ repl.freeVars := by
          intro g' hg' v' hv'
          exact ih (sizeOf g') hg' g' (Nat.le_refl _) t repl v' hv'
        have hsub := freeVars_substituteBranches_subset_aux ih' branches hbranch_sizes v hv
        cases hsub with
        | inl hcase =>
            left
            simp only [GlobalType.freeVars]
            exact hcase
        | inr hmem =>
            right
            exact hmem

/-- Main theorem: free vars of substituted type are bounded. -/
theorem freeVars_substitute_subset (body : GlobalType) (t : String) (repl : GlobalType)
    (v : String) (hv : v ∈ (body.substitute t repl).freeVars) :
    (v ∈ body.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars :=
  freeVars_substitute_subset_strong (sizeOf body) body (Nat.le_refl _) t repl v hv

/-- Corollary for branches: free vars of substituted branches are bounded. -/
theorem freeVars_substituteBranches_subset (branches : List (Label × GlobalType))
    (t : String) (repl : GlobalType) (v : String)
    (hv : v ∈ freeVarsOfBranches (substituteBranches branches t repl)) :
    (v ∈ freeVarsOfBranches branches ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  match branches with
  | [] =>
      simp only [substituteBranches, freeVarsOfBranches, List.not_mem_nil] at hv
  | hd :: tl =>
      simp only [substituteBranches, freeVarsOfBranches, List.mem_append] at hv
      cases hv with
      | inl hv_hd =>
          have hsub := freeVars_substitute_subset hd.2 t repl v hv_hd
          cases hsub with
          | inl hcase =>
              left
              simp only [freeVarsOfBranches, List.mem_append]
              exact ⟨Or.inl hcase.1, hcase.2⟩
          | inr hmem =>
              right
              exact hmem
      | inr hv_tl =>
          have hsub := freeVars_substituteBranches_subset tl t repl v hv_tl
          cases hsub with
          | inl hcase =>
              left
              simp only [freeVarsOfBranches, List.mem_append]
              exact ⟨Or.inr hcase.1, hcase.2⟩
          | inr hmem =>
              right
              exact hmem

/-- Substitution preserves closedness when both repl is closed AND body has no free vars other than t.

This is the precise property needed for mu-unfolding: if `(mu t body).isClosed`, then:
1. `repl = mu t body` is closed
2. `body.freeVars ⊆ [t]` (body has no free vars other than t)
Therefore `(body.substitute t repl).isClosed`.

**Coq reference:** Follows from `gType_fv_subst` in `coGlobal.v`. -/
theorem GlobalType.isClosed_substitute_of_closed' (body : GlobalType) (t : String) (repl : GlobalType)
    (hrepl_closed : repl.isClosed = true)
    (hbody_only_t : ∀ v ∈ body.freeVars, v = t) :
    (body.substitute t repl).isClosed = true := by
  simp only [GlobalType.isClosed, List.isEmpty_iff]
  simp only [GlobalType.isClosed, List.isEmpty_iff] at hrepl_closed
  by_contra hne
  have ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
  have hsub := freeVars_substitute_subset body t repl v hv
  cases hsub with
  | inl h =>
      -- v is in body.freeVars and v ≠ t
      -- But hbody_only_t says all vars in body.freeVars equal t
      -- Contradiction!
      have heq := hbody_only_t v h.1
      exact h.2 heq
  | inr hmem =>
      simp only [hrepl_closed, List.not_mem_nil] at hmem

/-- Mu type closedness implies body has only the bound variable free.

If `(mu t body).isClosed = true`, then `body.freeVars ⊆ [t]`. -/
theorem GlobalType.isClosed_mu_body_freeVars (t : String) (body : GlobalType)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    ∀ v ∈ body.freeVars, v = t := by
  simp only [GlobalType.isClosed, GlobalType.freeVars, List.isEmpty_iff] at hclosed
  intro v hv
  -- hclosed : body.freeVars.filter (· != t) = []
  -- hv : v ∈ body.freeVars
  -- Goal: v = t
  by_contra hne
  have hfilter : v ∈ body.freeVars.filter (fun x => x != t) := by
    simp only [List.mem_filter, bne_iff_ne]
    exact ⟨hv, hne⟩
  simp only [hclosed, List.not_mem_nil] at hfilter

/-- Mu-unfolding preserves closedness: if `(mu t body).isClosed`, then `(body.substitute t (mu t body)).isClosed`.

This is the key property needed for the mu case in step induction.
It combines:
1. `(mu t body).isClosed` → `mu t body` has no free vars
2. `(mu t body).isClosed` → body has only `t` as free var (`isClosed_mu_body_freeVars`)
3. Substitution doesn't add free vars beyond repl's vars (`isClosed_substitute_of_closed'`)

**Coq reference:** Follows from `gType_fv_subst` in `coGlobal.v`. -/
theorem GlobalType.isClosed_substitute_mu (t : String) (body : GlobalType)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    (body.substitute t (GlobalType.mu t body)).isClosed = true := by
  apply isClosed_substitute_of_closed' body t (.mu t body) hclosed
  exact isClosed_mu_body_freeVars t body hclosed

/-! ## Unfolding for GlobalType (Coq-style `full_unf`)

These helpers mirror LocalTypeR.fullUnfold and are used by the unfolding-
insensitive projection refactor (CProjectU). -/

/-- Unfold one level of recursion: μt.G ↦ G[μt.G/t]. -/
def GlobalType.unfold : GlobalType → GlobalType
  | g@(.mu t body) => body.substitute t g
  | g => g

/-- Height of leading mu binders. -/
def GlobalType.muHeight : GlobalType → Nat
  | .mu _ body => 1 + body.muHeight
  | _ => 0

/-- Fully unfold a global type by iterating unfold until non-mu form. -/
partial def GlobalType.fullUnfold (g : GlobalType) : GlobalType :=
  match g.muHeight with
  | 0 => g
  | _ => (g.unfold).fullUnfold

/-- Fully unfold a global type by iterating `unfold` exactly `muHeight` times.
    This matches the Coq `full_unf` definition used in the reference proofs. -/
def GlobalType.fullUnfoldIter (g : GlobalType) : GlobalType :=
  Nat.rec (motive := fun _ => GlobalType) g
    (fun _ acc => GlobalType.unfold acc) g.muHeight

end RumpsteakV2.Protocol.GlobalType
