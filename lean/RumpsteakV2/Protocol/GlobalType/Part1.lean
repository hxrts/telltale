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

/-! ## Core Syntax -/

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

/-! ## Roles and Free Variables -/

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

/-! ## Substitution -/

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

/-! ## Well-Formedness Predicates -/

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

/-! ## Branch Labels and Uniqueness -/

/-- Extract labels from a list of branches. -/
def branchLabels (branches : List (Label × GlobalType)) : List Label :=
  branches.map Prod.fst

private theorem label_mem_branchLabels_of_mem {label : Label} {cont : GlobalType}
    {branches : List (Label × GlobalType)} (hmem : (label, cont) ∈ branches) :
    label ∈ branchLabels branches := by
  -- Lift pair membership into label membership.
  simpa [branchLabels] using
    (List.mem_map (f := Prod.fst) (l := branches) (b := label)).2 ⟨(label, cont), hmem, rfl⟩

private theorem mem_branch_unique_label_head
    {head : Label × GlobalType} {rest : List (Label × GlobalType)}
    {label : Label} {cont cont' : GlobalType}
    (hnotmem : head.1 ∉ branchLabels rest)
    (hhead : head = (label, cont))
    (hmem : (label, cont') ∈ head :: rest) :
    cont = cont' := by
  -- If the duplicate label appears in the head, the other must be the same pair.
  have hmem' := (List.mem_cons).1 hmem
  cases hmem' with
  | inl hEq =>
      have hpair : (label, cont') = (label, cont) := by simpa [hhead] using hEq
      cases hpair
      rfl
  | inr hmem_tail =>
      have hlabel : label ∈ branchLabels rest := label_mem_branchLabels_of_mem hmem_tail
      have hbad : head.1 ∈ branchLabels rest := by simpa [hhead] using hlabel
      exact (hnotmem hbad).elim

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
      -- Reduce to head/tail cases using Nodup on labels.
      have huniq' : head.1 ∉ branchLabels tail ∧ (branchLabels tail).Nodup := by
        simpa [branchLabels] using (List.nodup_cons.mp huniq)
      have hnotmem := huniq'.1
      have htail := huniq'.2
      simp only [List.mem_cons] at hmem1 hmem2
      cases hmem1 with
      | inl hhead1 =>
          have hmem2' : (label, cont') ∈ head :: tail := by
            simpa [List.mem_cons] using hmem2
          exact mem_branch_unique_label_head hnotmem hhead1.symm hmem2'
      | inr htail1 =>
          cases hmem2 with
          | inl hhead2 =>
              have hmem1' : (label, cont) ∈ head :: tail := List.mem_cons_of_mem _ htail1
              exact (mem_branch_unique_label_head hnotmem hhead2.symm hmem1').symm
          | inr htail2 =>
              exact ih htail htail1 htail2

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

end RumpsteakV2.Protocol.GlobalType
