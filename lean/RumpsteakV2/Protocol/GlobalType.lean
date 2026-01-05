import Mathlib.Data.List.Basic

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

end RumpsteakV2.Protocol.GlobalType
