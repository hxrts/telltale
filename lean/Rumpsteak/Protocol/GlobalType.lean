/-! # Rumpsteak.Protocol.GlobalType

Recursive global types for multiparty session type protocols.

## Overview

This module defines global types that describe protocols from a bird's-eye view.
Global types specify the complete interaction pattern between all participants,
including message exchanges, choices, and recursive behavior.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Expose

The following definitions form the semantic interface for proofs:

- `PayloadSort`: Payload types for messages (unit, nat, bool, string, products)
- `Label`: Message label with associated payload sort
- `GlobalType`: Recursive global type with end, comm, mu, var constructors
- `GlobalType.wellFormed`: Well-formedness predicate
- `GlobalType.roles`: Extract all participating roles
- `GlobalType.freeVars`: Extract free type variables
- `GlobalType.substitute`: Substitute a type for a variable

## Main Definitions

- `PayloadSort` - Inductive type for message payloads
- `Label` - Structure pairing label name with payload sort
- `GlobalType` - Inductive type for global protocol specifications
- Well-formedness and utility functions
-/

namespace Rumpsteak.Protocol.GlobalType

/-- Payload sort types for message payloads.
    These represent the data types that can be sent in messages. -/
inductive PayloadSort where
  /-- Unit type (no payload) -/
  | unit : PayloadSort
  /-- Natural numbers -/
  | nat : PayloadSort
  /-- Booleans -/
  | bool : PayloadSort
  /-- Strings -/
  | string : PayloadSort
  /-- Product types (pairs) -/
  | prod : PayloadSort → PayloadSort → PayloadSort
deriving Repr, DecidableEq, BEq, Inhabited

/-- A message label with its payload sort.
    Labels identify message types in communications. -/
structure Label where
  /-- The label name identifying this message type -/
  name : String
  /-- The payload sort for this message -/
  sort : PayloadSort := PayloadSort.unit
deriving Repr, DecidableEq, BEq, Inhabited

/-- Global types describe protocols from the bird's-eye view.

    Syntax:
    - `end`: Protocol termination
    - `comm p q branches`: Communication p → q with labeled branches
    - `mu t G`: Recursive type μt.G
    - `var t`: Type variable reference

    The `comm` constructor models `p → q : {l₁(S₁).G₁, l₂(S₂).G₂, ...}`
    where the sender p chooses which branch to take. -/
inductive GlobalType where
  /-- Protocol termination -/
  | end : GlobalType
  /-- Communication: sender → receiver with choice of labeled continuations -/
  | comm : String → String → List (Label × GlobalType) → GlobalType
  /-- Recursive type: μt.G binds variable t in body G -/
  | mu : String → GlobalType → GlobalType
  /-- Type variable: reference to enclosing μ-binder -/
  | var : String → GlobalType
deriving Repr, Inhabited

/-- Extract all role names from a global type. -/
partial def GlobalType.roles : GlobalType → List String
  | .end => []
  | .comm sender receiver branches =>
    let branchRoles := branches.flatMap fun (_, g) => g.roles
    ([sender, receiver] ++ branchRoles).eraseDups
  | .mu _ body => body.roles
  | .var _ => []

/-- Extract free type variables from a global type. -/
partial def GlobalType.freeVars : GlobalType → List String
  | .end => []
  | .comm _ _ branches => branches.flatMap fun (_, g) => g.freeVars
  | .mu t body => body.freeVars.filter (· != t)
  | .var t => [t]

/-- Substitute a global type for a variable. -/
partial def GlobalType.substitute (g : GlobalType) (varName : String) (replacement : GlobalType) : GlobalType :=
  match g with
  | .end => .end
  | .comm sender receiver branches =>
    .comm sender receiver (branches.map fun (l, cont) => (l, cont.substitute varName replacement))
  | .mu t body =>
    if t == varName then
      -- Variable is shadowed by this binder
      .mu t body
    else
      .mu t (body.substitute varName replacement)
  | .var t =>
    if t == varName then replacement else .var t

/-- Check if all recursion variables are bound. -/
partial def GlobalType.allVarsBound (g : GlobalType) (bound : List String := []) : Bool :=
  match g with
  | .end => true
  | .comm _ _ branches => branches.all fun (_, cont) => cont.allVarsBound bound
  | .mu t body => body.allVarsBound (t :: bound)
  | .var t => bound.contains t

/-- Check if each communication has at least one branch. -/
partial def GlobalType.allCommsNonEmpty : GlobalType → Bool
  | .end => true
  | .comm _ _ branches => !branches.isEmpty && branches.all fun (_, cont) => cont.allCommsNonEmpty
  | .mu _ body => body.allCommsNonEmpty
  | .var _ => true

/-- Check if sender and receiver are different in each communication. -/
partial def GlobalType.noSelfComm : GlobalType → Bool
  | .end => true
  | .comm sender receiver branches =>
    sender != receiver && branches.all fun (_, cont) => cont.noSelfComm
  | .mu _ body => body.noSelfComm
  | .var _ => true

/-- Well-formedness predicate for global types.
    A global type is well-formed if:
    1. All recursion variables are bound
    2. Each communication has at least one branch
    3. Sender ≠ receiver in each communication -/
def GlobalType.wellFormed (g : GlobalType) : Bool :=
  g.allVarsBound && g.allCommsNonEmpty && g.noSelfComm

/-- Check if a role participates in the global type. -/
def GlobalType.mentionsRole (g : GlobalType) (role : String) : Bool :=
  g.roles.contains role

/-- Count the depth of a global type (for termination proofs). -/
partial def GlobalType.depth : GlobalType → Nat
  | .end => 0
  | .comm _ _ branches =>
    1 + (branches.map fun (_, g) => g.depth).foldl max 0
  | .mu _ body => 1 + body.depth
  | .var _ => 0

/-- Unfold one level of recursion: μt.G ↦ G[μt.G/t] -/
def GlobalType.unfold : GlobalType → GlobalType
  | g@(.mu t body) => body.substitute t g
  | g => g

/-- Check if a global type is guarded (no immediate recursion without communication). -/
partial def GlobalType.isGuarded : GlobalType → Bool
  | .end => true
  | .comm _ _ branches => branches.all fun (_, cont) => cont.isGuarded
  | .mu _ body =>
    match body with
    | .var _ => false  -- Immediately recursive without guard
    | .mu _ _ => false  -- Nested recursion without guard
    | _ => body.isGuarded
  | .var _ => true

/-! ## Global Type Consumption and Reduction

Based on Definition 7 from "A Very Gentle Introduction to Multiparty Session Types".
These operations formalize how global types evolve during protocol execution. -/

/-- Consume a communication from a global type.

    G \ p →ℓ q represents the global type after the communication p →ℓ q
    has been performed. This operation is essential for subject reduction.

    Definition 7 (Yoshida & Gheri):
    - (p → q : {ℓᵢ(Sᵢ).Gᵢ}) \ p →ℓⱼ q = Gⱼ
    - (μt.G) \ p →ℓ q = (G[μt.G/t]) \ p →ℓ q
    - For other cases where p →ℓ q is not at the head, consumption is undefined -/
partial def GlobalType.consume (g : GlobalType) (sender receiver : String) (label : Label)
    : Option GlobalType :=
  match g with
  | .comm s r branches =>
    if s == sender && r == receiver then
      -- Find the branch matching the label
      branches.find? (fun (l, _) => l.name == label.name) |>.map (·.2)
    else
      none  -- Communication doesn't match
  | .mu t body =>
    -- Unfold and try again
    (body.substitute t (.mu t body)).consume sender receiver label
  | _ => none

/-- Global type reduction relation.

    G ⟹ G' means G can reduce to G' by performing one communication.
    This is the type-level analog of process reduction.

    Based on the reduction rules in "A Very Gentle Introduction":
    - G = p → q : {ℓᵢ(Sᵢ).Gᵢ} reduces to Gⱼ when p sends ℓⱼ to q
    - Recursion unfolds: μt.G ⟹ G[μt.G/t] ⟹ ... -/
inductive GlobalTypeReduces : GlobalType → GlobalType → Prop where
  /-- Direct communication reduction -/
  | comm : ∀ (sender receiver : String) (branches : List (Label × GlobalType))
             (label : Label) (cont : GlobalType),
    branches.find? (fun (l, _) => l.name == label.name) = some (label, cont) →
    GlobalTypeReduces (.comm sender receiver branches) cont

  /-- Reduction under recursion unfold -/
  | mu : ∀ (t : String) (body : GlobalType) (g' : GlobalType),
    GlobalTypeReduces (body.substitute t (.mu t body)) g' →
    GlobalTypeReduces (.mu t body) g'

/-- Reflexive-transitive closure of global type reduction. -/
inductive GlobalTypeReducesStar : GlobalType → GlobalType → Prop where
  | refl : ∀ g, GlobalTypeReducesStar g g
  | step : ∀ g1 g2 g3, GlobalTypeReduces g1 g2 → GlobalTypeReducesStar g2 g3 →
           GlobalTypeReducesStar g1 g3

/-- Notation for global type reduction -/
scoped infix:50 " ⟹ " => GlobalTypeReduces
scoped infix:50 " ⟹* " => GlobalTypeReducesStar

end Rumpsteak.Protocol.GlobalType
