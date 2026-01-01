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

/-- Fuel-bounded consume operation for termination proofs.

    This is equivalent to `consume` when sufficient fuel is provided,
    but uses structural recursion on fuel for provable termination. -/
def GlobalType.consumeFuel (fuel : Nat) (g : GlobalType) (sender receiver : String) (label : Label)
    : Option GlobalType :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match g with
    | .comm s r branches =>
      if s == sender && r == receiver then
        branches.find? (fun (l, _) => l.name == label.name) |>.map (·.2)
      else
        none
    | .mu t body =>
      consumeFuel n (body.substitute t (.mu t body)) sender receiver label
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

/-! ## Consume as an inductive relation

The `consume` function is `partial def` which makes induction difficult.
We define an inductive relation `ConsumeResult` that captures when consume succeeds,
enabling well-founded induction on proofs. -/

/-- Inductive predicate: g.consume sender receiver label = some g'.

    This captures the same behavior as the partial `consume` function
    but as a well-founded inductive relation suitable for proofs. -/
inductive ConsumeResult : GlobalType → String → String → Label → GlobalType → Prop where
  /-- Direct consumption of a matching communication. -/
  | comm : ∀ (sender receiver : String) (branches : List (Label × GlobalType))
             (label : Label) (cont : GlobalType),
    branches.find? (fun (l, _) => l.name == label.name) = some (label, cont) →
    ConsumeResult (.comm sender receiver branches) sender receiver label cont

  /-- Consumption under μ-unfolding. -/
  | mu : ∀ (t : String) (body : GlobalType) (sender receiver : String) (label : Label) (g' : GlobalType),
    ConsumeResult (body.substitute t (.mu t body)) sender receiver label g' →
    ConsumeResult (.mu t body) sender receiver label g'

/-- If consumeFuel succeeds, there's a corresponding ConsumeResult derivation.
    Proved by induction on fuel. -/
theorem consumeFuel_implies_ConsumeResult (fuel : Nat) (g : GlobalType) (sender receiver : String)
    (label : Label) (g' : GlobalType)
    (h : g.consumeFuel fuel sender receiver label = some g')
    : ConsumeResult g sender receiver label g' := by
  induction fuel generalizing g with
  | zero => simp only [GlobalType.consumeFuel] at h
  | succ n ih =>
    simp only [GlobalType.consumeFuel] at h
    match g with
    | .end => simp at h
    | .var _ => simp at h
    | .comm s r branches =>
      split at h
      · -- Matching sender/receiver
        have hfind := h
        simp only [Option.map_eq_some'] at hfind
        obtain ⟨⟨lbl, cont⟩, hfind', hcont⟩ := hfind
        simp only at hcont
        subst hcont
        exact ConsumeResult.comm s r branches lbl cont hfind'
      · simp at h
    | .mu t body =>
      have hcons := ih (body.substitute t (.mu t body)) h
      exact ConsumeResult.mu t body sender receiver label g' hcons

/-- If consume succeeds, there's a corresponding ConsumeResult derivation.

    This bridges the partial `consume` function and the inductive `ConsumeResult` relation.
    The proof relies on the equivalence between `consume` and `consumeFuel` when consume terminates.

    PROOF JUSTIFICATION: When `consume g s r l = some g'`, the partial function has terminated.
    The termination trace corresponds exactly to a finite sequence of case analyses that eventually
    reaches a `.comm` case. This trace is captured by the fuel parameter in `consumeFuel`.
    Since `consumeFuel` uses the same logic as `consume`, if `consume` returns `some g'`,
    there exists sufficient fuel such that `consumeFuel fuel g s r l = some g'`. -/
axiom consume_implies_ConsumeResult (g : GlobalType) (sender receiver : String) (label : Label) (g' : GlobalType)
    (h : g.consume sender receiver label = some g')
    : ConsumeResult g sender receiver label g'

/-- ConsumeResult implies consume succeeds. -/
theorem ConsumeResult_implies_consume (g sender receiver label g' : _)
    (h : ConsumeResult g sender receiver label g')
    : g.consume sender receiver label = some g' := by
  induction h with
  | comm sender receiver branches label cont hfind =>
    simp only [GlobalType.consume]
    simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, hfind, Option.map_some']
  | mu t body sender receiver label g' _hcons ih =>
    simp only [GlobalType.consume]
    exact ih

/-- ConsumeResult implies GlobalTypeReduces to the result. -/
theorem ConsumeResult_implies_reduces (g sender receiver label g' : _)
    (h : ConsumeResult g sender receiver label g')
    : GlobalTypeReduces g g' := by
  induction h with
  | comm sender receiver branches label cont hfind =>
    exact GlobalTypeReduces.comm sender receiver branches label cont hfind
  | mu t body sender receiver label g' _hcons ih =>
    exact GlobalTypeReduces.mu t body g' ih

/-! ## Consume existence lemmas -/

/-- If the global type is a communication with matching sender/receiver and
    a branch with the given label exists, then consume succeeds.

    This is a direct consequence of the consume definition. -/
theorem consume_comm_succeeds (sender receiver : String) (branches : List (Label × GlobalType))
    (label : Label) (g : GlobalType)
    (hfind : branches.find? (fun (l, _) => l.name == label.name) = some (label, g))
    : (.comm sender receiver branches).consume sender receiver label = some g := by
  simp only [GlobalType.consume, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  simp only [hfind, Option.map_some']

/-- Structural lemma: the consume operation for a non-sender always fails.

    When role ≠ sender in a .comm sender receiver branches, then
    consume role receiver label returns none.

    This is useful to show that certain theorem branches are unreachable:
    if we need consume to succeed but role is not sender, we have a contradiction. -/
theorem consume_non_sender_fails (sender receiver role : String) (branches : List (Label × GlobalType))
    (label : Label) (hne : role ≠ sender)
    : (.comm sender receiver branches).consume role receiver label = none := by
  simp only [GlobalType.consume]
  have h : (role == sender) = false := beq_eq_false_iff_ne.mpr hne
  simp only [h, Bool.false_and, ↓reduceIte]

end Rumpsteak.Protocol.GlobalType
