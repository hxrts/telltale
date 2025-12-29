import Rumpsteak.Protocol.GlobalType

/-! # Rumpsteak.Protocol.LocalTypeR

Recursive local types for per-role protocol views.

## Overview

This module defines local types that describe protocols from a single participant's
perspective. Local types are obtained by projecting global types onto specific roles.
They support recursion, internal choice (send/select), and external choice (recv/branch).

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Expose

The following definitions form the semantic interface for proofs:

- `LocalTypeR`: Recursive local type with end, send, recv, mu, var constructors
- `LocalTypeR.dual`: Compute the dual of a local type (swap send/recv)
- `LocalTypeR.unfold`: Unfold one level of recursion
- `LocalTypeR.freeVars`: Extract free type variables
- `LocalTypeR.substitute`: Substitute a type for a variable

## Main Definitions

- `LocalTypeR` - Inductive type for local protocol views
- Duality and substitution operations
- Well-formedness predicates
-/

namespace Rumpsteak.Protocol.LocalTypeR

open Rumpsteak.Protocol.GlobalType (PayloadSort Label)

/-- Local types describe protocols from a single participant's view.

    Syntax:
    - `end`: Protocol termination
    - `send q branches`: Internal choice - send to q with labeled branches
    - `recv p branches`: External choice - receive from p with labeled branches
    - `mu t T`: Recursive type μt.T
    - `var t`: Type variable reference

    Internal choice (!q{lᵢ.Tᵢ}) means the role selects which branch to take.
    External choice (?p{lᵢ.Tᵢ}) means the role waits for p to decide. -/
inductive LocalTypeR where
  /-- Protocol termination -/
  | end : LocalTypeR
  /-- Internal choice: send to partner with choice of continuations -/
  | send : String → List (Label × LocalTypeR) → LocalTypeR
  /-- External choice: receive from partner with offered continuations -/
  | recv : String → List (Label × LocalTypeR) → LocalTypeR
  /-- Recursive type: μt.T binds variable t in body T -/
  | mu : String → LocalTypeR → LocalTypeR
  /-- Type variable: reference to enclosing μ-binder -/
  | var : String → LocalTypeR
deriving Repr, Inhabited

/-- Extract free type variables from a local type. -/
partial def LocalTypeR.freeVars : LocalTypeR → List String
  | .end => []
  | .send _ branches => branches.flatMap fun (_, t) => t.freeVars
  | .recv _ branches => branches.flatMap fun (_, t) => t.freeVars
  | .mu t body => body.freeVars.filter (· != t)
  | .var t => [t]

/-- Substitute a local type for a variable. -/
partial def LocalTypeR.substitute (lt : LocalTypeR) (varName : String) (replacement : LocalTypeR) : LocalTypeR :=
  match lt with
  | .end => .end
  | .send partner branches =>
    .send partner (branches.map fun (l, cont) => (l, cont.substitute varName replacement))
  | .recv partner branches =>
    .recv partner (branches.map fun (l, cont) => (l, cont.substitute varName replacement))
  | .mu t body =>
    if t == varName then
      -- Variable is shadowed by this binder
      .mu t body
    else
      .mu t (body.substitute varName replacement)
  | .var t =>
    if t == varName then replacement else .var t

/-- Unfold one level of recursion: μt.T ↦ T[μt.T/t] -/
partial def LocalTypeR.unfold : LocalTypeR → LocalTypeR
  | lt@(.mu t body) => body.substitute t lt
  | lt => lt

/-- Compute the dual of a local type (swap send/recv).
    The dual of role A's view is role B's view when A and B are the only participants. -/
partial def LocalTypeR.dual : LocalTypeR → LocalTypeR
  | .end => .end
  | .send partner branches =>
    .recv partner (branches.map fun (l, cont) => (l, cont.dual))
  | .recv partner branches =>
    .send partner (branches.map fun (l, cont) => (l, cont.dual))
  | .mu t body => .mu t body.dual
  | .var t => .var t

/-- Check if all recursion variables are bound. -/
partial def LocalTypeR.allVarsBound (lt : LocalTypeR) (bound : List String := []) : Bool :=
  match lt with
  | .end => true
  | .send _ branches => branches.all fun (_, cont) => cont.allVarsBound bound
  | .recv _ branches => branches.all fun (_, cont) => cont.allVarsBound bound
  | .mu t body => body.allVarsBound (t :: bound)
  | .var t => bound.contains t

/-- Check if each choice has at least one branch. -/
partial def LocalTypeR.allChoicesNonEmpty : LocalTypeR → Bool
  | .end => true
  | .send _ branches => !branches.isEmpty && branches.all fun (_, cont) => cont.allChoicesNonEmpty
  | .recv _ branches => !branches.isEmpty && branches.all fun (_, cont) => cont.allChoicesNonEmpty
  | .mu _ body => body.allChoicesNonEmpty
  | .var _ => true

/-- Well-formedness predicate for local types.
    A local type is well-formed if:
    1. All recursion variables are bound
    2. Each choice has at least one branch -/
def LocalTypeR.wellFormed (lt : LocalTypeR) : Bool :=
  lt.allVarsBound && lt.allChoicesNonEmpty

/-- Count the depth of a local type (for termination proofs). -/
partial def LocalTypeR.depth : LocalTypeR → Nat
  | .end => 0
  | .send _ branches => 1 + (branches.map fun (_, t) => t.depth).foldl max 0
  | .recv _ branches => 1 + (branches.map fun (_, t) => t.depth).foldl max 0
  | .mu _ body => 1 + body.depth
  | .var _ => 0

/-- Check if a local type is guarded (no immediate recursion). -/
partial def LocalTypeR.isGuarded : LocalTypeR → Bool
  | .end => true
  | .send _ branches => branches.all fun (_, cont) => cont.isGuarded
  | .recv _ branches => branches.all fun (_, cont) => cont.isGuarded
  | .mu _ body =>
    match body with
    | .var _ => false  -- Immediately recursive without guard
    | .mu _ _ => false  -- Nested recursion without guard
    | _ => body.isGuarded
  | .var _ => true

/-- Extract all labels from a local type. -/
partial def LocalTypeR.labels : LocalTypeR → List String
  | .end => []
  | .send _ branches => branches.map fun (l, _) => l.name
  | .recv _ branches => branches.map fun (l, _) => l.name
  | .mu _ body => body.labels
  | .var _ => []

/-- Extract all partners from a local type. -/
partial def LocalTypeR.partners : LocalTypeR → List String
  | .end => []
  | .send partner branches =>
    let branchPartners := branches.flatMap fun (_, t) => t.partners
    (partner :: branchPartners).eraseDups
  | .recv partner branches =>
    let branchPartners := branches.flatMap fun (_, t) => t.partners
    (partner :: branchPartners).eraseDups
  | .mu _ body => body.partners
  | .var _ => []

end Rumpsteak.Protocol.LocalTypeR
