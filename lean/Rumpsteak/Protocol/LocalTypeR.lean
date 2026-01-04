import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.Core

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
open Rumpsteak.Protocol.Core (LocalKind)

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

/-! ## Termination Helpers for LocalTypeR -/

private theorem sizeOf_snd_lt_prod_local {α : Type} [SizeOf α] (a : α) (b : LocalTypeR) :
    sizeOf b < sizeOf (a, b) := by
  simp only [sizeOf, Prod._sizeOf_1]
  omega

private theorem sizeOf_head_lt_cons_local {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf x < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_tail_lt_cons_local {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_mem_snd_lt_local {bs : List (Label × LocalTypeR)} {pair : Label × LocalTypeR}
    (hmem : pair ∈ bs) : sizeOf pair.2 < sizeOf bs := by
  induction bs with
  | nil => cases hmem
  | cons hd tl ih =>
    cases hmem with
    | head =>
      have h1 : sizeOf pair.2 < sizeOf pair := sizeOf_snd_lt_prod_local pair.1 pair.2
      have h2 : sizeOf pair < sizeOf (pair :: tl) := sizeOf_head_lt_cons_local pair tl
      exact Nat.lt_trans h1 h2
    | tail _ hmem' =>
      have h1 := ih hmem'
      have h2 : sizeOf tl < sizeOf (hd :: tl) := sizeOf_tail_lt_cons_local hd tl
      exact Nat.lt_trans h1 h2

private theorem sizeOf_bs_lt_send_local (p : String) (bs : List (Label × LocalTypeR)) :
    sizeOf bs < sizeOf (LocalTypeR.send p bs) := by
  simp only [LocalTypeR.send.sizeOf_spec]
  omega

private theorem sizeOf_bs_lt_recv_local (p : String) (bs : List (Label × LocalTypeR)) :
    sizeOf bs < sizeOf (LocalTypeR.recv p bs) := by
  simp only [LocalTypeR.recv.sizeOf_spec]
  omega

private theorem sizeOf_body_lt_mu_local (v : String) (body : LocalTypeR) :
    sizeOf body < sizeOf (LocalTypeR.mu v body) := by
  simp only [LocalTypeR.mu.sizeOf_spec]
  omega

/-- Substitute a local type for a variable. -/
def LocalTypeR.substitute (lt : LocalTypeR) (varName : String) (replacement : LocalTypeR) : LocalTypeR :=
  match lt with
  | .end => .end
  | .send partner branches =>
    .send partner (branches.attach.map fun ⟨(l, cont), hmem⟩ =>
      have _h : sizeOf cont < 1 + sizeOf partner + sizeOf branches := by
        have h1 : sizeOf cont < sizeOf branches := sizeOf_mem_snd_lt_local hmem
        omega
      (l, cont.substitute varName replacement))
  | .recv partner branches =>
    .recv partner (branches.attach.map fun ⟨(l, cont), hmem⟩ =>
      have _h : sizeOf cont < 1 + sizeOf partner + sizeOf branches := by
        have h1 : sizeOf cont < sizeOf branches := sizeOf_mem_snd_lt_local hmem
        omega
      (l, cont.substitute varName replacement))
  | .mu t body =>
    if t == varName then
      -- Variable is shadowed by this binder
      .mu t body
    else
      .mu t (body.substitute varName replacement)
  | .var t =>
    if t == varName then replacement else .var t
termination_by sizeOf lt

/-- Unfold one level of recursion: μt.T ↦ T[μt.T/t] -/
partial def LocalTypeR.unfold : LocalTypeR → LocalTypeR
  | lt@(.mu t body) => body.substitute t lt
  | lt => lt

/-! ## Substitute Specification Theorems

Now that `substitute` is a total function, we can prove its behavior on each constructor. -/

/-- Helper: attach.map with function extracting element equals map with that function. -/
private theorem attach_map_eq_map_local {α β : Type} (l : List α) (f : α → β) :
    l.attach.map (fun ⟨x, _⟩ => f x) = l.map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [List.attach, List.map, ih]

/-- Substitute on end yields end. -/
@[simp] theorem LocalTypeR.substitute_end (t : String) (repl : LocalTypeR) :
    LocalTypeR.substitute .end t repl = .end := by
  unfold substitute
  rfl

/-- Substitute on matching variable yields replacement. -/
@[simp] theorem LocalTypeR.substitute_var_eq (t : String) (repl : LocalTypeR) :
    LocalTypeR.substitute (.var t) t repl = repl := by
  simp only [substitute, beq_self_eq_true, ↓reduceIte]

/-- Substitute on non-matching variable yields the variable unchanged. -/
@[simp] theorem LocalTypeR.substitute_var_ne {s t : String} (hne : s ≠ t) (repl : LocalTypeR) :
    LocalTypeR.substitute (.var s) t repl = .var s := by
  simp only [substitute, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte]

/-- Substitute on send maps over branches. -/
theorem LocalTypeR.substitute_send (partner t : String) (branches : List (Label × LocalTypeR))
    (repl : LocalTypeR) :
    LocalTypeR.substitute (.send partner branches) t repl =
      .send partner (branches.map fun (l, lt) => (l, lt.substitute t repl)) := by
  simp only [substitute]
  congr 1
  exact attach_map_eq_map_local branches fun (l, cont) => (l, cont.substitute t repl)

/-- Substitute on recv maps over branches. -/
theorem LocalTypeR.substitute_recv (partner t : String) (branches : List (Label × LocalTypeR))
    (repl : LocalTypeR) :
    LocalTypeR.substitute (.recv partner branches) t repl =
      .recv partner (branches.map fun (l, lt) => (l, lt.substitute t repl)) := by
  simp only [substitute]
  congr 1
  exact attach_map_eq_map_local branches fun (l, cont) => (l, cont.substitute t repl)

/-- Substitute on mu when variable is shadowed (same name) yields mu unchanged. -/
@[simp] theorem LocalTypeR.substitute_mu_shadow (t : String) (body repl : LocalTypeR) :
    LocalTypeR.substitute (.mu t body) t repl = .mu t body := by
  simp only [substitute, beq_self_eq_true, ↓reduceIte]

/-- Substitute on mu when variable is not shadowed recurses into body. -/
theorem LocalTypeR.substitute_mu_ne {s t : String} (hne : s ≠ t) (body repl : LocalTypeR) :
    LocalTypeR.substitute (.mu s body) t repl = .mu s (body.substitute t repl) := by
  simp only [substitute, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte]

/-- Substitution of a non-variable into a local type that isn't .end or a matching variable
    produces a non-.end result. More precisely: if lt ≠ .end and lt isn't a matching var,
    then lt.substitute t repl ≠ .end. -/
theorem LocalTypeR.substitute_non_end_non_var {lt : LocalTypeR} {t : String} {repl : LocalTypeR}
    (hne : lt ≠ .end)
    (hvar : ∀ v, lt = .var v → v ≠ t)
    : lt.substitute t repl ≠ .end := by
  cases lt with
  | «end» => exact absurd rfl hne
  | var v =>
    by_cases hv : v = t
    · -- v = t: substitute gives repl, and we need repl ≠ .end
      -- But hvar says v ≠ t, contradiction
      exact absurd hv (hvar v rfl)
    · -- v ≠ t: substitute gives .var v ≠ .end
      simp only [substitute_var_ne hv repl]
      intro h; cases h
  | send partner branches =>
    simp only [substitute_send]
    intro h; cases h
  | recv partner branches =>
    simp only [substitute_recv]
    intro h; cases h
  | mu s body =>
    by_cases hs : s = t
    · -- Shadowed: substitute gives .mu s body ≠ .end
      subst hs
      simp only [substitute_mu_shadow]
      intro h; cases h
    · -- Not shadowed: substitute gives .mu s (body.substitute t repl) ≠ .end
      simp only [substitute_mu_ne hs]
      intro h; cases h

/-- For well-formed recursive types, if projBody came from projecting a mu body and is non-.end,
    then substituting into projBody preserves the non-.end property when the replacement type
    respects the guardedness structure. This captures the equi-recursive typing property. -/
theorem LocalTypeR.mu_proj_substitute_non_end {projBody : LocalTypeR} {t : String} {rlt : LocalTypeR}
    (hne : projBody ≠ .end)
    : projBody.substitute t rlt ≠ .end ∨
      ∃ v, projBody = .var v ∧ v = t ∧ rlt = .end := by
  cases projBody with
  | «end» => exact absurd rfl hne
  | var v =>
    by_cases hv : v = t
    · -- v = t: substitution gives rlt
      subst hv
      by_cases hr : rlt = .end
      · -- rlt = .end: right disjunct
        right
        exact ⟨v, rfl, rfl, hr⟩
      · -- rlt ≠ .end: left disjunct
        left
        simp only [substitute_var_eq]
        exact hr
    · -- v ≠ t: substitution gives .var v ≠ .end
      left
      simp only [substitute_var_ne hv]
      intro h; cases h
  | send partner branches =>
    left
    simp only [substitute_send]
    intro h; cases h
  | recv partner branches =>
    left
    simp only [substitute_recv]
    intro h; cases h
  | mu s body =>
    left
    by_cases hs : s = t
    · subst hs
      simp only [substitute_mu_shadow]
      intro h; cases h
    · simp only [substitute_mu_ne hs]; intro h; cases h

/-- Local actions over recursive local types (kind, partner, label). -/
structure LocalActionR where
  kind : LocalKind
  partner : String
  label : Label
deriving Repr, DecidableEq, Inhabited

/-- Smart constructors for local actions. -/
def LocalActionR.send (partner : String) (label : Label) : LocalActionR :=
  { kind := LocalKind.send, partner := partner, label := label }

def LocalActionR.recv (partner : String) (label : Label) : LocalActionR :=
  { kind := LocalKind.recv, partner := partner, label := label }

/-- Convert a local action to a global action for a given role. -/
def LocalActionR.toGlobal (role : String) (act : LocalActionR) : Rumpsteak.Protocol.GlobalType.GlobalActionR :=
  match act.kind with
  | LocalKind.send =>
      { sender := role, receiver := act.partner, label := act.label }
  | LocalKind.recv =>
      { sender := act.partner, receiver := role, label := act.label }

/-- Local enabledness (async): a local type can take a local action.
    Async skip is allowed only through send heads (receiver blocks). -/
inductive canStep : LocalTypeR → LocalActionR → Prop
  | send_head (partner : String) (branches : List (Label × LocalTypeR))
      (label : Label) (cont : LocalTypeR) :
      (label, cont) ∈ branches →
      canStep (.send partner branches) (LocalActionR.send partner label)
  | recv_head (partner : String) (branches : List (Label × LocalTypeR))
      (label : Label) (cont : LocalTypeR) :
      (label, cont) ∈ branches →
      canStep (.recv partner branches) (LocalActionR.recv partner label)
  | send_async (partner : String) (branches : List (Label × LocalTypeR))
      (act : LocalActionR) (label : Label) (cont : LocalTypeR) :
      act.partner ≠ partner →
      (label, cont) ∈ branches →
      canStep cont act →
      canStep (.send partner branches) act
  | mu (t : String) (body : LocalTypeR) (act : LocalActionR) :
      canStep (body.substitute t (.mu t body)) act →
      canStep (.mu t body) act

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
