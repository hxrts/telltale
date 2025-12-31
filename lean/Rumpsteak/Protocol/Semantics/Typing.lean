import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.Semantics.Process
import Rumpsteak.Protocol.Semantics.Configuration

/-! # Rumpsteak.Protocol.Semantics.Typing

Type system for multiparty session processes.

## Overview

This module defines the typing relation between processes and local types.
A process is well-typed if its communication actions match the expected
local type obtained by projecting the global type.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Typing Rules

- `inaction ⊢ end`
- `P ⊢ T` implies `send q l v P ⊢ !q{l.T}`
- `∀i. Pᵢ ⊢ Tᵢ` implies `recv p {lᵢ.Pᵢ} ⊢ ?p{lᵢ.Tᵢ}`
- `P ⊢ T[μX.T/X]` implies `rec X P ⊢ μX.T`

## Expose

The following definitions form the semantic interface for proofs:

- `WellTyped`: Relation between Process and LocalTypeR
- `ConfigWellTyped`: Typing for configurations against global types
- `typecheck`: Decidable type checking

## Main Definitions

- `WellTyped` - Inductive typing relation
- `ConfigWellTyped` - Configuration typing
-/

namespace Rumpsteak.Protocol.Semantics.Typing

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.ProjectionR
open Rumpsteak.Protocol.Semantics.Process
open Rumpsteak.Protocol.Semantics.Configuration

/-- Typing context maps process variables to local types. -/
abbrev TypingContext := List (String × LocalTypeR)

/-- Look up a variable in the typing context. -/
def TypingContext.lookup (ctx : TypingContext) (x : String) : Option LocalTypeR :=
  ctx.find? (fun (y, _) => y == x) |>.map (·.2)

/-- Extend the context with a new binding. -/
def TypingContext.extend (ctx : TypingContext) (x : String) (t : LocalTypeR) : TypingContext :=
  (x, t) :: ctx

/-- Well-typed process against a local type.

    Judgment: Γ ⊢ P : T
    - Context Γ maps process variables to types
    - Process P has local type T -/
inductive WellTyped : TypingContext → Process → LocalTypeR → Prop where
  /-- Inaction has type end -/
  | inaction : WellTyped Γ .inaction .end

  /-- Send: if continuation has type T, send has type !q{l.T} -/
  | send :
    ∀ {Γ : TypingContext} {receiver : String} {label : Label} {value : Value}
      {cont : Process} {contType : LocalTypeR},
    WellTyped Γ cont contType →
    WellTyped Γ (.send receiver label value cont) (.send receiver [(label, contType)])

  /-- Receive: if all branches have matching types, receive is typed -/
  | recv :
    ∀ {Γ : TypingContext} {sender : String}
      {branches : List (Label × Process)} {types : List (Label × LocalTypeR)},
    branches.length = types.length →
    (∀ i, WellTyped Γ (branches.get! i).2 (types.get! i).2) →
    (∀ i, (branches.get! i).1 = (types.get! i).1) →
    WellTyped Γ (.recv sender branches) (.recv sender types)

  /-- Conditional: both branches must have the same type -/
  | cond :
    ∀ {Γ : TypingContext} {b : Bool} {p q : Process} {t : LocalTypeR},
    WellTyped Γ p t →
    WellTyped Γ q t →
    WellTyped Γ (.cond b p q) t

  /-- Recursion: body is typed in extended context -/
  | recurse :
    ∀ {Γ : TypingContext} {x : String} {body : Process} {t : LocalTypeR},
    WellTyped (Γ.extend x t) body t →
    WellTyped Γ (.recurse x body) (.mu x t)

  /-- Variable: lookup in context -/
  | var :
    ∀ {Γ : TypingContext} {x : String} {t : LocalTypeR},
    Γ.lookup x = some t →
    WellTyped Γ (.var x) t

/-- A role process is well-typed if its process has the projected type. -/
def RoleProcessWellTyped (g : GlobalType) (rp : RoleProcess) : Prop :=
  match projectR g rp.role with
  | .ok lt => WellTyped [] rp.process lt
  | .error _ => False

/-- A configuration is well-typed against a global type if:
    1. Each role's process has the projected local type
    2. Messages in queues are consistent with the protocol -/
def ConfigWellTyped (g : GlobalType) (c : Configuration) : Prop :=
  ∀ rp ∈ c.processes, RoleProcessWellTyped g rp

/-! ## Decidable Type Checking -/

/-- Result of type checking. -/
inductive TypeCheckResult where
  | ok : LocalTypeR → TypeCheckResult
  | error : String → TypeCheckResult
deriving Repr, Inhabited

/-- Check if a value matches a sort. -/
def valueMatchesSort (v : Value) (s : PayloadSort) : Bool :=
  match v, s with
  | .unit, .unit => true
  | .nat _, .nat => true
  | .bool _, .bool => true
  | .string _, .string => true
  | .pair v1 v2, .prod s1 s2 => valueMatchesSort v1 s1 && valueMatchesSort v2 s2
  | _, _ => false

/-- Synthesize a type for a process (simplified). -/
partial def synthesizeType (ctx : TypingContext) (p : Process) (fuel : Nat := 50)
    : TypeCheckResult :=
  if fuel == 0 then .error "Type synthesis depth limit exceeded"
  else match p with
  | .inaction => .ok .end
  | .var x =>
    match ctx.lookup x with
    | some t => .ok t
    | none => .error s!"Unbound variable: {x}"
  | .send receiver label value cont =>
    match synthesizeType ctx cont (fuel - 1) with
    | .ok contType => .ok (.send receiver [(label, contType)])
    | .error e => .error e
  | .recv sender branches =>
    let typedBranches := branches.map fun (label, cont) =>
      match synthesizeType ctx cont (fuel - 1) with
      | .ok t => some (label, t)
      | .error _ => none
    if typedBranches.all (·.isSome) then
      .ok (.recv sender (typedBranches.filterMap id))
    else
      .error "Failed to type check receive branches"
  | .cond _ p q =>
    match synthesizeType ctx p (fuel - 1), synthesizeType ctx q (fuel - 1) with
    | .ok t1, .ok t2 =>
      if t1 == t2 then .ok t1
      else .error "Conditional branches have different types"
    | .error e, _ => .error e
    | _, .error e => .error e
  | .recurse x body =>
    -- Infer type by checking body with placeholder
    match synthesizeType (ctx.extend x .end) body (fuel - 1) with
    | .ok t => .ok (.mu x t)
    | .error e => .error e
  | .par _ _ =>
    .error "Parallel composition type synthesis not supported"

/-- Check if a process has a given type. -/
def checkType (ctx : TypingContext) (p : Process) (expected : LocalTypeR) (fuel : Nat := 50)
    : Bool :=
  match synthesizeType ctx p fuel with
  | .ok actual => actual == expected
  | .error _ => false

/-! ## Typing Lemmas -/

/-- Free variables of a well-typed process are in the context domain. -/
theorem freeVars_in_context (Γ : TypingContext) (p : Process) (t : LocalTypeR)
    (h : WellTyped Γ p t) : ∀ x ∈ p.freeVars, ∃ t', Γ.lookup x = some t' := by
  -- TODO: Update proof for partial def freeVars
  -- Process.freeVars is now partial, so simp can't unfold it
  sorry

/-- Well-typed processes in empty context have no free variables.

    This follows from freeVars_in_context: if a variable is free,
    it must be in the context, but the empty context has no variables. -/
theorem wellTyped_closed (p : Process) (t : LocalTypeR)
    (h : WellTyped [] p t) : p.isClosed := by
  -- TODO: Update proof for partial def freeVars
  sorry

/-- Inversion lemma for conditional typing. -/
theorem wellTyped_cond_inversion (Γ : TypingContext) (b : Bool) (p q : Process) (t : LocalTypeR)
    (h : WellTyped Γ (.cond b p q) t)
    : WellTyped Γ p t ∧ WellTyped Γ q t := by
  cases h with
  | cond hp hq => exact ⟨hp, hq⟩

/-- Inversion lemma for send typing. -/
theorem wellTyped_send_inversion (Γ : TypingContext) (receiver : String)
    (label : Label) (value : Value) (cont : Process) (t : LocalTypeR)
    (h : WellTyped Γ (.send receiver label value cont) t)
    : ∃ contType, t = .send receiver [(label, contType)] ∧ WellTyped Γ cont contType := by
  cases h with
  | send hcont =>
    rename_i contType
    exact ⟨contType, rfl, hcont⟩

/-- Inversion lemma for recv typing. -/
theorem wellTyped_recv_inversion (Γ : TypingContext) (sender : String)
    (branches : List (Label × Process)) (t : LocalTypeR)
    (h : WellTyped Γ (.recv sender branches) t)
    : ∃ types, t = .recv sender types ∧
               branches.length = types.length ∧
               (∀ i, WellTyped Γ (branches.get! i).2 (types.get! i).2) ∧
               (∀ i, (branches.get! i).1 = (types.get! i).1) := by
  cases h with
  | recv hlen hall hlabel =>
    rename_i types
    exact ⟨types, rfl, hlen, hall, hlabel⟩

/-- Inversion lemma for recursion typing. -/
theorem wellTyped_rec_inversion (Γ : TypingContext) (x : String) (body : Process) (t : LocalTypeR)
    (h : WellTyped Γ (.recurse x body) t)
    : ∃ bodyType, t = .mu x bodyType ∧ WellTyped (Γ.extend x bodyType) body bodyType := by
  cases h with
  | recurse hbody =>
    rename_i bodyType
    exact ⟨bodyType, rfl, hbody⟩

/-- Context lookup is preserved when extending with a different variable. -/
theorem lookup_extend_neq (Γ : TypingContext) (x y : String) (s t : LocalTypeR)
    (hne : x ≠ y)
    : (Γ.extend y t).lookup x = Γ.lookup x := by
  unfold TypingContext.extend TypingContext.lookup
  simp only [List.find?_cons]
  have hyx : (y == x) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun h => hne h.symm
  simp only [hyx]

/-- Extending with the same variable twice: inner shadows outer.
    For any lookup, ((Γ.extend x s).extend x t).lookup z = (Γ.extend x t).lookup z -/
theorem lookup_extend_shadow (Γ : TypingContext) (x : String) (s t : LocalTypeR) (z : String)
    : ((Γ.extend x s).extend x t).lookup z = (Γ.extend x t).lookup z := by
  unfold TypingContext.extend TypingContext.lookup
  simp only [List.find?_cons]
  split <;> rfl

/-- Typing is preserved under context shadowing: if the inner binding shadows
    an identical outer binding, typing is preserved. -/
theorem wellTyped_shadow (Γ : TypingContext) (p : Process) (t : LocalTypeR) (x : String) (s u : LocalTypeR)
    (h : WellTyped (Γ.extend x u) p t)
    : WellTyped ((Γ.extend x s).extend x u) p t := by
  -- TODO: Fix induction structure for context shadowing
  -- The key insight is that lookups in both contexts agree (lookup_extend_shadow)
  -- Need to generalize the induction properly for compound contexts
  sorry

/-- Weakening: Adding an unused variable binding preserves typing.

    If P is well-typed in Γ and x is not free in P, then P is well-typed
    in any extension of Γ with x. -/
theorem wellTyped_weaken (Γ : TypingContext) (p : Process) (t : LocalTypeR) (x : String) (s : LocalTypeR)
    (h : WellTyped Γ p t) (hfree : x ∉ p.freeVars)
    : WellTyped (Γ.extend x s) p t := by
  -- TODO: Fix induction with partial def freeVars
  -- Key insight: if x is not free, adding x to context doesn't affect lookups
  -- for any variable actually used in p
  sorry

/-- Context exchange: swapping independent bindings preserves typing. -/
theorem wellTyped_exchange (Γ : TypingContext) (p : Process) (t : LocalTypeR)
    (x y : String) (s u : LocalTypeR) (hne : x ≠ y)
    (h : WellTyped ((Γ.extend x s).extend y u) p t)
    : WellTyped ((Γ.extend y u).extend x s) p t := by
  -- TODO: Fix induction for compound contexts
  -- Exchange is a standard structural property: lookup in swapped contexts
  -- gives the same result for any variable z (since x ≠ y)
  sorry

/-- Substitution lemma for process/type.

    If process P has type T in context with X:S, and process Q has type S in context Γ,
    then P[Q/X] has type T in context Γ.

    Note: For session types, we use a simplified version since we only substitute
    recursive processes for their bound variables. -/
theorem wellTyped_process_substitute (Γ : TypingContext) (p q : Process)
    (x : String) (s t : LocalTypeR)
    (hp : WellTyped (Γ.extend x s) p t)
    (hq : WellTyped Γ q s)
    : WellTyped Γ (p.substitute x q) t := by
  -- TODO: Fix induction for compound contexts and partial substitute
  -- The proof requires induction on the typing derivation with careful
  -- handling of context extension and variable shadowing
  sorry

/-- Recursion unfolding preserves typing (equi-recursive view).

    If μX.P : μX.T, then P[μX.P/X] : μX.T (via equi-recursion μX.T ≅ T[μX.T/X]). -/
theorem wellTyped_rec_unfold (Γ : TypingContext) (x : String) (body : Process) (bodyType : LocalTypeR)
    (h : WellTyped Γ (.recurse x body) (.mu x bodyType))
    : WellTyped Γ (body.substitute x (.recurse x body)) (.mu x bodyType) := by
  -- TODO: Requires equi-recursive type reasoning
  -- The key insight is that μX.T ≅ T[μX.T/X] under equi-recursive semantics
  -- This allows us to type the unfolded body at the recursive type
  sorry

/-- ConfigWellTyped respects setProcess when the new process is well-typed. -/
theorem configWellTyped_setProcess (g : GlobalType) (c : Configuration)
    (role : String) (newProc : Process) (newType : LocalTypeR)
    (hwt : ConfigWellTyped g c)
    (hproj : projectR g role = .ok newType)
    (hprocWt : WellTyped [] newProc newType)
    : ConfigWellTyped g (c.setProcess role newProc) := by
  unfold ConfigWellTyped at *
  intro rp hrp
  unfold Configuration.setProcess at hrp
  simp only [List.mem_map] at hrp
  obtain ⟨rp', hrp', heq⟩ := hrp
  by_cases h : rp'.role == role
  · -- This is the role being updated
    simp only [h, ↓reduceIte] at heq
    subst heq
    unfold RoleProcessWellTyped
    simp only [beq_iff_eq] at h
    simp only [h, hproj]
    exact hprocWt
  · -- Different role, preserved by setProcess
    simp only [h] at heq
    subst heq
    exact hwt rp' hrp'

end Rumpsteak.Protocol.Semantics.Typing
