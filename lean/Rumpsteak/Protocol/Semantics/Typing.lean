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

import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.Semantics.Process
import Rumpsteak.Protocol.Semantics.Configuration

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
  | rec :
    ∀ {Γ : TypingContext} {x : String} {body : Process} {t : LocalTypeR},
    WellTyped (Γ.extend x t) body t →
    WellTyped Γ (.rec x body) (.rec x t)

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
  c.processes.all (fun rp => RoleProcessWellTyped g rp)

/-! ## Decidable Type Checking -/

/-- Result of type checking. -/
inductive TypeCheckResult where
  | ok : LocalTypeR → TypeCheckResult
  | error : String → TypeCheckResult
deriving Repr, Inhabited

/-- Check if a value matches a sort. -/
def valueMatchesSort (v : Value) (s : Sort) : Bool :=
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
  | .rec x body =>
    -- Infer type by checking body with placeholder
    match synthesizeType (ctx.extend x .end) body (fuel - 1) with
    | .ok t => .ok (.rec x t)
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
  induction h with
  | inaction =>
    intro x hx
    simp only [Process.freeVars, List.not_mem_nil] at hx
  | @send Γ receiver label value cont contType _ ih =>
    intro x hx
    simp only [Process.freeVars] at hx
    exact ih x hx
  | @recv Γ sender branches types hlen hall hlabel ih =>
    intro x hx
    simp only [Process.freeVars, List.mem_bind] at hx
    obtain ⟨⟨lbl, proc⟩, hmem, hxproc⟩ := hx
    -- Find the index of this branch
    have ⟨i, hi⟩ := List.get_of_mem hmem
    -- The ih for index i says: ∀ y ∈ (branches.get! i).2.freeVars, ∃ t', Γ.lookup y = some t'
    have ih_i := ih i
    -- We need to show x is in (branches.get! i).2.freeVars
    -- From hi we have branches[i] = (lbl, proc), so (branches.get! i).2 = proc
    have hget : branches.get ⟨i, by omega⟩ = (lbl, proc) := hi
    have hproc_eq : (branches.get! i).2 = proc := by
      simp only [List.get!_eq_getD]
      rw [List.getD_eq_get (by omega)]
      simp only [hget]
    rw [← hproc_eq] at hxproc
    exact ih_i x hxproc
  | cond ihp ihq =>
    intro x hx
    simp only [Process.freeVars, List.mem_append] at hx
    cases hx with
    | inl hp => exact ihp x hp
    | inr hq => exact ihq x hq
  | @rec Γ varName body bodyType _ ih =>
    intro x hx
    simp only [Process.freeVars, List.mem_filter, bne_iff_ne, ne_eq,
               decide_eq_true_eq] at hx
    obtain ⟨hbody, hne⟩ := hx
    -- ih says: ∀ y ∈ body.freeVars, ∃ t', (Γ.extend varName bodyType).lookup y = some t'
    obtain ⟨t', hlookup⟩ := ih x hbody
    -- The lookup in extended context
    unfold TypingContext.extend TypingContext.lookup at hlookup
    simp only [List.find?_cons] at hlookup
    -- Case split on whether x == varName
    by_cases hxvar : x == varName
    · -- x = varName, but we have hne : x ≠ varName, contradiction
      simp only [beq_iff_eq] at hxvar
      exact absurd hxvar hne
    · -- x ≠ varName, so lookup goes to the tail
      simp only [hxvar, cond_false] at hlookup
      exact ⟨t', hlookup⟩
  | var hlookup =>
    intro y hy
    simp only [Process.freeVars, List.mem_singleton] at hy
    simp only [hy]
    exact ⟨_, hlookup⟩

/-- Well-typed processes in empty context have no free variables.

    This follows from freeVars_in_context: if a variable is free,
    it must be in the context, but the empty context has no variables. -/
theorem wellTyped_closed (p : Process) (t : LocalTypeR)
    (h : WellTyped [] p t) : p.isClosed := by
  unfold Process.isClosed
  simp only [List.isEmpty_eq_true, List.eq_nil_iff_forall_not_mem]
  intro x hx
  obtain ⟨t', hlookup⟩ := freeVars_in_context [] p t h x hx
  unfold TypingContext.lookup at hlookup
  simp only [List.find?_nil, Option.map_none'] at hlookup

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
    (h : WellTyped Γ (.rec x body) t)
    : ∃ bodyType, t = .rec x bodyType ∧ WellTyped (Γ.extend x bodyType) body bodyType := by
  cases h with
  | rec hbody =>
    rename_i bodyType
    exact ⟨bodyType, rfl, hbody⟩

/-- Context lookup is preserved when extending with a different variable. -/
theorem lookup_extend_neq (Γ : TypingContext) (x y : String) (s t : LocalTypeR)
    (hne : x ≠ y)
    : (Γ.extend y t).lookup x = Γ.lookup x := by
  unfold TypingContext.extend TypingContext.lookup
  simp only [List.find?_cons]
  have hneq : (x == y) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact hne
  simp only [hneq, cond_false]

/-- Weakening: Adding an unused variable binding preserves typing.

    If P is well-typed in Γ and x is not free in P, then P is well-typed
    in any extension of Γ with x. -/
theorem wellTyped_weaken (Γ : TypingContext) (p : Process) (t : LocalTypeR) (x : String) (s : LocalTypeR)
    (h : WellTyped Γ p t) (hfree : x ∉ p.freeVars)
    : WellTyped (Γ.extend x s) p t := by
  induction h with
  | inaction => exact WellTyped.inaction
  | @send Γ' receiver label value cont contType hwt ih =>
    simp only [Process.freeVars] at hfree
    exact WellTyped.send (ih hfree)
  | @recv Γ' sender branches types hlen hall hlabel ih =>
    simp only [Process.freeVars, List.mem_bind] at hfree
    apply WellTyped.recv hlen
    · intro i
      apply ih i
      push_neg at hfree
      intro hmem
      exact hfree (branches.get! i) (by
        simp only [List.get!_eq_getD]
        by_cases hi : i < branches.length
        · exact List.getD_mem branches default hi
        · simp only [List.getD_eq_default (by omega)]
          simp only [List.not_mem_nil] at hmem) hmem
    · exact hlabel
  | @cond Γ' b p' q' t' hp hq ihp ihq =>
    simp only [Process.freeVars, List.mem_append] at hfree
    push_neg at hfree
    exact WellTyped.cond (ihp hfree.1) (ihq hfree.2)
  | @rec Γ' y body bodyType hwt ih =>
    simp only [Process.freeVars, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq] at hfree
    apply WellTyped.rec
    -- TODO: Weakening for recursion case
    --
    -- Need: WellTyped ((Γ.extend x s).extend y bodyType) body bodyType
    --
    -- Strategy:
    -- 1. If x = y: The inner binding shadows x, so adding x to context is irrelevant
    --    Use: ((Γ.extend x s).extend y bodyType) ≃ (Γ.extend y bodyType) for lookups
    -- 2. If x ≠ y: Apply context exchange then use IH
    --    Exchange: ((Γ.extend x s).extend y bodyType) ≃ ((Γ.extend y bodyType).extend x s)
    --    Then apply ih with the extended context
    --
    -- Required lemmas:
    -- - `extend_shadow`: (Γ.extend x s).extend x t ≃ Γ.extend x t (for typing)
    -- - `wellTyped_exchange`: Context exchange preserves typing
    by_cases hxy : x = y
    · subst hxy
      sorry
    · sorry
  | @var Γ' y t' hlookup =>
    simp only [Process.freeVars, List.mem_singleton] at hfree
    apply WellTyped.var
    rw [lookup_extend_neq Γ x y s t' hfree]
    exact hlookup

/-- Context exchange: swapping independent bindings preserves typing. -/
theorem wellTyped_exchange (Γ : TypingContext) (p : Process) (t : LocalTypeR)
    (x y : String) (s u : LocalTypeR) (hne : x ≠ y)
    (h : WellTyped ((Γ.extend x s).extend y u) p t)
    : WellTyped ((Γ.extend y u).extend x s) p t := by
  -- Exchange is a standard structural property
  -- The key insight is that lookup in swapped contexts gives the same result
  -- for any variable z (since x ≠ y)
  induction h with
  | inaction => exact WellTyped.inaction
  | send ih => exact WellTyped.send ih
  | recv hlen hall hlabel ih =>
    exact WellTyped.recv hlen (fun i => ih i) hlabel
  | cond ihp ihq =>
    exact WellTyped.cond ihp ihq
  | rec ih =>
    apply WellTyped.rec
    rename_i z body bodyType _
    -- TODO: Exchange lemma for recursion case
    --
    -- Need to show that swapping x and y bindings preserves typing
    -- when adding a third binding z for the rec body.
    --
    -- Cases:
    -- 1. z = x: innermost z shadows x, effectively removes x from consideration
    -- 2. z = y: innermost z shadows y, effectively removes y from consideration
    -- 3. z ≠ x ∧ z ≠ y: apply exchange recursively, then use ih
    --
    -- Required: `extend_shadow` and recursive application of exchange
    by_cases hzx : z = x
    · subst hzx
      sorry
    · by_cases hzy : z = y
      · subst hzy
        sorry
      · sorry
  | var hlookup =>
    apply WellTyped.var
    rename_i z t'
    -- Need to show ((Γ.extend y u).extend x s).lookup z = some t'
    -- Given: ((Γ.extend x s).extend y u).lookup z = some t'
    unfold TypingContext.extend TypingContext.lookup at hlookup ⊢
    simp only [List.find?_cons] at hlookup ⊢
    by_cases hzy : z == y
    · simp only [hzy, cond_true] at hlookup
      simp only [Option.some.injEq] at hlookup
      subst hlookup
      by_cases hzx : z == x
      · simp only [beq_iff_eq] at hzy hzx
        subst hzy hzx
        exact absurd rfl hne
      · simp only [hzx, cond_false, hzy, cond_true]
    · simp only [hzy, cond_false] at hlookup
      by_cases hzx : z == x
      · simp only [hzx, cond_true] at hlookup ⊢
      · simp only [hzx, cond_false] at hlookup ⊢
        simp only [hzy, cond_false]
        exact hlookup

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
  -- Induction on the typing derivation
  induction hp generalizing Γ s with
  | inaction =>
    simp only [Process.substitute]
    exact WellTyped.inaction
  | @send Γ' receiver label value cont contType hwt_cont ih =>
    simp only [Process.substitute]
    exact WellTyped.send (ih Γ s hq)
  | @recv Γ' sender branches types hlen hall hlabel ih =>
    simp only [Process.substitute]
    apply WellTyped.recv
    · simp only [List.length_map]
      exact hlen
    · intro i
      simp only [List.get!_map]
      exact ih i Γ s hq
    · intro i
      simp only [List.get!_map]
      exact hlabel i
  | cond ihp ihq =>
    simp only [Process.substitute]
    exact WellTyped.cond (ihp Γ s hq) (ihq Γ s hq)
  | @rec Γ' y body bodyType hwt_body ih =>
    simp only [Process.substitute]
    -- TODO: Substitution lemma for recursion
    --
    -- Two cases based on whether y shadows x:
    -- 1. y = x: The rec binding shadows x, so substitution is identity on body
    --    Result is (.rec y body) which should be typed at (.rec y bodyType)
    --    Need to show the original typing still holds (x not free in body)
    --
    -- 2. y ≠ x: Apply context exchange then IH
    --    hwt_body : WellTyped ((Γ.extend x s).extend y bodyType) body bodyType
    --    Exchange to: WellTyped ((Γ.extend y bodyType).extend x s) body bodyType
    --    Apply ih with context (Γ.extend y bodyType)
    --    Need hq weakened: WellTyped (Γ.extend y bodyType) q s
    --
    -- Required lemmas:
    -- - wellTyped_exchange (proven above, has sorries)
    -- - wellTyped_weaken (proven above, has sorries)
    by_cases hxy : y == x
    · simp only [hxy, ↓reduceIte]
      sorry
    · simp only [hxy, ↓reduceIte]
      apply WellTyped.rec
      sorry
  | @var Γ' y t' hlookup =>
    simp only [Process.substitute]
    by_cases hxy : y == x
    · -- y = x, so substitution returns q
      simp only [hxy, ↓reduceIte]
      -- From lookup in extended context: (Γ.extend x s).lookup y = some t'
      -- Since y == x, this means s = t'
      unfold TypingContext.extend TypingContext.lookup at hlookup
      simp only [beq_iff_eq] at hxy
      simp only [hxy, List.find?_cons, beq_self_eq_true, ↓reduceIte, Option.some_get] at hlookup
      simp only [← hlookup]
      exact hq
    · -- y ≠ x, substitution is identity
      simp only [hxy, ↓reduceIte]
      apply WellTyped.var
      -- Need: Γ.lookup y = some t'
      -- From hlookup: (Γ.extend x s).lookup y = some t'
      unfold TypingContext.extend TypingContext.lookup at hlookup ⊢
      simp only [List.find?_cons, hxy, cond_false] at hlookup
      exact hlookup

/-- Recursion unfolding preserves typing (equi-recursive view).

    If μX.P : μX.T, then P[μX.P/X] : μX.T (via equi-recursion μX.T ≅ T[μX.T/X]). -/
theorem wellTyped_rec_unfold (Γ : TypingContext) (x : String) (body : Process) (bodyType : LocalTypeR)
    (h : WellTyped Γ (.rec x body) (.rec x bodyType))
    : WellTyped Γ (body.substitute x (.rec x body)) (.rec x bodyType) := by
  -- By inversion, we have WellTyped (Γ.extend x bodyType) body bodyType
  cases h with
  | rec hbody =>
    -- We need to show body[μX.body/X] : μX.bodyType
    -- Using equi-recursive reasoning: μX.T ≅ T, so we can type the substituted
    -- body at the recursive type
    -- This requires the substitution lemma with S = μX.bodyType
    have hrec : WellTyped Γ (.rec x body) (.rec x bodyType) := WellTyped.rec hbody
    -- For equi-recursive types, we accept this via the substitution lemma
    exact wellTyped_process_substitute Γ body (.rec x body) x bodyType bodyType hbody hrec

/-- ConfigWellTyped respects setProcess when the new process is well-typed. -/
theorem configWellTyped_setProcess (g : GlobalType) (c : Configuration)
    (role : String) (newProc : Process) (newType : LocalTypeR)
    (hwt : ConfigWellTyped g c)
    (hproj : projectR g role = .ok newType)
    (hprocWt : WellTyped [] newProc newType)
    : ConfigWellTyped g (c.setProcess role newProc) := by
  unfold ConfigWellTyped at hwt ⊢
  unfold RoleProcessWellTyped
  simp only [List.all_eq_true, decide_eq_true_eq] at hwt ⊢
  intro rp hrp
  -- rp is in the setProcess result
  unfold Configuration.setProcess at hrp
  simp only [List.mem_map] at hrp
  obtain ⟨rp', hrp', heq⟩ := hrp
  by_cases hrole : rp'.role == role
  · -- This is the role we're updating
    simp only [hrole, ↓reduceIte] at heq
    simp only [← heq, hproj]
    simp only [beq_iff_eq] at hrole
    simp only [hrole]
    exact hprocWt
  · -- This is a different role, preserved
    simp only [hrole, ↓reduceIte] at heq
    simp only [← heq]
    exact hwt rp' hrp'

end Rumpsteak.Protocol.Semantics.Typing
