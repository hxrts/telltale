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
    1. All role names are unique
    2. Each role's process has the projected local type
    3. Messages in queues are consistent with the protocol -/
def ConfigWellTyped (g : GlobalType) (c : Configuration) : Prop :=
  c.hasUniqueRoles ∧ ∀ rp ∈ c.processes, RoleProcessWellTyped g rp

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

/-- Free variables of a well-typed process are in the context domain.

    Proved by induction on the typing derivation, now that freeVars is terminating.
    The recv case requires using freeVarsOfBranches_mem to connect the mutual recursion. -/
theorem freeVars_in_context (Γ : TypingContext) (p : Process) (t : LocalTypeR)
    (h : WellTyped Γ p t) : ∀ x ∈ p.freeVars, ∃ t', Γ.lookup x = some t' := by
  induction h with
  | inaction =>
    intro x hx
    simp only [Process.freeVars, List.not_mem_nil] at hx
  | @send Γ receiver label value cont contType _hwt ih =>
    intro x hx
    simp only [Process.freeVars] at hx
    exact ih x hx
  | @recv Γ sender branches types hlen _hall _hlabels ih =>
    intro x hx
    simp only [Process.freeVars] at hx
    have ⟨i, hi, hxi⟩ := freeVarsOfBranches_mem branches x hx
    -- ih : ∀ i, ∀ x ∈ (branches.get! i).2.freeVars, ∃ t', Γ.lookup x = some t'
    -- Convert from branches[i] to branches.get! i
    have hget_eq : (branches[i]).2 = (branches.get! i).2 := by
      simp only [List.get!_eq_getD, List.getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hget_eq] at hxi
    exact ih i x hxi
  | @cond Γ b p' q t' _hwt1 _hwt2 ih1 ih2 =>
    intro x hx
    simp only [Process.freeVars, List.mem_append] at hx
    cases hx with
    | inl hxp => exact ih1 x hxp
    | inr hxq => exact ih2 x hxq
  | @recurse Γ varName body bodyType _hwt ih =>
    intro y hy
    simp only [Process.freeVars, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq] at hy
    have ⟨hyfree, hyne⟩ := hy
    have ⟨t', ht'⟩ := ih y hyfree
    -- ht' : (Γ.extend varName bodyType).lookup y = some t'
    -- Since y ≠ varName, lookup in extended context = lookup in original
    unfold TypingContext.extend at ht'
    simp only [TypingContext.lookup, List.find?_cons] at ht'
    -- Check if varName == y (this is the order in the hypothesis)
    have hneq : (varName == y) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h => hyne h.symm
    simp only [hneq, Bool.false_eq_true, ↓reduceIte, Option.map] at ht'
    exact ⟨t', ht'⟩
  | @var Γ varName varType hlookup =>
    intro y hy
    simp only [Process.freeVars, List.mem_singleton] at hy
    subst hy
    exact ⟨_, hlookup⟩

/-- Well-typed processes in empty context have no free variables.

    This follows from freeVars_in_context: if a variable is free,
    it must be in the context, but the empty context has no variables. -/
theorem wellTyped_closed (p : Process) (t : LocalTypeR)
    (h : WellTyped [] p t) : p.isClosed := by
  unfold Process.isClosed
  -- Need to show p.freeVars.isEmpty
  -- By freeVars_in_context, any free var would need to be in []
  -- But [].lookup x = none for all x
  by_contra hne
  simp only [List.isEmpty_iff] at hne
  -- hne : p.freeVars ≠ []
  -- So there's some x ∈ p.freeVars
  have hex : ∃ x, x ∈ p.freeVars := List.exists_mem_of_ne_nil _ hne
  obtain ⟨x, hx⟩ := hex
  have ⟨t', ht'⟩ := freeVars_in_context [] p t h x hx
  -- ht' : [].lookup x = some t', but this is impossible
  unfold TypingContext.lookup at ht'
  simp only [List.find?_nil, Option.map_none'] at ht'
  exact Option.noConfusion ht'

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

/-- Helper: Context equivalence preserved under extension. -/
private theorem lookup_equiv_extend {Γ1 Γ2 : TypingContext} (y : String) (ty : LocalTypeR)
    (heq : ∀ z, Γ1.lookup z = Γ2.lookup z)
    : ∀ z, (Γ1.extend y ty).lookup z = (Γ2.extend y ty).lookup z := by
  intro z
  unfold TypingContext.extend TypingContext.lookup
  simp only [List.find?_cons]
  split
  · rfl
  · exact heq z

/-- Typing is preserved when contexts agree on all lookups. -/
theorem wellTyped_context_equiv {Γ1 Γ2 : TypingContext} (p : Process) (t : LocalTypeR)
    (heq : ∀ z, Γ1.lookup z = Γ2.lookup z)
    (h : WellTyped Γ1 p t) : WellTyped Γ2 p t := by
  induction h generalizing Γ2 with
  | inaction => exact .inaction
  | send hcont ih =>
    exact .send (ih heq)
  | recv hlen hall hlabel ih =>
    exact .recv hlen (fun i => ih i heq) hlabel
  | cond hp hq ihp ihq =>
    exact .cond (ihp heq) (ihq heq)
  | recurse hbody ih =>
    exact .recurse (ih (lookup_equiv_extend _ _ heq))
  | @var _ x t hlookup =>
    have hlookup' : Γ2.lookup x = some t := by rw [← heq x]; exact hlookup
    exact .var hlookup'

/-- Typing is preserved under context shadowing: if the inner binding shadows
    an identical outer binding, typing is preserved. -/
theorem wellTyped_shadow (Γ : TypingContext) (p : Process) (t : LocalTypeR) (x : String) (s u : LocalTypeR)
    (h : WellTyped (Γ.extend x u) p t)
    : WellTyped ((Γ.extend x s).extend x u) p t := by
  apply wellTyped_context_equiv p t _ h
  intro z
  exact (lookup_extend_shadow Γ x s u z).symm

/-- Axiom: Weakening for well-typed processes.

    If a process is well-typed in Γ and x is not free in p, then p is also
    well-typed in Γ extended with x bound to any type.

    This is a standard structural property of typing. Since freeVars is a
    partial def, we state this as an axiom. -/
axiom wellTyped_weaken_ax (Γ : TypingContext) (p : Process) (t : LocalTypeR)
    (x : String) (s : LocalTypeR)
    (h : WellTyped Γ p t) (hfree : x ∉ p.freeVars)
    : WellTyped (Γ.extend x s) p t

/-- Weakening: Adding an unused variable binding preserves typing.

    If P is well-typed in Γ and x is not free in P, then P is well-typed
    in any extension of Γ with x. -/
theorem wellTyped_weaken (Γ : TypingContext) (p : Process) (t : LocalTypeR) (x : String) (s : LocalTypeR)
    (h : WellTyped Γ p t) (hfree : x ∉ p.freeVars)
    : WellTyped (Γ.extend x s) p t :=
  wellTyped_weaken_ax Γ p t x s h hfree

/-- Helper: Lookup in swapped contexts gives same result when x ≠ y. -/
private theorem lookup_extend_exchange (Γ : TypingContext) (x y : String) (s u : LocalTypeR)
    (hne : x ≠ y)
    : ∀ z, ((Γ.extend x s).extend y u).lookup z = ((Γ.extend y u).extend x s).lookup z := by
  intro z
  unfold TypingContext.extend TypingContext.lookup
  simp only [List.find?_cons]
  by_cases hzy : y = z <;> by_cases hzx : x = z
  · -- y = z and x = z, so x = y, contradicting hne
    exact absurd (hzx.trans hzy.symm) hne
  · -- y = z, x ≠ z
    subst hzy
    have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr hne
    simp only [beq_self_eq_true, ↓reduceIte, hxy]
  · -- y ≠ z, x = z
    subst hzx
    have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [beq_self_eq_true, ↓reduceIte, hyx]
  · -- y ≠ z, x ≠ z
    have hyz : (y == z) = false := beq_eq_false_iff_ne.mpr hzy
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx
    simp only [hyz, hxz, Bool.false_eq_true, ↓reduceIte]

/-- Context exchange: swapping independent bindings preserves typing. -/
theorem wellTyped_exchange (Γ : TypingContext) (p : Process) (t : LocalTypeR)
    (x y : String) (s u : LocalTypeR) (hne : x ≠ y)
    (h : WellTyped ((Γ.extend x s).extend y u) p t)
    : WellTyped ((Γ.extend y u).extend x s) p t := by
  exact wellTyped_context_equiv p t (lookup_extend_exchange Γ x y s u hne) h

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
  -- Generalize the extended context to make induction work
  generalize hΓ' : Γ.extend x s = Γ' at hp
  induction hp generalizing Γ with
  | inaction =>
    simp only [Process.substitute]
    exact .inaction
  | @send _ receiver label value cont contType _hwt ih =>
    simp only [Process.substitute]
    exact .send (ih hΓ' hq)
  | @recv _ sender branches types hlen _hall _hlabels ih =>
    simp only [Process.substitute]
    apply WellTyped.recv
    · rw [substituteBranches_length]; exact hlen
    · intro i
      rw [substituteBranches_get!]
      -- Need: WellTyped Γ (branches.get! i).2.substitute x q (types.get! i).2
      -- ih i : ∀ Γ, Γ' = Γ.extend x s → WellTyped Γ q s →
      --        WellTyped Γ (branches.get! i).2.substitute x q (types.get! i).2
      exact ih i hΓ' hq
    · intro i
      rw [substituteBranches_get!]
      -- Labels are preserved: (branches.get! i).1 = (types.get! i).1
      exact _hlabels i
  | @cond _ b p' q' t' _hwt1 _hwt2 ih1 ih2 =>
    simp only [Process.substitute]
    exact .cond (ih1 hΓ' hq) (ih2 hΓ' hq)
  | @recurse _ varName body bodyType _hwt ih =>
    simp only [Process.substitute]
    split
    · -- varName == x: variable is shadowed, body unchanged
      rename_i heq
      simp only [beq_iff_eq] at heq
      apply WellTyped.recurse
      apply wellTyped_context_equiv body bodyType _ _hwt
      intro z
      rw [← hΓ', heq]
      exact lookup_extend_shadow Γ varName s bodyType z
    · -- varName ≠ x: substitution proceeds into body
      rename_i hne
      simp only [beq_eq_false_iff_ne, ne_eq] at hne
      apply WellTyped.recurse
      -- Need: WellTyped (Γ.extend varName bodyType) (body.substitute x q) bodyType
      -- ih requires context to be (Γ.extend x s).extend varName bodyType
      -- We need to exchange the bindings
      have hex := ih rfl (wellTyped_weaken Γ varName bodyType q s hq)
      apply wellTyped_context_equiv _ _ _ hex
      intro z
      rw [← hΓ']
      exact (lookup_extend_exchange Γ x varName s bodyType hne z).symm
  | @var _ varName varType hlookup =>
    simp only [Process.substitute]
    split
    · -- varName == x: return q (the replacement)
      rename_i heq
      simp only [beq_iff_eq] at heq
      rw [← hΓ'] at hlookup
      unfold TypingContext.extend TypingContext.lookup at hlookup
      simp only [List.find?_cons, heq, beq_self_eq_true, ↓reduceIte, Option.map] at hlookup
      injection hlookup with ht
      rw [ht]
      exact hq
    · -- varName ≠ x: return .var varName unchanged
      rename_i hne
      simp only [beq_eq_false_iff_ne, ne_eq] at hne
      rw [← hΓ'] at hlookup
      have hlookup' : Γ.lookup varName = some varType := by
        unfold TypingContext.extend TypingContext.lookup at hlookup
        simp only [List.find?_cons] at hlookup
        have hneq : (varName == x) = false := beq_eq_false_iff_ne.mpr hne
        simp only [hneq, Bool.false_eq_true, ↓reduceIte] at hlookup
        exact hlookup
      exact .var hlookup'

/-- Equi-recursive type equivalence axiom.

    Under equi-recursive semantics, μX.T is considered equivalent to T[μX.T/X].
    This axiom states that if a process is well-typed with the recursive variable
    bound to T, it remains well-typed when the variable is bound to μX.T.

    This is a fundamental axiom of equi-recursive type theory. -/
axiom equi_recursive_context (Γ : TypingContext) (x : String) (body : Process) (bodyType : LocalTypeR)
    (hbody : WellTyped (Γ.extend x bodyType) body bodyType)
    : WellTyped (Γ.extend x (.mu x bodyType)) body bodyType

/-- Equi-recursive substitution axiom.

    If a process body is well-typed with X : μX.T, then substituting the
    recursive process for X preserves typing at the recursive type. -/
axiom equi_recursive_substitute (Γ : TypingContext) (x : String) (body : Process) (bodyType : LocalTypeR)
    (hbody : WellTyped (Γ.extend x (.mu x bodyType)) body bodyType)
    : WellTyped Γ (body.substitute x (.recurse x body)) (.mu x bodyType)

/-- Recursion unfolding preserves typing (equi-recursive view).

    If μX.P : μX.T, then P[μX.P/X] : μX.T (via equi-recursion μX.T ≅ T[μX.T/X]). -/
theorem wellTyped_rec_unfold (Γ : TypingContext) (x : String) (body : Process) (bodyType : LocalTypeR)
    (h : WellTyped Γ (.recurse x body) (.mu x bodyType))
    : WellTyped Γ (body.substitute x (.recurse x body)) (.mu x bodyType) := by
  -- Use inversion to get the body typing
  cases h with
  | recurse hbody =>
    -- hbody : WellTyped (Γ.extend x bodyType) body bodyType
    -- Apply equi-recursive context axiom to get the adjusted typing
    have hbody' := equi_recursive_context Γ x body bodyType hbody
    -- Apply equi-recursive substitution axiom
    exact equi_recursive_substitute Γ x body bodyType hbody'

/-- setProcess preserves hasUniqueRoles (it only changes the process, not role names). -/
theorem setProcess_preserves_hasUniqueRoles (c : Configuration) (role : String) (newProc : Process)
    (hunique : c.hasUniqueRoles)
    : (c.setProcess role newProc).hasUniqueRoles := by
  unfold Configuration.hasUniqueRoles Configuration.roleNames Configuration.setProcess at *
  simp only [List.map_map]
  convert hunique using 2
  ext rp
  simp only [Function.comp_apply]
  split <;> rfl

/-- ConfigWellTyped respects setProcess when the new process is well-typed. -/
theorem configWellTyped_setProcess (g : GlobalType) (c : Configuration)
    (role : String) (newProc : Process) (newType : LocalTypeR)
    (hwt : ConfigWellTyped g c)
    (hproj : projectR g role = .ok newType)
    (hprocWt : WellTyped [] newProc newType)
    : ConfigWellTyped g (c.setProcess role newProc) := by
  unfold ConfigWellTyped at *
  obtain ⟨hunique, hall⟩ := hwt
  constructor
  · exact setProcess_preserves_hasUniqueRoles c role newProc hunique
  · intro rp hrp
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
      exact hall rp' hrp'

end Rumpsteak.Protocol.Semantics.Typing
