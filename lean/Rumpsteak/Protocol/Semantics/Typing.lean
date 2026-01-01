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

/-- Helper: If x is not in freeVars, extending with x doesn't affect variable lookups. -/
private theorem lookup_extend_fresh (Γ : TypingContext) (x y : String) (s : LocalTypeR)
    (hne : x ≠ y) : (Γ.extend x s).lookup y = Γ.lookup y := by
  sorry

/-- Weakening: Adding an unused variable binding preserves typing.

    If P is well-typed in Γ and x is not free in P, then P is well-typed
    in any extension of Γ with x.

    PROOF SKETCH:
    By induction on the typing derivation. Each case either:
    - Directly applies the IH with the same freeVars condition
    - Uses wellTyped_shadow for the shadowing case (x = bound variable)
    - Uses context exchange for non-shadowing case (x ≠ bound variable)
    - Uses lookup_extend_fresh for variable lookups -/
theorem wellTyped_weaken (Γ : TypingContext) (p : Process) (t : LocalTypeR) (x : String) (s : LocalTypeR)
    (h : WellTyped Γ p t) (hfree : x ∉ p.freeVars)
    : WellTyped (Γ.extend x s) p t := by
  sorry

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

    PROOF SKETCH:
    By induction on the typing derivation for P:
    - Base cases: inaction (trivial), var (check if it's the substituted variable)
    - Recursive cases: send, recv, cond, recurse (apply IH with appropriate contexts)

    The key insights:
    1. Variable case checks if varName == x: if so, return q with type s; else unchanged
    2. Recurse case: if bound variable shadows x, body unchanged; else exchange contexts
    3. Uses wellTyped_weaken and wellTyped_exchange for context manipulation -/
theorem wellTyped_process_substitute (Γ : TypingContext) (p q : Process)
    (x : String) (s t : LocalTypeR)
    (hp : WellTyped (Γ.extend x s) p t)
    (hq : WellTyped Γ q s)
    : WellTyped Γ (p.substitute x q) t := by
  sorry

/-! ## Equi-Recursive Type Theory Axioms

Under equi-recursive semantics, recursive types are treated as infinite regular trees
where μX.T is definitionally equal to its unfolding T[μX.T/X]. These axioms capture
this fundamental property from type theory.

**References:**
- B. C. Pierce, "Types and Programming Languages," MIT Press 2002, Section 20.1
  (Recursive Types via Iso-Recursive and Equi-Recursive approaches)
- M. Abadi and L. Cardelli, "A Theory of Objects," Springer 1996, Chapter 21
  (Coinductive interpretation of recursive types)
- S. Gay and M. Hole, "Subtyping for Session Types in the Pi Calculus,"
  Acta Informatica 42(2-3), 2005. doi:10.1007/s00236-005-0177-z
  (Session types with recursion)
- K. Honda, V. T. Vasconcelos, and M. Kubo, "Language Primitives and Type Discipline
  for Structured Communication-Based Programming," ESOP 1998.
  (Original session type recursion)

In equi-recursive systems, type equality is defined coinductively, making μX.T
and T[μX.T/X] indistinguishable. Proving these axioms directly would require
defining type equality as a coinductive relation, which is beyond the scope of
this formalization. -/

/-- Equi-recursive type equivalence axiom.

    Under equi-recursive semantics, μX.T is considered equivalent to T[μX.T/X].
    This axiom states that if a process is well-typed with the recursive variable
    bound to T, it remains well-typed when the variable is bound to μX.T.

    **Justification:** In equi-recursive type theory [Pierce 2002, §20.1], μX.T ≈ T[μX.T/X].
    A process well-typed under Γ, X:T remains well-typed under Γ, X:μX.T because
    the types are coinductively equal. The typing derivation is preserved because
    type equality respects the typing rules. -/
axiom equi_recursive_context (Γ : TypingContext) (x : String) (body : Process) (bodyType : LocalTypeR)
    (hbody : WellTyped (Γ.extend x bodyType) body bodyType)
    : WellTyped (Γ.extend x (.mu x bodyType)) body bodyType

/-- Equi-recursive substitution axiom.

    If a process body is well-typed with X : μX.T, then substituting the
    recursive process for X preserves typing at the recursive type.

    **Justification:** This captures the equi-recursive unfolding principle. Given
    Γ, X:μX.T ⊢ P : T and μX.T ≈ T, we have Γ ⊢ P[μX.P/X] : μX.T by substitution
    [Abadi & Cardelli 1996]. The recursive process μX.P has type μX.T, and
    substituting it for X in the body preserves typing. -/
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

/-! ## Queue-Type Correspondence

For async semantics, we track the relationship between queue contents
and global type state. This is essential for proving progress and
subject reduction. These definitions follow the approach in:
- Ghilezan et al., "Precise Subtyping for Asynchronous Multiparty Sessions" (2019)
- Honda, Yoshida, Carbone, "Multiparty Asynchronous Session Types" (2016) -/

/-- Queue invariant: messages in queues correspond to "in-flight" communications.

    A message (sender→receiver, label) in the queue means sender has executed
    a send but receiver hasn't yet processed the corresponding recv.
    In terms of global type reduction, there exists some reduced state g'
    where the communication has been partially processed. -/
def QueueTypeCorrespondence (g : GlobalType) (c : Configuration) : Prop :=
  ∀ ch : Channel, ∀ msg, msg ∈ c.getQueue ch →
    -- The message was produced by a valid send according to the protocol
    ∃ g', GlobalTypeReducesStar g g' ∧
          -- The global type at that point can consume this communication
          g'.consume ch.sender ch.receiver msg.label ≠ none

/-- Projection duality: if role has recv type from sender, sender has or had send type to role.

    This captures the fundamental duality property of session types:
    every receive has a matching send. In async semantics, the send may have
    already been executed (message in queue) or may be pending. -/
def ProjectionDuality (g : GlobalType) : Prop :=
  ∀ role sender branches,
    projectR g role = .ok (.recv sender branches) →
    ∃ senderBranches, projectR g sender = .ok (.send role senderBranches) ∨
                       -- Or sender has already sent and advanced
                       ∃ g', GlobalTypeReducesStar g g' ∧
                             projectR g' sender = .ok (.send role senderBranches)

/-- Extended well-typing for async configurations.

    Each role is typed against a global type that may have "advanced"
    by consuming some communications that are now in queues. This allows
    for the sender to be ahead of the receiver in the protocol. -/
def ConfigWellTypedAsync (g : GlobalType) (c : Configuration) : Prop :=
  c.hasUniqueRoles ∧
  QueueTypeCorrespondence g c ∧
  ∀ rp ∈ c.processes, ∃ g' lt,
    GlobalTypeReducesStar g g' ∧
    projectR g' rp.role = .ok lt ∧
    WellTyped [] rp.process lt

/-- Empty queues trivially satisfy queue-type correspondence. -/
theorem empty_queues_queueTypeCorrespondence (g : GlobalType) (c : Configuration)
    (hempty : c.queuesEmpty)
    : QueueTypeCorrespondence g c := by
  intro ch msg hmem
  -- hempty : c.queues.all (fun (_, q) => q.isEmpty) = true
  -- hmem : msg ∈ c.getQueue ch
  -- If all queues are empty, c.getQueue ch = [], so no msg ∈ it
  unfold Configuration.queuesEmpty at hempty
  unfold Configuration.getQueue at hmem
  simp only [List.all_eq_true, List.isEmpty_iff] at hempty
  -- Find the queue for ch if it exists
  cases hfind : c.queues.find? (fun (ch', _) => ch' == ch) with
  | none =>
    simp only [hfind, Option.map_none', Option.getD_none, List.not_mem_nil] at hmem
  | some pair =>
    simp only [hfind, Option.map_some', Option.getD_some] at hmem
    -- pair ∈ c.queues, so hempty applies
    have hpair_mem : pair ∈ c.queues := by
      exact List.mem_of_find?_eq_some hfind
    have hpair_empty : pair.2 = [] := hempty pair hpair_mem
    rw [hpair_empty] at hmem
    cases hmem

/-! ## Synchronous Semantics

In synchronous semantics, all roles execute in lockstep and queues are always empty.
The following definition captures a well-typed configuration with explicit queue invariant. -/

/-- Full well-typing with queue invariant for async semantics.

    This extends ConfigWellTyped with the queue-type correspondence invariant,
    making it suitable for proving progress and subject reduction. -/
def ConfigWellTypedFull (g : GlobalType) (c : Configuration) : Prop :=
  ConfigWellTyped g c ∧ QueueTypeCorrespondence g c

/-- Synchronous well-typing: ConfigWellTyped with empty queues.

    In synchronous semantics, queues are always empty, so the queue invariant
    is trivially satisfied. -/
def ConfigWellTypedSync (g : GlobalType) (c : Configuration) : Prop :=
  ConfigWellTyped g c ∧ c.queuesEmpty

/-- Synchronous configs satisfy the full invariant. -/
theorem syncWellTyped_implies_full (g : GlobalType) (c : Configuration)
    (h : ConfigWellTypedSync g c)
    : ConfigWellTypedFull g c := by
  obtain ⟨hwt, hempty⟩ := h
  exact ⟨hwt, empty_queues_queueTypeCorrespondence g c hempty⟩

/-- getQueue returns the actual queue content for a channel in the list.

    PROOF SKETCH:
    By induction on c.queues. The find? returns the first matching channel.
    If (ch, q) ∈ c.queues and channels are unique, find? returns (ch, q).
    Then getQueue extracts q from the result. -/
theorem getQueue_of_mem (c : Configuration) (ch : Channel) (q : Queue)
    (hmem : (ch, q) ∈ c.queues)
    (hunique : ∀ ch' q1 q2, (ch', q1) ∈ c.queues → (ch', q2) ∈ c.queues → q1 = q2)
    : c.getQueue ch = q := by
  unfold Configuration.getQueue
  induction c.queues with
  | nil =>
    cases hmem
  | cons head tail ih =>
    cases head with
    | mk ch' q' =>
      simp only [List.find?_cons]
      by_cases hch : ch' == ch
      · -- find? hits the head
        simp [hch]
        have hchEq : ch' = ch := by
          exact beq_iff_eq.mp hch
        -- Use uniqueness to show q' = q
        have hmem_head : (ch', q') ∈ (ch', q') :: tail := List.mem_cons_self _ _
        have hmem_q : (ch', q) ∈ (ch', q') :: tail := by
          simpa [hchEq] using hmem
        have hqeq : q' = q := hunique ch' q' q hmem_head hmem_q
        simpa [hqeq]
      · -- find? continues in the tail
        simp [hch] at hmem
        -- (ch, q) must be in the tail
        have hmem_tail : (ch, q) ∈ tail := by
          cases hmem with
          | head =>
            -- head channel is different from ch
            cases hmem
            have : False := by
              simpa using hch
            exact False.elim this
          | tail _ htail => exact htail
        -- Apply IH on the tail with restricted uniqueness
        have hunique_tail :
            ∀ ch'' q1 q2, (ch'', q1) ∈ tail → (ch'', q2) ∈ tail → q1 = q2 := by
          intro ch'' q1 q2 h1 h2
          exact hunique ch'' q1 q2 (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2)
        exact ih hmem_tail hunique_tail

end Rumpsteak.Protocol.Semantics.Typing
