import Mathlib.Data.List.Basic

/-
The Problem. Multiple context types (for named↔de Bruijn conversion, substitution environments)
share the same list-based structure but were defined separately, leading to duplicated lemmas
and awkward conversions between representations.

Solution Structure. Defines parametric `TypeContext V T` with generic lookup/extend operations.
`NameOnlyContext` specializes for name-only contexts with fresh name generation. Provides
`indexOf`, `get?`, `Nodup` predicates with comprehensive lemmas. Coercion instances enable
seamless conversion between `List String` and `NameOnlyContext`.
-/

/-! # Unified Context Infrastructure

This module provides a parametric `TypeContext` structure that unifies the various
context types used throughout Telltale:
- `Context` (named → de Bruijn conversion)
- `NameContext` (de Bruijn → named conversion)
- `Env` (substitution environments)

The key insight is that all these contexts share the same list-based structure
with lookup/extend operations, differing only in their variable and value types. -/

namespace SessionTypes

/-! ## Generic TypeContext -/

/-- Parametric context for variable bindings.

`V` is the variable/key type (usually `String` or `Nat`)
`T` is the value type (usually `Unit`, `LocalTypeR`, or `LocalTypeDB`)
-/
structure TypeContext (V : Type) (T : Type) where
  bindings : List (V × T)
  deriving Repr, DecidableEq

namespace TypeContext

variable {V T : Type}

/-! ## Core Operations -/

/-- Empty context. -/
def empty : TypeContext V T := ⟨[]⟩

/-- Extend context with a new binding (prepends to front). -/
def extend (ctx : TypeContext V T) (v : V) (t : T) : TypeContext V T :=
  ⟨(v, t) :: ctx.bindings⟩

/-- Number of bindings in context. -/
def length (ctx : TypeContext V T) : Nat := ctx.bindings.length

/-- Extract all variable names. -/
def names (ctx : TypeContext V T) : List V := ctx.bindings.map Prod.fst

/-- Extract all values. -/
def values (ctx : TypeContext V T) : List T := ctx.bindings.map Prod.snd

/-! ## Lookup Operations -/

/-- Look up a variable and return its associated value. -/
def lookup [DecidableEq V] (ctx : TypeContext V T) (v : V) : Option T :=
  ctx.bindings.lookup v

/-- Find the index of a variable (de Bruijn index). -/
def indexOf [DecidableEq V] (ctx : TypeContext V T) (v : V) : Option Nat :=
  ctx.bindings.findIdx? (fun (w, _) => w = v)

/-- Get the binding at a given index. -/
def get? (ctx : TypeContext V T) (i : Nat) : Option (V × T) :=
  ctx.bindings[i]?

/-- Get the value at a given index. -/
def getVal? (ctx : TypeContext V T) (i : Nat) : Option T :=
  ctx.bindings[i]? |>.map Prod.snd

/-- Get the variable name at a given index. -/
def getName? (ctx : TypeContext V T) (i : Nat) : Option V :=
  ctx.bindings[i]? |>.map Prod.fst

/-! ## Properties -/

/-- Context has no duplicate variable names. -/
def Nodup [DecidableEq V] (ctx : TypeContext V T) : Prop := ctx.names.Nodup

/-! ## Basic Lemmas -/

@[simp]
theorem length_empty : (empty : TypeContext V T).length = 0 := rfl

@[simp]
theorem length_extend (ctx : TypeContext V T) (v : V) (t : T) :
    (ctx.extend v t).length = ctx.length + 1 := by
  simp only [extend, length, List.length_cons]

@[simp]
theorem names_empty : (empty : TypeContext V T).names = [] := rfl

@[simp]
theorem names_extend (ctx : TypeContext V T) (v : V) (t : T) :
    (ctx.extend v t).names = v :: ctx.names := by
  simp only [extend, names, List.map_cons]

@[simp]
theorem bindings_empty : (empty : TypeContext V T).bindings = [] := rfl

@[simp]
theorem bindings_extend (ctx : TypeContext V T) (v : V) (t : T) :
    (ctx.extend v t).bindings = (v, t) :: ctx.bindings := rfl

theorem mem_names_extend_self (ctx : TypeContext V T) (v : V) (t : T) :
    v ∈ (ctx.extend v t).names := by
  simp only [names_extend, List.mem_cons, true_or]

theorem mem_names_extend_of_mem (ctx : TypeContext V T) (v w : V) (t : T)
    (h : v ∈ ctx.names) : v ∈ (ctx.extend w t).names := by
  simp only [names_extend, List.mem_cons]
  right
  exact h

/-! ## IndexOf Lemmas -/

theorem indexOf_extend_eq [DecidableEq V] (ctx : TypeContext V T) (v : V) (t : T) :
    (ctx.extend v t).indexOf v = some 0 := by
  simp only [extend, indexOf, List.findIdx?]
  simp only [List.findIdx?.go, decide_eq_true_eq, ↓reduceIte]

/-! ## Get Lemmas -/

theorem getName?_lt (ctx : TypeContext V T) (i : Nat) (h : i < ctx.length) :
    ∃ v, ctx.getName? i = some v := by
  simp only [getName?, length] at *
  have hget : (ctx.bindings[i]?).isSome := by
    rw [Option.isSome_iff_exists]
    exact ⟨ctx.bindings[i], List.getElem?_eq_getElem h⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hget
  exact ⟨p.1, by simp only [hp]; rfl⟩

theorem get?_lt (ctx : TypeContext V T) (i : Nat) (h : i < ctx.length) :
    ∃ p, ctx.get? i = some p := by
  simp only [get?, length] at *
  exact ⟨ctx.bindings[i], List.getElem?_eq_getElem h⟩

end TypeContext


end SessionTypes
