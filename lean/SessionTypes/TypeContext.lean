import Mathlib.Data.List.Basic

/-!
# Unified Context Infrastructure

This module provides a parametric `TypeContext` structure that unifies the various
context types used throughout Telltale:
- `Context` (named → de Bruijn conversion)
- `NameContext` (de Bruijn → named conversion)
- `Env` (substitution environments)

The key insight is that all these contexts share the same list-based structure
with lookup/extend operations, differing only in their variable and value types.
-/

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

/-! ### Core Operations -/

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

/-! ### Lookup Operations -/

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

/-! ### Properties -/

/-- Context has no duplicate variable names. -/
def Nodup [DecidableEq V] (ctx : TypeContext V T) : Prop := ctx.names.Nodup

/-! ### Basic Lemmas -/

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

/-! ### IndexOf Lemmas -/

theorem indexOf_extend_eq [DecidableEq V] (ctx : TypeContext V T) (v : V) (t : T) :
    (ctx.extend v t).indexOf v = some 0 := by
  simp only [extend, indexOf, List.findIdx?]
  simp only [List.findIdx?.go, decide_eq_true_eq, ↓reduceIte]

/-! ### Get Lemmas -/

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

/-! ## Name-Only Context

Used for conversions between named variables and de Bruijn indices.
The value type is `Unit` since we only care about variable names.
-/

/-- Context containing only variable names (no associated values). -/
abbrev NameOnlyContext := TypeContext String Unit

namespace NameOnlyContext

/-- Convert a list of names to a NameOnlyContext. -/
def fromList (l : List String) : NameOnlyContext := ⟨l.map (·, ())⟩

/-- Convert a NameOnlyContext back to a list of names. -/
def toList (ctx : NameOnlyContext) : List String := ctx.names

/-- Generate a fresh variable name that won't conflict with existing names.
Uses the pattern `_db0`, `_db1`, etc. based on context length. -/
def freshName (ctx : NameOnlyContext) : String :=
  "_db" ++ toString ctx.length

/-! ### Lemmas -/

@[simp]
theorem toList_fromList (l : List String) : (fromList l).toList = l := by
  simp only [fromList, toList, TypeContext.names, List.map_map, Function.comp_def]
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, ih]

@[simp]
theorem length_fromList (l : List String) : (fromList l).length = l.length := by
  simp only [fromList, TypeContext.length, List.length_map]

/-! ### Cons-like operation for easy context extension -/

/-- Extend context with a name (prepends). This mirrors `::` on lists. -/
def cons (v : String) (ctx : NameOnlyContext) : NameOnlyContext :=
  ctx.extend v ()

/-- List-like notation for NameOnlyContext. -/
instance : Coe (List String) NameOnlyContext where
  coe l := fromList l

/-- Convert back to list. -/
instance : Coe NameOnlyContext (List String) where
  coe ctx := ctx.toList

/-! ### fromList cons lemma -/

/-- When we coerce `x :: ctx.toList`, we get `cons x ctx` after fromList.
    This bridges the List syntax to NameOnlyContext operations. -/
@[simp]
theorem fromList_cons_toList (x : String) (ctx : NameOnlyContext) :
    fromList (x :: ctx.toList) = cons x ctx := by
  simp only [fromList, toList, TypeContext.names, cons, TypeContext.extend]
  congr 1
  simp only [List.map_cons, List.map_map, Function.comp_def]
  congr 1
  induction ctx.bindings with
  | nil => rfl
  | cons h t ih => simp [ih]

/-! ### Operations matching List String -/

/-- Get name at index (matches old NameContext.get?). -/
def get? (ctx : NameOnlyContext) (i : Nat) : Option String :=
  ctx.getName? i

/-- Find index of name (matches old Context.indexOf). -/
def indexOf (ctx : NameOnlyContext) (v : String) : Option Nat :=
  ctx.bindings.findIdx? (fun (w, _) => w == v)

/-- Empty context as list notation. -/
@[simp]
theorem empty_toList : toList (TypeContext.empty : NameOnlyContext) = [] := rfl

@[simp]
theorem cons_toList (v : String) (ctx : NameOnlyContext) :
    (cons v ctx).toList = v :: ctx.toList := by
  simp only [cons, toList, TypeContext.names_extend]

@[simp]
theorem cons_length (v : String) (ctx : NameOnlyContext) :
    (cons v ctx).length = ctx.length + 1 :=
  TypeContext.length_extend _ _ _

@[simp]
theorem cons_names (v : String) (ctx : NameOnlyContext) :
    (cons v ctx).names = v :: ctx.names :=
  TypeContext.names_extend _ _ _

@[simp]
theorem cons_bindings (v : String) (ctx : NameOnlyContext) :
    (cons v ctx).bindings = (v, ()) :: ctx.bindings := rfl

@[simp]
theorem empty_length : (TypeContext.empty : NameOnlyContext).length = 0 := rfl

@[simp]
theorem empty_names : (TypeContext.empty : NameOnlyContext).names = [] := rfl

@[simp]
theorem empty_bindings : (TypeContext.empty : NameOnlyContext).bindings = [] := rfl

/-! ### Induction Principle -/

/-- Induction principle for NameOnlyContext that mirrors List String induction.
    This allows `induction ctx using NameOnlyContext.induction` to work like
    `induction ctx with | nil => | cons a ctx ih =>` on lists. -/
theorem induction {motive : NameOnlyContext → Prop}
    (h_empty : motive TypeContext.empty)
    (h_cons : ∀ (v : String) (ctx : NameOnlyContext), motive ctx → motive (cons v ctx)) :
    ∀ ctx, motive ctx := by
  intro ⟨bindings⟩
  induction bindings with
  | nil => exact h_empty
  | cons head tail ih =>
      obtain ⟨v, u⟩ := head
      have hu : u = () := rfl
      subst hu
      exact h_cons v ⟨tail⟩ ih

/-! ### Append Operation -/

/-- Append two NameOnlyContexts. -/
def append (ctx1 ctx2 : NameOnlyContext) : NameOnlyContext :=
  ⟨ctx1.bindings ++ ctx2.bindings⟩

instance : Append NameOnlyContext where
  append := append

@[simp]
theorem append_length (ctx1 ctx2 : NameOnlyContext) :
    (ctx1 ++ ctx2).length = ctx1.length + ctx2.length := by
  show (ctx1.bindings ++ ctx2.bindings).length = _
  simp [TypeContext.length]

@[simp]
theorem append_names (ctx1 ctx2 : NameOnlyContext) :
    (ctx1 ++ ctx2).names = ctx1.names ++ ctx2.names := by
  show (ctx1.bindings ++ ctx2.bindings).map Prod.fst = _
  simp [TypeContext.names]

@[simp]
theorem append_bindings (ctx1 ctx2 : NameOnlyContext) :
    (ctx1 ++ ctx2).bindings = ctx1.bindings ++ ctx2.bindings := rfl

/-! ### Nodup Lemmas -/

theorem Nodup_empty : (TypeContext.empty : NameOnlyContext).Nodup := by
  simp [TypeContext.Nodup, TypeContext.names_empty, List.nodup_nil]

theorem Nodup_cons {v : String} {ctx : NameOnlyContext}
    (hv : v ∉ ctx.names) (hnd : ctx.Nodup) : (cons v ctx).Nodup := by
  simp only [TypeContext.Nodup, cons_names]
  exact List.nodup_cons.mpr ⟨hv, hnd⟩

theorem Nodup_tail {v : String} {ctx : NameOnlyContext}
    (h : (cons v ctx).Nodup) : ctx.Nodup := by
  simp only [TypeContext.Nodup, cons_names] at h
  exact h.tail

theorem notMem_of_Nodup_cons {v : String} {ctx : NameOnlyContext}
    (h : (cons v ctx).Nodup) : v ∉ ctx.names := by
  simp only [TypeContext.Nodup, cons_names] at h
  exact (List.nodup_cons.mp h).1

/-! ### Get/Name Lemmas -/

@[simp]
theorem get?_cons_zero (v : String) (ctx : NameOnlyContext) :
    (cons v ctx).get? 0 = some v := by
  simp only [get?, TypeContext.getName?, cons_bindings, List.getElem?_cons_zero]
  rfl

@[simp]
theorem get?_cons_succ (v : String) (ctx : NameOnlyContext) (i : Nat) :
    (cons v ctx).get? (i + 1) = ctx.get? i := by
  simp only [get?, TypeContext.getName?, cons_bindings, List.getElem?_cons_succ]

theorem get?_mem {ctx : NameOnlyContext} {i : Nat} {v : String}
    (h : ctx.get? i = some v) : v ∈ ctx.names := by
  induction ctx using induction generalizing i with
  | h_empty =>
      simp [get?, TypeContext.getName?, TypeContext.bindings_empty] at h
  | h_cons a ctx ih =>
      cases i with
      | zero =>
          simp only [get?_cons_zero] at h
          simp only [cons_names, List.mem_cons]
          left
          exact (Option.some.inj h).symm
      | succ i =>
          simp only [get?_cons_succ] at h
          simp only [cons_names, List.mem_cons]
          right
          exact ih h

theorem get?_lt {ctx : NameOnlyContext} {i : Nat} (h : i < ctx.length) :
    ∃ v, ctx.get? i = some v := by
  induction ctx using induction generalizing i with
  | h_empty =>
      simp at h
  | h_cons a ctx ih =>
      cases i with
      | zero => exact ⟨a, get?_cons_zero a ctx⟩
      | succ i =>
          have h' : i < ctx.length := by simpa using h
          exact ih h'

/-! ### IndexOf Lemmas -/

private theorem findIdx?_go_succ (p : String × Unit → Bool) (l : List (String × Unit)) (i : Nat) :
    List.findIdx?.go p l (i + 1) = Option.map Nat.succ (List.findIdx?.go p l i) := by
  induction l generalizing i with
  | nil => rfl
  | cons head tail ih =>
      unfold List.findIdx?.go
      split
      · rfl
      · have h := ih (i + 1)
        simp only [Nat.add_assoc] at h
        exact h

theorem indexOf_cons_eq (v : String) (ctx : NameOnlyContext) :
    (cons v ctx).indexOf v = some 0 := by
  simp only [indexOf, cons_bindings, List.findIdx?, List.findIdx?.go]
  simp only [beq_self_eq_true, ↓reduceIte]

theorem indexOf_cons_ne {v a : String} (ctx : NameOnlyContext) (hne : a ≠ v) :
    (cons a ctx).indexOf v = Option.map Nat.succ (ctx.indexOf v) := by
  simp only [indexOf, cons_bindings, List.findIdx?, List.findIdx?.go]
  have hneq : (a == v) = false := by simp [hne]
  simp only [hneq]
  exact findIdx?_go_succ (fun w => w.1 == v) ctx.bindings 0

theorem indexOf_get? {ctx : NameOnlyContext} {v : String} {i : Nat}
    (h : ctx.indexOf v = some i) : ctx.get? i = some v := by
  induction ctx using induction generalizing i with
  | h_empty => simp [indexOf, List.findIdx?, List.findIdx?.go] at h
  | h_cons a ctx ih =>
      by_cases hav : a = v
      · subst hav
        simp only [indexOf_cons_eq] at h
        cases h
        simp [get?_cons_zero]
      · simp only [indexOf_cons_ne ctx hav] at h
        cases hi : ctx.indexOf v with
        | none => simp [hi] at h
        | some j =>
            simp only [hi, Option.map] at h
            cases h
            simp only [get?_cons_succ]
            exact ih hi

theorem indexOf_lt {ctx : NameOnlyContext} {v : String} {i : Nat}
    (h : ctx.indexOf v = some i) : i < ctx.length := by
  induction ctx using induction generalizing i with
  | h_empty => simp [indexOf, List.findIdx?, List.findIdx?.go] at h
  | h_cons a ctx ih =>
      by_cases hav : a = v
      · subst hav
        simp only [indexOf_cons_eq] at h
        cases h
        simp [cons_length]
      · simp only [indexOf_cons_ne ctx hav] at h
        cases hi : ctx.indexOf v with
        | none => simp [hi] at h
        | some j =>
            simp only [hi, Option.map] at h
            cases h
            simp only [cons_length]
            exact Nat.succ_lt_succ (ih hi)

theorem indexOf_eq_none_iff {ctx : NameOnlyContext} {v : String} :
    ctx.indexOf v = none ↔ v ∉ ctx.names := by
  induction ctx using induction with
  | h_empty => simp [indexOf, List.findIdx?, List.findIdx?.go]
  | h_cons a ctx ih =>
      simp only [cons_names, List.mem_cons]
      by_cases hav : a = v
      · subst hav
        simp only [indexOf_cons_eq, Option.some_ne_none, true_or, not_true_eq_false]
      · constructor
        · intro h
          simp only [indexOf_cons_ne ctx hav] at h
          cases hctx : ctx.indexOf v with
          | none =>
              push_neg
              exact ⟨Ne.symm hav, ih.mp hctx⟩
          | some i =>
              simp [hctx] at h
        · intro h
          push_neg at h
          simp only [indexOf_cons_ne ctx hav]
          cases hctx : ctx.indexOf v with
          | none => rfl
          | some i =>
              have hmem : v ∈ ctx.names := by
                have hget := indexOf_get? hctx
                exact get?_mem hget
              exact (h.2 hmem).elim

theorem indexOf_mem {ctx : NameOnlyContext} {v : String} (hmem : v ∈ ctx.names) :
    ∃ i, ctx.indexOf v = some i := by
  by_contra h
  push_neg at h
  have hnone : ctx.indexOf v = none := by
    cases hctx : ctx.indexOf v with
    | none => rfl
    | some i => exact (h i hctx).elim
  exact (indexOf_eq_none_iff.mp hnone) hmem

/-! ### Membership instance -/

/-- String membership in NameOnlyContext: a string is in a context if it's in the names list. -/
instance instMembershipStringNameOnlyContext : Membership String NameOnlyContext where
  mem := fun (ctx : NameOnlyContext) (v : String) => List.Mem v ctx.names

/-! ### Roundtrip and Distribution Lemmas for Coercion -/

/-- Roundtrip: fromList ∘ toList = id -/
@[simp]
theorem fromList_toList (ctx : NameOnlyContext) : fromList ctx.toList = ctx := by
  simp only [fromList, toList, TypeContext.names]
  congr 1
  induction ctx.bindings with
  | nil => rfl
  | cons h t ih => simp [ih]

/-- toList distributes over append -/
@[simp]
theorem toList_append (ctx1 ctx2 : NameOnlyContext) :
    (ctx1 ++ ctx2).toList = ctx1.toList ++ ctx2.toList := by
  simp only [toList, TypeContext.names, append_bindings, List.map_append]

/-- fromList distributes over append -/
@[simp]
theorem fromList_append (xs ys : List String) :
    fromList (xs ++ ys) = fromList xs ++ fromList ys := by
  show (⟨_⟩ : NameOnlyContext) = _
  congr 1
  simp only [List.map_append, fromList]

/-- cons of (toList) simplifies -/
@[simp]
theorem fromList_cons (x : String) (xs : List String) :
    fromList (x :: xs) = cons x (fromList xs) := by
  simp only [fromList, cons, TypeContext.extend, List.map_cons]

/-- Decidable equality for NameOnlyContext membership. -/
instance instDecidableMemStringNameOnlyContext (v : String) (ctx : NameOnlyContext) :
    Decidable (v ∈ ctx) :=
  inferInstanceAs (Decidable (v ∈ ctx.names))

@[simp]
theorem mem_iff_mem_names (v : String) (ctx : NameOnlyContext) : v ∈ ctx ↔ v ∈ ctx.names := Iff.rfl

@[simp]
theorem mem_cons_iff (v a : String) (ctx : NameOnlyContext) :
    v ∈ cons a ctx ↔ v = a ∨ v ∈ ctx := by
  simp only [mem_iff_mem_names, cons_names, List.mem_cons]

theorem mem_cons_self (v : String) (ctx : NameOnlyContext) : v ∈ cons v ctx := by
  simp only [mem_cons_iff, true_or]

theorem mem_cons_of_mem (v a : String) (ctx : NameOnlyContext) (h : v ∈ ctx) :
    v ∈ cons a ctx := by
  simp only [mem_cons_iff]
  right
  exact h

end NameOnlyContext

/-- Membership instance outside namespace to ensure global visibility.
    This helps with abbreviations like `Context := NameOnlyContext`. -/
instance : Membership String NameOnlyContext := NameOnlyContext.instMembershipStringNameOnlyContext

end SessionTypes
