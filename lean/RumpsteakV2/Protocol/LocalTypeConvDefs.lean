import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.LocalTypeDB
import RumpsteakV2.Protocol.TypeContext

set_option linter.dupNamespace false

set_option linter.unnecessarySimpa false

/-! # RumpsteakV2.Protocol.LocalTypeConvDefs

Definitions for conversions between named variables (LocalTypeR) and de Bruijn indices (LocalTypeDB).
This file contains only core definitions to avoid import cycles.

## Context Types

This module uses `NameOnlyContext` from `TypeContext.lean` for all context operations.
The unified `TypeContext` structure provides a clean API for variable binding contexts.
-/

namespace RumpsteakV2.Protocol.LocalTypeConv

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.LocalTypeDB
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol

/-! ## Contexts

`Context` and `NameContext` are now unified as `NameOnlyContext`.
-/

abbrev Context := NameOnlyContext
abbrev NameContext := NameOnlyContext

/-! ### Context Operations -/

-- Re-export Membership instance for Context/NameContext abbreviations
instance : Membership String Context := inferInstance
instance : Membership String NameContext := inferInstance

/-- Find the de Bruijn index of a name in the context. -/
def Context.indexOf (ctx : Context) (name : String) : Option Nat :=
  NameOnlyContext.indexOf ctx name

/-- Coverage: all free variables are in the context. -/
def Context.Covers (ctx : Context) (t : LocalTypeR) : Prop :=
  ∀ v, v ∈ t.freeVars → v ∈ ctx

theorem Context.covers_of_closed (ctx : Context) (t : LocalTypeR) :
    t.isClosed = true → Context.Covers ctx t := by
  intro hclosed v hv
  have hclosed' : t.freeVars.isEmpty = true := by
    simpa [LocalTypeR.isClosed] using hclosed
  have hfv : t.freeVars = [] := by
    cases h : t.freeVars with
    | nil => rfl
    | cons x xs =>
        have hfalse : False := by
          have : (List.isEmpty (x :: xs)) = true := by
            simpa [h] using hclosed'
          simpa [List.isEmpty] using this
        cases hfalse
  have hv' : False := by
    simpa [hfv] using hv
  exact hv'.elim

theorem Context.covers_of_closed_singleton (t : String) (body : LocalTypeR) :
    body.isClosed = true → Context.Covers (NameOnlyContext.cons t TypeContext.empty) body := by
  intro hclosed v hv
  have hcov := Context.covers_of_closed (NameOnlyContext.cons t TypeContext.empty) body hclosed
  exact hcov v hv

theorem Context.covers_of_mu_closed_singleton (t : String) (body : LocalTypeR) :
    (LocalTypeR.mu t body).isClosed = true → Context.Covers (NameOnlyContext.cons t TypeContext.empty) body := by
  intro hclosed v hv
  by_cases hvt : v = t
  · simp only [hvt]
    exact NameOnlyContext.mem_cons_self t TypeContext.empty
  · have hclosed' : (body.freeVars.filter (· != t)).isEmpty = true := by
      simpa only [LocalTypeR.isClosed, LocalTypeR.freeVars] using hclosed
    have hnil : body.freeVars.filter (· != t) = [] :=
      (List.isEmpty_eq_true _).1 hclosed'
    have hfilter : v ∈ body.freeVars.filter (· != t) := by
      simpa [List.mem_filter, hv, hvt] using hv
    have : False := by
      simpa [hnil] using hfilter
    exact this.elim

/-! ### NameContext Operations -/

/-- Fresh binder names for DB → named conversion (simple scheme). -/
def NameContext.freshName (ctx : NameContext) : String :=
  NameOnlyContext.freshName ctx

/-- Get name at index. -/
def NameContext.get? (ctx : NameContext) (i : Nat) : Option String :=
  NameOnlyContext.get? ctx i

end RumpsteakV2.Protocol.LocalTypeConv

/-! ## Conversions -/

namespace RumpsteakV2.Protocol.LocalTypeR

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol

mutual
  def LocalTypeR.toDB? (ctx : RumpsteakV2.Protocol.LocalTypeConv.Context) :
      LocalTypeR → Option RumpsteakV2.Protocol.LocalTypeDB
    | .end => some .end
    | .var v =>
        (NameOnlyContext.indexOf ctx v).map LocalTypeDB.var
    | .send p bs =>
        branchesToDB? ctx bs |>.map (fun bs' => .send p bs')
    | .recv p bs =>
        branchesToDB? ctx bs |>.map (fun bs' => .recv p bs')
    | .mu t body =>
        (body.toDB? (NameOnlyContext.cons t ctx)).map (fun body' => .mu body')
  termination_by
    t => sizeOf t

  def branchesToDB? (ctx : RumpsteakV2.Protocol.LocalTypeConv.Context) :
      List (Label × LocalTypeR) → Option (List (Label × RumpsteakV2.Protocol.LocalTypeDB))
    | [] => some []
    | (l, t) :: rest =>
        match t.toDB? ctx, branchesToDB? ctx rest with
        | some t', some rest' => some ((l, t') :: rest')
        | _, _ => none
  termination_by
    bs => sizeOf bs
end

end RumpsteakV2.Protocol.LocalTypeR

namespace RumpsteakV2.Protocol.LocalTypeDB

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol

/-! ## Safe Conversions with Option

The previous `fromDB` was total but could generate synthetic variable names for
out-of-bounds indices. We now provide both:
- `fromDB?` - Safe version that returns `None` for out-of-bounds indices
- `fromDB` - Unsafe version kept for backward compatibility (generates synthetic names)
-/

mutual
  /-- Safe conversion from DB to named, fails on out-of-bounds indices. -/
  def fromDB? (ctx : RumpsteakV2.Protocol.LocalTypeConv.NameContext) :
      RumpsteakV2.Protocol.LocalTypeDB → Option LocalTypeR
    | .end => some LocalTypeR.end
    | .var n =>
        (RumpsteakV2.Protocol.LocalTypeConv.NameContext.get? ctx n).map LocalTypeR.var
    | .send p bs =>
        branchesFromDB? ctx bs |>.map (LocalTypeR.send p)
    | .recv p bs =>
        branchesFromDB? ctx bs |>.map (LocalTypeR.recv p)
    | .mu body =>
        let fresh := RumpsteakV2.Protocol.LocalTypeConv.NameContext.freshName ctx
        (body.fromDB? (NameOnlyContext.cons fresh ctx)).map (LocalTypeR.mu fresh)
  termination_by
    t => sizeOf t

  def branchesFromDB? (ctx : RumpsteakV2.Protocol.LocalTypeConv.NameContext) :
      List (Label × RumpsteakV2.Protocol.LocalTypeDB) → Option (List (Label × LocalTypeR))
    | [] => some []
    | (l, t) :: rest =>
        match t.fromDB? ctx, branchesFromDB? ctx rest with
        | some t', some rest' => some ((l, t') :: rest')
        | _, _ => none
  termination_by
    bs => sizeOf bs
end

mutual
  /-- Unsafe conversion (backward compatibility): generates synthetic names for out-of-bounds indices.

  **Warning**: This function is unsafe and should only be used when you can guarantee that all
  indices are in bounds (e.g., for closed terms with empty context, or when the context is known
  to be adequate). Prefer `fromDB?` for new code. -/
  def fromDB (ctx : RumpsteakV2.Protocol.LocalTypeConv.NameContext) :
      RumpsteakV2.Protocol.LocalTypeDB → LocalTypeR
    | .end => LocalTypeR.end
    | .var n =>
        match RumpsteakV2.Protocol.LocalTypeConv.NameContext.get? ctx n with
        | some v => LocalTypeR.var v
        | none => LocalTypeR.var ("_UNSAFE_db" ++ toString n)  -- Mark as unsafe
    | .send p bs => LocalTypeR.send p (branchesFromDB ctx bs)
    | .recv p bs => LocalTypeR.recv p (branchesFromDB ctx bs)
    | .mu body =>
        let fresh := RumpsteakV2.Protocol.LocalTypeConv.NameContext.freshName ctx
        LocalTypeR.mu fresh (body.fromDB (NameOnlyContext.cons fresh ctx))
  termination_by
    t => sizeOf t

  def branchesFromDB (ctx : RumpsteakV2.Protocol.LocalTypeConv.NameContext) :
      List (Label × RumpsteakV2.Protocol.LocalTypeDB) → List (Label × LocalTypeR)
    | [] => []
    | (l, t) :: rest => (l, t.fromDB ctx) :: branchesFromDB ctx rest
  termination_by
    bs => sizeOf bs
end
end RumpsteakV2.Protocol.LocalTypeDB
