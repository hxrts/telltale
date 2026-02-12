import SessionTypes.LocalTypeR
import SessionTypes.LocalTypeDB
import SessionTypes.TypeContext

set_option linter.dupNamespace false

set_option linter.unnecessarySimpa false

/-
The Problem. Session types need two representations: named variables (LocalTypeR) for
readability and de Bruijn indices (LocalTypeDB) for clean substitution proofs. Converting
between them requires tracking variable bindings and ensuring closedness is preserved.

Solution Structure. Defines `Context` for name→index lookup during toDB? and `NameContext`
for index→name lookup during fromDB?. Provides `toDB?` converting named types to de Bruijn
with closedness guarantees, and `fromDB`/`fromDB?` converting back with fresh name generation.
-/

/-! # SessionTypes.LocalTypeConvDefs

Definitions for conversions between named variables (LocalTypeR) and de Bruijn indices (LocalTypeDB).
This file contains only core definitions to avoid import cycles.

## Context Types

This module uses `NameOnlyContext` from `TypeContext.lean` for all context operations.
The unified `TypeContext` structure provides a clean API for variable binding contexts.
-/

namespace SessionTypes.LocalTypeConv

open SessionTypes.LocalTypeR
open SessionTypes.LocalTypeDB
open SessionTypes.GlobalType
open SessionTypes

/-! ## Contexts

`Context` and `NameContext` are now unified as `NameOnlyContext`.
-/

abbrev Context := NameOnlyContext
abbrev NameContext := NameOnlyContext

/-! ## Context Operations -/

-- Re-export Membership instance for Context/NameContext abbreviations
instance : Membership String Context := inferInstance
instance : Membership String NameContext := inferInstance

/-- Find the de Bruijn index of a name in the context. -/
def Context.indexOf (ctx : Context) (name : String) : Option Nat :=
  NameOnlyContext.indexOf ctx name

@[simp]
theorem Context.indexOf_eq (ctx : Context) (name : String) :
    Context.indexOf ctx name = NameOnlyContext.indexOf ctx name := rfl

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

/-! ## NameContext Operations -/

/-- Fresh binder names for DB → named conversion (simple scheme). -/
def NameContext.freshName (ctx : NameContext) : String :=
  NameOnlyContext.freshName ctx

/-- Get name at index. -/
def NameContext.get? (ctx : NameContext) (i : Nat) : Option String :=
  NameOnlyContext.get? ctx i

end SessionTypes.LocalTypeConv

/-! ## Conversions -/

namespace SessionTypes.LocalTypeR

open SessionTypes.GlobalType
open SessionTypes

mutual
  def LocalTypeR.toDB? (ctx : SessionTypes.LocalTypeConv.Context) :
      LocalTypeR → Option SessionTypes.LocalTypeDB
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

  def branchesToDB? (ctx : SessionTypes.LocalTypeConv.Context) :
      List BranchR → Option (List (Label × SessionTypes.LocalTypeDB))
    | [] => some []
    | (l, _vt, t) :: rest =>
        match t.toDB? ctx, branchesToDB? ctx rest with
        | some t', some rest' => some ((l, t') :: rest')
        | _, _ => none
  termination_by
    bs => sizeOf bs
end

end SessionTypes.LocalTypeR

namespace SessionTypes.LocalTypeDB

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes

/-! ## Safe Conversions with Option

We provide two safe entry points:
- `fromDB?` - returns `None` for out-of-bounds indices
- `fromDB` - total, but requires a closedness proof (no unchecked names)
-/

mutual
  /-- Safe conversion from DB to named, fails on out-of-bounds indices. -/
  def fromDB? (ctx : SessionTypes.LocalTypeConv.NameContext) :
      SessionTypes.LocalTypeDB → Option LocalTypeR
    | .end => some LocalTypeR.end
    | .var n =>
        (SessionTypes.LocalTypeConv.NameContext.get? ctx n).map LocalTypeR.var
    | .send p bs =>
        branchesFromDB? ctx bs |>.map (LocalTypeR.send p)
    | .recv p bs =>
        branchesFromDB? ctx bs |>.map (LocalTypeR.recv p)
    | .mu body =>
        let fresh := SessionTypes.LocalTypeConv.NameContext.freshName ctx
        (body.fromDB? (NameOnlyContext.cons fresh ctx)).map (LocalTypeR.mu fresh)
  termination_by
    t => sizeOf t

  def branchesFromDB? (ctx : SessionTypes.LocalTypeConv.NameContext) :
      List (Label × SessionTypes.LocalTypeDB) → Option (List BranchR)
    | [] => some []
    | (l, t) :: rest =>
        match t.fromDB? ctx, branchesFromDB? ctx rest with
        | some t', some rest' => some ((l, none, t') :: rest')
        | _, _ => none
  termination_by
    bs => sizeOf bs
end

/-! ## Total Conversion with Closedness Proofs -/

mutual
  /-- Total conversion from DB to named terms, requiring closedness at the given depth. -/
  def fromDB (ctx : SessionTypes.LocalTypeConv.NameContext) :
      (t : SessionTypes.LocalTypeDB) →
      t.isClosedAt ctx.length = true →
      LocalTypeR
    | .end, _ => LocalTypeR.end
    | .var n, hclosed =>
        by
          classical
          -- Closedness ensures the index is in bounds.
          have hlt : n < ctx.length := by
            simpa [SessionTypes.LocalTypeDB.isClosedAt] using hclosed
          have hsome : ∃ v, SessionTypes.NameOnlyContext.get? ctx n = some v :=
            SessionTypes.NameOnlyContext.get?_lt (ctx := ctx) (i := n) hlt
          exact LocalTypeR.var (Classical.choose hsome)
    | .send p bs, hclosed =>
        have hclosed' : isClosedAtBranches ctx.length bs = true := by
          simpa [SessionTypes.LocalTypeDB.isClosedAt] using hclosed
        LocalTypeR.send p (branchesFromDB ctx bs hclosed')
    | .recv p bs, hclosed =>
        have hclosed' : isClosedAtBranches ctx.length bs = true := by
          simpa [SessionTypes.LocalTypeDB.isClosedAt] using hclosed
        LocalTypeR.recv p (branchesFromDB ctx bs hclosed')
    | .mu body, hclosed =>
        let fresh := SessionTypes.LocalTypeConv.NameContext.freshName ctx
        have hclosed' : body.isClosedAt (ctx.length + 1) = true := by
          simpa [SessionTypes.LocalTypeDB.isClosedAt] using hclosed
        have hclosed'' :
            body.isClosedAt (NameOnlyContext.cons fresh ctx).length = true := by
          simp [NameOnlyContext.cons_length, hclosed']
        LocalTypeR.mu fresh (fromDB (NameOnlyContext.cons fresh ctx) body hclosed'')
  termination_by
    t => sizeOf t

  def branchesFromDB (ctx : SessionTypes.LocalTypeConv.NameContext) :
      (bs : List (Label × SessionTypes.LocalTypeDB)) →
      isClosedAtBranches ctx.length bs = true →
      List BranchR
    | [], _ => []
    | (l, t) :: rest, hclosed =>
        have hclosed' :
            t.isClosedAt ctx.length = true ∧
            isClosedAtBranches ctx.length rest = true := by
          simpa [isClosedAtBranches] using hclosed
        (l, none, fromDB ctx t hclosed'.1) ::
          branchesFromDB ctx rest hclosed'.2
  termination_by
    bs => sizeOf bs
end
end SessionTypes.LocalTypeDB
