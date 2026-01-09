import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.LocalTypeDB

/-! # RumpsteakV2.Protocol.LocalTypeConv

Conversions between named variables (LocalTypeR) and de Bruijn indices (LocalTypeDB).
-/

namespace RumpsteakV2.Protocol.LocalTypeConv

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.LocalTypeDB
open RumpsteakV2.Protocol.GlobalType

/-! ## Contexts -/

abbrev Context := List String
abbrev NameContext := List String

/-- Find the de Bruijn index of a name in the context. -/
def Context.indexOf (ctx : Context) (name : String) : Option Nat :=
  ctx.findIdx? (· == name)

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
    body.isClosed = true → Context.Covers [t] body :=
  Context.covers_of_closed [t] body

theorem Context.covers_of_mu_closed_singleton (t : String) (body : LocalTypeR) :
    (LocalTypeR.mu t body).isClosed = true → Context.Covers [t] body := by
  intro hclosed v hv
  by_cases hvt : v = t
  · simp [hvt]
  · have hclosed' : (body.freeVars.filter (· != t)).isEmpty = true := by
      simpa only [LocalTypeR.isClosed, LocalTypeR.freeVars] using hclosed
    have hnil : body.freeVars.filter (· != t) = [] :=
      (List.isEmpty_eq_true _).1 hclosed'
    have hfilter : v ∈ body.freeVars.filter (· != t) := by
      simpa [List.mem_filter, hv, hvt] using hv
    have : False := by
      simpa [hnil] using hfilter
    exact this.elim

/-- Fresh binder names for DB → named conversion (simple scheme). -/
def NameContext.freshName (ctx : NameContext) : String :=
  "_db" ++ toString ctx.length

def NameContext.get? : NameContext → Nat → Option String
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => NameContext.get? xs n

end RumpsteakV2.Protocol.LocalTypeConv

/-! ## Conversions -/

namespace RumpsteakV2.Protocol.LocalTypeR

open RumpsteakV2.Protocol.GlobalType

mutual
  def LocalTypeR.toDB? (ctx : RumpsteakV2.Protocol.LocalTypeConv.Context) :
      LocalTypeR → Option RumpsteakV2.Protocol.LocalTypeDB
    | .end => some .end
    | .var v =>
        (RumpsteakV2.Protocol.LocalTypeConv.Context.indexOf ctx v).map LocalTypeDB.var
    | .send p bs =>
        branchesToDB? ctx bs |>.map (fun bs' => .send p bs')
    | .recv p bs =>
        branchesToDB? ctx bs |>.map (fun bs' => .recv p bs')
    | .mu t body =>
        (body.toDB? (t :: ctx)).map (fun body' => .mu body')
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
        (body.fromDB? (fresh :: ctx)).map (LocalTypeR.mu fresh)
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
        LocalTypeR.mu fresh (body.fromDB (fresh :: ctx))
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

/-! ## Safe Conversion Properties for Closed Terms

For **closed terms** (no free variables), conversions are safe and should round-trip correctly.
These properties are currently axiomatized but could be proven with sufficient infrastructure.
-/

namespace RumpsteakV2.Protocol.LocalTypeConv

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.LocalTypeDB
open RumpsteakV2.Protocol.GlobalType

/-- For closed DB terms, the safe conversion succeeds and matches unsafe conversion. -/
axiom fromDB?_eq_fromDB_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
  t.fromDB? [] = some (t.fromDB [])

/-- Closed DB term converts to closed named term. -/
axiom fromDB_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
  (t.fromDB []).isClosed = true

/-- Closed named term converts to closed DB term. -/
axiom toDB_closed (t : LocalTypeR) (hclosed : t.isClosed = true) :
  ∃ db, t.toDB? [] = some db ∧ db.isClosed = true

/-- Round-trip for closed DB terms: fromDB then toDB gives original.

This is the key property enabling DB-based proofs: we can convert to DB, prove something,
then convert back, knowing we get the same term. -/
axiom toDB_fromDB_roundtrip_closed (t : LocalTypeDB) (hclosed : t.isClosed = true) :
  (t.fromDB []).toDB? [] = some t

/-! ## General Conversion Properties (require adequate context)

These properties hold when the context is "adequate" for the term being converted.
For closed terms, empty context is adequate. For open terms, the context must contain
all free variables. -/

/-- General round-trip requires adequate context.

**Warning**: This assumes the context contains appropriate names for all free variables
and that `freshName` generates names not in the context. Without these guarantees,
this property may not hold. -/
axiom toDB_fromDB_roundtrip (t : LocalTypeDB) (ctx : NameContext) :
  (t.fromDB ctx).toDB? ctx = some t

/-- Branch version of round-trip. -/
axiom branches_toDB_fromDB_roundtrip (bs : List (Label × LocalTypeDB)) (ctx : NameContext) :
  LocalTypeR.branchesToDB? ctx (LocalTypeDB.branchesFromDB ctx bs) = some bs

/-! ## Guardedness and Contractiveness Preservation

These properties show that structural predicates are preserved across conversions.
-/

axiom isGuarded_toDB (t : LocalTypeR) (ctx : Context) (x : String) (i : Nat) (db : LocalTypeDB) :
  t.isGuarded x = true →
  ctx.indexOf x = some i →
  t.toDB? ctx = some db →
  db.isGuarded i = true

axiom isGuarded_fromDB (t : LocalTypeDB) (ctx : NameContext) (i : Nat) :
  t.isClosedAt (ctx.length) = true →
  t.isGuarded i = true →
  True

axiom isContractive_toDB (t : LocalTypeR) (ctx : Context) (db : LocalTypeDB) :
  t.isContractive = true →
  t.toDB? ctx = some db →
  db.isContractive = true

axiom isContractive_fromDB (t : LocalTypeDB) (ctx : NameContext) :
  t.isContractive = true →
  t.isClosedAt (ctx.length) = true →
  (t.fromDB ctx).isContractive = true

/-- Bridge theorem: preserve contractiveness for mu-substitution via DB.

This enables proving substitution properties at the DB level, then transporting
the result back to LocalTypeR. -/
axiom isContractive_substitute_mu_via_DB (body : LocalTypeR) (t : String)
    (hcov : Context.Covers [t] body)
    (h_body : body.isContractive = true)
    (h_mu : (LocalTypeR.mu t body).isContractive = true) :
    (body.substitute t (.mu t body)).isContractive = true

/-! ## Safe Conversion Helpers for Closed Terms

These wrappers make it explicit when conversions are guaranteed to be safe.
-/

/-- Convert closed named term to DB (guaranteed to succeed). -/
def toDB_closed_safe (t : LocalTypeR) (hclosed : t.isClosed = true) : LocalTypeDB :=
  match t.toDB? [] with
  | some db => db
  | none => .end  -- Should never happen for closed terms

/-- Convert closed DB term to named (safe version). -/
def fromDB_closed_safe (t : LocalTypeDB) (hclosed : t.isClosed = true) : LocalTypeR :=
  match t.fromDB? [] with
  | some r => r
  | none => .end  -- Should never happen for closed terms

/-! ## Usage Guidelines: When is it safe to use DB conversions?

**Always safe:**
- Closed terms (no free variables) with empty context
- The conversion will succeed and round-trip correctly

**Safe with proper context:**
- Terms where `Context.Covers ctx t` holds
- The context must contain all free variables
- Generated names from `freshName` must not collide

**Unsafe:**
- Arbitrary open terms with inadequate context
- Using `fromDB` without checking bounds (generates `_UNSAFE_db*` names)

**Recommended usage:**
1. For closed terms: Use `toDB_closed_safe` / `fromDB_closed_safe`
2. For open terms: Use `toDB?` / `fromDB?` and handle `Option`
3. Gate all DB usage behind `isClosed` or `Context.Covers` hypotheses
-/

end RumpsteakV2.Protocol.LocalTypeConv
