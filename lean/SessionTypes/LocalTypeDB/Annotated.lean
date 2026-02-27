import SessionTypes.LocalTypeR
import SessionTypes.LocalTypeDB.Core
import SessionTypes.TypeContext

set_option autoImplicit false

/-! # SessionTypes.LocalTypeDB.Annotated

Experimental payload-preserving de Bruijn surface for local types.

This module is intentionally proof-light and executable. It preserves
`Option ValType` payload annotations on local branches to support parity-sensitive
serialization and cross-language checks.
-/

/-!
The Problem. Legacy de Bruijn conversion erases branch payload annotations, but
parity-sensitive serialization and cross-language checks need those annotations.

Solution Structure. Introduce an executable payload-preserving de Bruijn surface,
provide conversions to and from named local types, closedness checks, and a
deterministic payload-erasure projection back to the legacy de Bruijn surface.
-/

namespace SessionTypes

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes (ValType)

/-! ## Payload-Preserving Syntax -/

/-- Payload-preserving de Bruijn local types. -/
inductive LocalTypeDBAnn where
  | end : LocalTypeDBAnn
  | var : Nat → LocalTypeDBAnn
  | send : String → List (Label × Option ValType × LocalTypeDBAnn) → LocalTypeDBAnn
  | recv : String → List (Label × Option ValType × LocalTypeDBAnn) → LocalTypeDBAnn
  | mu : LocalTypeDBAnn → LocalTypeDBAnn
  deriving Repr, Inhabited

abbrev NameContext := SessionTypes.NameOnlyContext

/-! ## Named-to-de-Bruijn Conversion -/

mutual
  /-- Convert named local types to payload-preserving de Bruijn form. -/
  def LocalTypeR.toDBAnn? : NameContext → LocalTypeR → Option LocalTypeDBAnn
    | _, .end => some .end
    | ctx, .var v => (SessionTypes.NameOnlyContext.indexOf ctx v).map LocalTypeDBAnn.var
    | ctx, .mu v body =>
        (LocalTypeR.toDBAnn? (SessionTypes.NameOnlyContext.cons v ctx) body).map LocalTypeDBAnn.mu
    | ctx, .send p bs =>
        (LocalTypeR.branchesToDBAnn? ctx bs).map (LocalTypeDBAnn.send p)
    | ctx, .recv p bs =>
        (LocalTypeR.branchesToDBAnn? ctx bs).map (LocalTypeDBAnn.recv p)

  /-- Convert branch lists to payload-preserving de Bruijn form. -/
  def LocalTypeR.branchesToDBAnn? :
      NameContext → List BranchR → Option (List (Label × Option ValType × LocalTypeDBAnn))
    | _, [] => some []
    | ctx, (lbl, vt, cont) :: rest => do
        let cont' ← LocalTypeR.toDBAnn? ctx cont
        let rest' ← LocalTypeR.branchesToDBAnn? ctx rest
        pure ((lbl, vt, cont') :: rest')
end

/-! ## de-Bruijn-to-Named Conversion -/

mutual
  /-- Convert payload-preserving de Bruijn form back to named local types. -/
  def LocalTypeDBAnn.fromDBAnn : NameContext → LocalTypeDBAnn → LocalTypeR
    | _, .end => .end
    | ctx, .var n =>
        match SessionTypes.NameOnlyContext.get? ctx n with
        | some v => .var v
        | none => .var s!"free{n}"
    | ctx, .mu body =>
        let v := SessionTypes.NameOnlyContext.freshName ctx
        .mu v (LocalTypeDBAnn.fromDBAnn (SessionTypes.NameOnlyContext.cons v ctx) body)
    | ctx, .send p bs => .send p (LocalTypeDBAnn.branchesFromDBAnn ctx bs)
    | ctx, .recv p bs => .recv p (LocalTypeDBAnn.branchesFromDBAnn ctx bs)

  /-- Convert payload-preserving de Bruijn branch lists back to named local types. -/
  def LocalTypeDBAnn.branchesFromDBAnn :
      NameContext → List (Label × Option ValType × LocalTypeDBAnn) → List BranchR
    | _, [] => []
    | ctx, (lbl, vt, cont) :: rest =>
        (lbl, vt, LocalTypeDBAnn.fromDBAnn ctx cont) :: LocalTypeDBAnn.branchesFromDBAnn ctx rest
end

/-! ## Closedness Checks -/

mutual
  /-- Closedness at de Bruijn depth `k`. -/
  def LocalTypeDBAnn.isClosedAt : Nat → LocalTypeDBAnn → Bool
    | _, .end => true
    | k, .var n => n < k
    | k, .mu body => body.isClosedAt (k + 1)
    | k, .send _ bs => LocalTypeDBAnn.branchesClosedAt k bs
    | k, .recv _ bs => LocalTypeDBAnn.branchesClosedAt k bs

  /-- Closedness check for payload-preserving branches. -/
  def LocalTypeDBAnn.branchesClosedAt : Nat → List (Label × Option ValType × LocalTypeDBAnn) → Bool
    | _, [] => true
    | k, (_, _, cont) :: rest => cont.isClosedAt k && LocalTypeDBAnn.branchesClosedAt k rest
end

/-- Closedness at top-level depth. -/
def LocalTypeDBAnn.isClosed (t : LocalTypeDBAnn) : Bool :=
  t.isClosedAt 0

/-! ## Payload Erasure -/

mutual
  /-- Erase payload annotations from payload-preserving de Bruijn local types. -/
  def LocalTypeDBAnn.erasePayloads : LocalTypeDBAnn → LocalTypeDB
    | .end => .end
    | .var n => .var n
    | .mu body => .mu (LocalTypeDBAnn.erasePayloads body)
    | .send p bs => .send p (LocalTypeDBAnn.erasePayloadBranches bs)
    | .recv p bs => .recv p (LocalTypeDBAnn.erasePayloadBranches bs)

  /-- Erase payload annotations from payload-preserving branch lists. -/
  def LocalTypeDBAnn.erasePayloadBranches :
      List (Label × Option ValType × LocalTypeDBAnn) → List (Label × LocalTypeDB)
    | [] => []
    | (lbl, _vt, cont) :: rest =>
        (lbl, LocalTypeDBAnn.erasePayloads cont) :: LocalTypeDBAnn.erasePayloadBranches rest
end

end SessionTypes
