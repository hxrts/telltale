import SessionCoTypes.Bisim.Substitution.Core

/-! # SessionCoTypes.Bisim.Substitution.EQ2Bridge

Bridge lemma from Barendregt substitution compatibility to EQ2.
-/

/-
The Problem. Most users consume EQ2-level substitution preservation, not the
intermediate Bisim-compatible statement.

Solution Structure. Re-export the final EQ2 bridge theorem in a compact module
that depends on the core Barendregt development.
-/

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace SessionCoTypes.Bisim
open SessionTypes.LocalTypeR
open SessionTypes.GlobalType
open SessionCoTypes.Observable
open SessionCoTypes.EQ2
open SessionCoTypes.CoinductiveRel

open SessionCoTypes.SubstCommBarendregt in
/-- EQ2 is preserved by substitution (Barendregt version).

    This version is proven via the Barendregt commutation proof in
    `SubstCommBarendregt.lean` and removes the DB bridge assumption. -/
theorem EQ2_substitute_via_Bisim {a b : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : EQ2 a b)
    (hbarA : notBoundAt var a = true)
    (hbarB : notBoundAt var b = true)
    (hfresh : ∀ t, isFreeIn t repl = false)
    (hnomu : ∀ t body, repl ≠ .mu t body) :
    EQ2 (a.substitute var repl) (b.substitute var repl) := by
  exact EQ2_substitute_barendregt a b var repl h hbarA hbarB hfresh hnomu

end SessionCoTypes.Bisim
