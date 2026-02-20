import SessionTypes.LocalTypeConvProofs.Roundtrip.Contractive

/-! # SessionTypes.LocalTypeConvProofs.Roundtrip.Substitution

Named-side substitution invariance for DB conversion.
-/

/-
The Problem. A final bridge lemma is needed to show non-free substitutions do
not affect DB conversion output.

Solution Structure. Proves the substitution roundtrip corollary from the prior
conversion and not-free substitution lemmas.
-/

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SessionTypes.LocalTypeConvProofs
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.LocalTypeDB
open SessionTypes.LocalTypeConv
open SessionTypes.NameOnlyContext

/-! ## Substitution (Named → DB) -/

/-! ## Substitution (Named → DB) -/

/-- If a variable is not free, named substitution is a no-op and conversion is unchanged. -/
theorem toDB?_substitute_not_free
    (t repl : LocalTypeR) (ctx : Context) (x : String) (db : LocalTypeDB)
    (hdb : t.toDB? ctx = some db)
    (hfree : LocalTypeR.isFreeIn x t = false) :
    (t.substitute x repl).toDB? ctx = some db := by
  have hsub : t.substitute x repl = t :=
    LocalTypeR.substitute_not_free t x repl hfree
  simpa [hsub] using hdb

end SessionTypes.LocalTypeConvProofs
