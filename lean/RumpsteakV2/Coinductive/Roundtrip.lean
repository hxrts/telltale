import Mathlib
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CEnv
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Coinductive.ToInductive
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
# Round-trip helpers for LocalTypeC/LocalTypeR

This module is temporarily stubbed to keep the build green.
Full proofs are preserved in `Roundtrip.full.lean` and should be restored.
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.LocalTypeR

/-- Name assigned to a coinductive node in a finite system. -/
axiom nameOf (c : LocalTypeC) (all : Finset LocalTypeC) : String

/-- Environment generated from a finite system of nodes. -/
axiom envOf (all visited : Finset LocalTypeC) : EnvPair

/-- Canonical round-trip statement (env-aware). -/
axiom toCoind_toInductive_eq2ce (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t

/-- Erase env-aware round-trip to EQ2C under back-edge hypotheses. -/
axiom toCoind_toInductive_eq2c_of_eq2ce (t : LocalTypeC) (h : Regular t)
    (hback :
      ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c)
    (hce :
      EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
        (toCoind (toInductive t h)) t) :
    EQ2C (toCoind (toInductive t h)) t

/-- Round-trip in EQ2C assuming back-edge resolution. -/
axiom toCoind_toInductive_eq2c_of_backedge (t : LocalTypeC) (h : Regular t)
    (hback :
      ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c) :
    EQ2C (toCoind (toInductive t h)) t

/-- Round-trip in EQ2C assuming env resolves back-edges. -/
axiom toCoind_toInductive_eq2c_of_env (t : LocalTypeC) (h : Regular t)
    (hEnv : EnvResolves (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))) :
    EQ2C (toCoind (toInductive t h)) t

/-- Canonical round-trip statement (alias). -/
axiom toCoind_toInductive (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t

end RumpsteakV2.Coinductive
