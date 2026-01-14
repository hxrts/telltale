import Mathlib
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CEnv
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Coinductive.ToInductive
import RumpsteakV2.Coinductive.ToCoindInjectivity
import RumpsteakV2.Coinductive.RoundtripHelpers
import RumpsteakV2.Coinductive.BisimHelpers
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-
The Problem. The key correctness property for the inductive-coinductive bridge
is that round-tripping preserves equivalence: toCoind(toInductive(t)) ≅ t.
This ensures we can convert freely between representations without losing
semantic meaning.

The difficulty is that toInductive introduces fresh mu-binders and variable
names that don't exist in the original coinductive type. We need to prove
that these are equivalent under EQ2C (equi-recursive type equality).

Module Organization.
- ToCoindInjectivity.lean: injectivity of toCoind (complete)
- RoundtripHelpers.lean: structural helper lemmas (complete)
- BisimHelpers.lean: bisimulation construction lemmas (complete)
- RoundtripWIP.lean: incomplete round-trip theorems with sorry (work in progress)

This file provides the public API, re-exporting completed theorems and
providing axioms for incomplete ones.

Solution Structure.
1. toCoind_injective: distinct inductive types map to distinct coinductive types
2. VisitedLt: invariant for recursive descent in toInductiveAux
3. nameOf: compute the canonical name for a node (WIP)
4. envOf: build environment mapping names to their definitions (WIP)
5. toCoind_toInductive_eq2ce: round-trip holds under environment (WIP)
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.LocalTypeR

/-! ## Re-exports from ToCoindInjectivity -/

-- toCoind_injective is available from ToCoindInjectivity
-- toCoindBranches_injective is available from ToCoindInjectivity
-- toCoindBranches_length, toCoindBranches_get are available from ToCoindInjectivity

/-! ## Re-exports from RoundtripHelpers -/

-- childRel_toCoind, childRel_toCoind_size are available from RoundtripHelpers
-- VisitedLt, visitedLt_not_mem, visitedLt_insert are available from RoundtripHelpers
-- childRel_toCoind_mu, childRel_toCoind_send, childRel_toCoind_recv are available

/-! ## Re-exports from BisimHelpers -/

-- EQ2C_end_head, EQ2C_var_head, EQ2C_send_head, EQ2C_recv_head are available from BisimHelpers
-- EQ2CE_step_to_EQ2C is available from BisimHelpers

/-! ## Stub Definitions (Work in Progress)

These definitions and theorems are incomplete. Full proofs are being developed
in RoundtripWIP.lean. The axioms below serve as placeholders for the public API.
-/

/-- Name assigned to a coinductive node in a finite system. -/
axiom nameOf (c : LocalTypeC) (all : Finset LocalTypeC) : String

/-- Environment generated from a finite system of nodes. -/
axiom envOf (all visited : Finset LocalTypeC) : EnvPair

/-! ## Round-Trip Theorems (Axioms - proofs in progress) -/

/-- Canonical round-trip: toCoind(toInductive(t)) is EQ2CE-equivalent to t. -/
axiom toCoind_toInductive_eq2ce (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t

/-- Erase environment awareness given back-edge resolution. -/
axiom toCoind_toInductive_eq2c_of_eq2ce (t : LocalTypeC) (h : Regular t)
    (hback : ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c)
    (hce : EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
             (toCoind (toInductive t h)) t) :
    EQ2C (toCoind (toInductive t h)) t

/-- Round-trip in EQ2C assuming back-edge resolution. -/
axiom toCoind_toInductive_eq2c_of_backedge (t : LocalTypeC) (h : Regular t)
    (hback : ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c) :
    EQ2C (toCoind (toInductive t h)) t

/-- Round-trip in EQ2C assuming environment resolves back-edges. -/
axiom toCoind_toInductive_eq2c_of_env (t : LocalTypeC) (h : Regular t)
    (hEnv : EnvResolves (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))) :
    EQ2C (toCoind (toInductive t h)) t

/-- Canonical round-trip statement (alias). -/
axiom toCoind_toInductive (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t

end RumpsteakV2.Coinductive
