import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # Projection-Substitution Commutation

This module provides the projection-substitution commutation axiom, following the Coq
proof in `indProj.v` (lemma `proj_subst`).

## Main Result

```
trans (g.substitute t G) role = (trans g role).substitute t (trans G role)
```

This is the key lemma needed to eliminate the mu-unfold axioms in Harmony.lean.

## Status

The main theorem is axiomatized. The Coq proof uses induction on g with:
- `.end`, `.var` cases: trivial
- `.mu s body` case: requires guardedness analysis (the complex case)
- `.comm` case: recursive on branch continuations

The axiom is semantically sound - proven in Coq's `indProj.v:173`.

## References

- Coq: `proj_subst` in `Projection/indProj.v` (line 173)
-/

namespace RumpsteakV2.Protocol.Projection.ProjSubst

open RumpsteakV2.Protocol.GlobalType (GlobalType Label)
open RumpsteakV2.Protocol.LocalTypeR (LocalTypeR)
open RumpsteakV2.Protocol.CoTypes.EQ2 (EQ2 EQ2_refl)

-- Aliases to avoid name collision with _root_.trans
abbrev projTrans := RumpsteakV2.Protocol.Projection.Trans.trans
abbrev projTransBranches := RumpsteakV2.Protocol.Projection.Trans.transBranches

/-! ## Main Axiom: Projection-Substitution Commutation -/

/-- Projection commutes with global type substitution.

    Corresponds to Coq's `proj_subst`:
    ```
    trans p g[sigma] = (trans p g)[sigma >> trans p]
    ```

    Specialized to single-variable substitution:
    ```
    trans (g.substitute t G) role = (trans g role).substitute t (trans G role)
    ```

    This axiom is proven in Coq's `indProj.v` (line 173) by induction on g.
    The proof requires careful handling of the mu case with guardedness analysis.

    **PROVABLE**: This axiom can be eliminated by porting the Coq proof. -/
axiom proj_subst (g : GlobalType) (t : String) (G : GlobalType) (role : String) :
    projTrans (g.substitute t G) role = (projTrans g role).substitute t (projTrans G role)

/-! ## Corollaries -/

/-- proj_subst lifted to EQ2 (trivially, via equality). -/
theorem proj_subst_EQ2 (g : GlobalType) (t : String) (G : GlobalType) (role : String) :
    EQ2 (projTrans (g.substitute t G) role)
        ((projTrans g role).substitute t (projTrans G role)) := by
  rw [proj_subst]
  exact EQ2_refl _

/-- Specialized version: substituting mu into its body commutes with projection.

    This is the key case for the Harmony axioms:
    ```
    trans (body.substitute t (mu t body)) role = (trans body role).substitute t (mu t (trans body role))
    ```
    when (trans body role).isGuarded t = true. -/
theorem proj_subst_mu_self (t : String) (body : GlobalType) (role : String) :
    projTrans (body.substitute t (.mu t body)) role =
    (projTrans body role).substitute t (projTrans (.mu t body) role) :=
  proj_subst body t (.mu t body) role

/-- EQ2 version of mu-self substitution. -/
theorem proj_subst_mu_self_EQ2 (t : String) (body : GlobalType) (role : String) :
    EQ2 (projTrans (body.substitute t (.mu t body)) role)
        ((projTrans body role).substitute t (projTrans (.mu t body) role)) := by
  rw [proj_subst_mu_self]
  exact EQ2_refl _

/-! ## Guardedness Preservation

These lemmas establish that guardedness is preserved through substitution,
which is needed for the mu case of proj_subst. -/

/-- If body is guarded for v, and repl is guarded for v, then substitution preserves guardedness.

    **PROVABLE**: By induction on body. -/
axiom isGuarded_substitute_preserved (body : LocalTypeR) (t v : String) (repl : LocalTypeR)
    (hbody : body.isGuarded v = true) (hrepl : repl.isGuarded v = true) :
    (body.substitute t repl).isGuarded v = true

/-- If body is NOT guarded for v (v appears unguarded), and t ≠ v, then substitution
    for t doesn't change guardedness for v.

    **PROVABLE**: By induction on body. -/
axiom isGuarded_substitute_unguarded (body : LocalTypeR) (t v : String) (repl : LocalTypeR)
    (hbody : body.isGuarded v = false) (hneq : t ≠ v) :
    (body.substitute t repl).isGuarded v = false

end RumpsteakV2.Protocol.Projection.ProjSubst
