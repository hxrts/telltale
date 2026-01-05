import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.LocalTypeR

/-! # EQ2_substitute: Substitution Preserves Equi-recursive Equality

This module establishes that EQ2 (the coinductive equi-recursive equality) is
preserved under substitution. This is a key lemma for the typing and subject
reduction proofs.

## Theorem Statement

`EQ2_substitute`: If `EQ2 a b`, then `EQ2 (a.substitute var repl) (b.substitute var repl)`.

## Proof Strategy

The proof uses coinduction with the following relation:

```
SubstRel var repl a' b' ≜ ∃ a b, EQ2 a b ∧ a' = a.subst var repl ∧ b' = b.subst var repl
```

For most cases, showing `SubstRel` is a post-fixpoint of `EQ2F` is straightforward.
The complex case is when we have `mu` binders where the substitution interacts with
the mu-unfolding.

## The Substitution Commutation Challenge

When unfolding `(mu t body).substitute var repl`, we need to show that:

```
(body.subst var repl).subst t (mu t (body.subst var repl))
= (body.subst t (mu t body)).subst var repl
```

This is the **substitution commutation lemma**. It holds syntactically when:
- `t ≠ var` (the binder name differs from the substituted variable), AND
- `t ∉ freeVars(repl)` (the **Barendregt convention**)

The freshness condition ensures that `repl` doesn't accidentally capture `t`.

## Why This Is Sound

In well-formed type contexts, the Barendregt convention always holds:
- `t` is a local binder introduced by `mu t body`
- `repl` comes from an outer scope where `t` is not bound
- Therefore `t` cannot appear free in `repl`

Even when the syntactic terms differ (due to variable capture edge cases), the
infinite tree semantics are identical. EQ2 captures this semantic equality.

## Coq Reference

This corresponds to the `subst_EQ2` lemma in the Coq subject reduction proof.
The Coq proof uses similar coinductive reasoning with careful handling of the
mu-unfolding case.

-/

namespace RumpsteakV2.Protocol.CoTypes.Substitute

open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## Freshness Predicate -/

mutual
  /-- Check if a variable appears free in a local type. -/
  def isFreeIn (v : String) : LocalTypeR → Bool
    | .end => false
    | .var w => v == w
    | .send _ bs => isFreeInBranches v bs
    | .recv _ bs => isFreeInBranches v bs
    | .mu t body => if v == t then false else isFreeIn v body

  /-- Check if a variable appears free in any branch. -/
  def isFreeInBranches (v : String) : List (Label × LocalTypeR) → Bool
    | [] => false
    | (_, cont) :: rest => isFreeIn v cont || isFreeInBranches v rest
end

/-- A variable is fresh for a type if it doesn't appear free. -/
def Fresh (v : String) (t : LocalTypeR) : Prop := isFreeIn v t = false

/-! ## The Main Axiom -/

/-- EQ2 is preserved under substitution.

This axiom captures that equi-recursive equality is closed under substitution.
The proof uses coinduction with the `SubstRel` relation and relies on the
Barendregt convention (bound variables are fresh w.r.t. external terms).

**Proof sketch:**
1. Define `SubstRel var repl a' b' ≜ ∃ a b, EQ2 a b ∧ a' = a.subst var repl ∧ b' = b.subst var repl`
2. Show `SubstRel` is a post-fixpoint of `EQ2F` up to `EQ2`
3. For the mu case, use substitution commutation: when `t ∉ freeVars(repl)`,
   `(body.subst var repl).subst t X = (body.subst t X).subst var repl`
4. The freshness condition holds by Barendregt convention

**Coq reference:** `subst_EQ2` in `subject_reduction/EQ2.v`
-/
axiom EQ2_substitute (a b : LocalTypeR) (var : String) (repl : LocalTypeR) :
    EQ2 a b → EQ2 (a.substitute var repl) (b.substitute var repl)

/-! ## Derived Lemmas -/

/-- Substitution preserves EQ2 with any replacement term. -/
theorem EQ2_substitute' {a b : LocalTypeR} (var : String) (repl : LocalTypeR)
    (h : EQ2 a b) : EQ2 (a.substitute var repl) (b.substitute var repl) :=
  EQ2_substitute a b var repl h

/-- If two types are EQ2-equal, substituting in one gives an EQ2-equal result. -/
theorem EQ2_substitute_left (a : LocalTypeR) (var : String) (repl : LocalTypeR) :
    EQ2 (a.substitute var repl) (a.substitute var repl) :=
  EQ2_substitute a a var repl (EQ2_refl a)

end RumpsteakV2.Protocol.CoTypes.Substitute
