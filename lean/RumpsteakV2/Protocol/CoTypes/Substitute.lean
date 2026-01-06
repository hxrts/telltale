import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.Bisim
import RumpsteakV2.Protocol.LocalTypeR

/-! # EQ2_substitute: Substitution Preserves Equi-recursive Equality

This module establishes that EQ2 (the coinductive equi-recursive equality) is
preserved under substitution. This is a key lemma for the typing and subject
reduction proofs.

## Expose

The following definitions form the semantic interface for proofs:

- `EQ2_substitute`: substitution preserves EQ2
- `unfold_substitute_EQ2`: unfold/substitute confluence (substitute then unfold ≈ unfold then substitute)
- `Fresh`: freshness predicate (variable not free in type)
- `isFreeIn`: check if variable appears free in type

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

**Proven version:** See `EQ2_substitute_barendregt` in `SubstCommBarendregt.lean` which
proves this under explicit Barendregt preconditions:
- `notBoundAt var a` and `notBoundAt var b` (no shadowing of var)
- `∀ t, isFreeIn t repl = false` (repl is closed, so no capture)

The unconditional axiom here is semantically sound because well-formed types
satisfy the Barendregt convention. The proof has 2 remaining sorries for
double-unfold edge cases that require more sophisticated coinductive reasoning.

**Coq reference:** `subst_EQ2` in `subject_reduction/EQ2.v`

**Status:** PROVEN via Bisim approach (see `EQ2_substitute_via_Bisim` in Bisim.lean).
-/
theorem EQ2_substitute (a b : LocalTypeR) (var : String) (repl : LocalTypeR) :
    EQ2 a b → EQ2 (a.substitute var repl) (b.substitute var repl) :=
  RumpsteakV2.Protocol.CoTypes.Bisim.EQ2_substitute_via_Bisim

/-! ## Derived Lemmas -/

/-- Substitution preserves EQ2 with any replacement term. -/
theorem EQ2_substitute' {a b : LocalTypeR} (var : String) (repl : LocalTypeR)
    (h : EQ2 a b) : EQ2 (a.substitute var repl) (b.substitute var repl) :=
  EQ2_substitute a b var repl h

/-- If two types are EQ2-equal, substituting in one gives an EQ2-equal result. -/
theorem EQ2_substitute_left (a : LocalTypeR) (var : String) (repl : LocalTypeR) :
    EQ2 (a.substitute var repl) (a.substitute var repl) :=
  EQ2_substitute a a var repl (EQ2_refl a)

/-! ## Unfold-Substitute Confluence

The second key axiom for substitution: unfolding and substitution are confluent
operations on equi-recursive types.

## Theorem Statement

`unfold_substitute_EQ2`: For any type `t`, variable `var`, and replacement `repl`:
  `EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl)`

This says that substitute-then-unfold produces an EQ2-equivalent result to
unfold-then-substitute.

## Proof Strategy

The proof proceeds by case analysis on `t`:

### Non-mu cases (end, var, send, recv)

For these constructors, `unfold` is the identity function:
- `t.unfold = t`
- `(t.substitute var repl).unfold = t.substitute var repl`
- `(t.unfold).substitute var repl = t.substitute var repl`

Both sides are definitionally equal, so `EQ2_refl` suffices.

### Mu case (mu s body)

This is where the interesting confluence happens. Let `M = mu s body`:

- **LHS**: `(M.substitute var repl).unfold`
  - If `s == var`: `M.unfold = body.substitute s M`
  - If `s ≠ var`: `(mu s (body.substitute var repl)).unfold`
              `= (body.substitute var repl).substitute s (mu s (body.substitute var repl))`

- **RHS**: `(M.unfold).substitute var repl`
  - `M.unfold = body.substitute s M`
  - `(body.substitute s M).substitute var repl`

The two sides differ in the ORDER of substitutions:
- LHS: substitute `var`, then unfold (which substitutes `s` with the modified mu)
- RHS: unfold (substitute `s` with original mu), then substitute `var`

The key insight is that these produce the same INFINITE TREE. The difference is
only in how the finite recursive syntax is represented. When fully unfolded to
infinite depth, both give identical communication structures.

## Circular Dependency with EQ2_substitute

This axiom and `EQ2_substitute` are mutually dependent:
- `EQ2_substitute` proof needs `unfold_substitute_EQ2` for the mu case
- `unfold_substitute_EQ2` proof needs `EQ2_substitute` for recursive reasoning

Both can be proven simultaneously using a combined coinductive relation, but
the proof is complex. We accept both as axioms since:
1. They are semantically sound (infinite tree semantics)
2. They correspond to proven lemmas in Coq (`subst_EQ2`, `full_eunf_subst`)
3. The Barendregt convention ensures well-formedness

## Connection to Coq's `full_eunf_subst`

This corresponds to the single-step version of `full_eunf_subst` (coLocal.v:56):
  `full_eunf (μt.body) = full_eunf (body[t := μt.body])`

Where `full_eunf` completely unfolds all mu binders. Our axiom is weaker
(single step vs full unfolding) but sufficient when combined with coinduction.

-/

/-- Unfold and substitute are confluent operations on local types.

This axiom states that applying substitute then unfold is EQ2-equivalent to
applying unfold then substitute. Both produce observationally equivalent
infinite communication trees.

**Proof sketch:**
1. Non-mu cases: unfold is identity, trivial by `EQ2_refl`
2. Mu case: requires showing confluence of substitution order
3. Use coinduction on the infinite tree to show semantic equivalence

**Coq reference:** `full_eunf_subst` in `subject_reduction/coLocal.v`

**Status:** PROVEN via Bisim approach (see `unfold_substitute_EQ2_via_Bisim` in Bisim.lean).
-/
theorem unfold_substitute_EQ2 (t : LocalTypeR) (var : String) (repl : LocalTypeR) :
    EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl) :=
  RumpsteakV2.Protocol.CoTypes.Bisim.unfold_substitute_EQ2_via_Bisim t var repl

/-- Unfold-substitute confluence for the reflexive case. -/
theorem unfold_substitute_EQ2_refl (t : LocalTypeR) (var : String) (repl : LocalTypeR) :
    EQ2 ((t.substitute var repl).unfold) ((t.substitute var repl).unfold) :=
  EQ2_refl _

end RumpsteakV2.Protocol.CoTypes.Substitute
