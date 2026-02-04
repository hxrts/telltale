# Session Type Representation Theory

The SessionTypes and SessionCoTypes libraries establish a formal equivalence between two representations of recursive session types. The inductive representation uses explicit `mu` binders and de Bruijn variables. The coinductive representation uses infinite trees defined as polynomial functor M-types. A machine-checked roundtrip theorem proves these representations are isomorphic up to bisimulation. A decidable bisimulation algorithm makes the coinductive representation computationally useful.

## Inductive Representation

The `LocalTypeR` type represents recursive local session types with named recursion variables. Constructors include `send`, `recv`, `end`, `mu`, and `var`. The `mu` constructor binds a recursion variable. The `var` constructor references a bound variable.

```lean
inductive LocalTypeR where
  | send (role : Role) (label : Label) (cont : LocalTypeR)
  | recv (role : Role) (label : Label) (cont : LocalTypeR)
  | end
  | mu (body : LocalTypeR)
  | var (idx : Nat)
```

Substitution replaces the outermost bound variable with a given type. Well-formedness requires that all variables are bound by an enclosing `mu`. These definitions and their properties are in `SessionTypes/LocalTypeR/`.

The de Bruijn representation in `SessionTypes/LocalTypeDB/` provides an alternative with clean substitution properties. The conversion between named and de Bruijn forms has a full roundtrip proof in `SessionTypes/LocalTypeConvProofs/`.

## Coinductive Representation

The `LocalTypeC` type represents session types as infinite trees. It is defined as an M-type of a polynomial functor with constructors for send, recv, and end. Recursive types unfold to their infinite expansion.

```lean
def LocalTypeC := SessionPF.M
```

The equi-recursive equality `EQ2` captures when two coinductive types have the same observable behavior. Two types are `EQ2`-equal when they produce the same sequence of send and receive actions under all possible unfoldings. The `EQ2` relation is defined coinductively using parametrized coinduction (paco-lean) to avoid manual guardedness arguments.

Observable behavior predicates classify types by their head constructor. A type is `ObsSend` if its outermost observable action is a send. A type is `ObsRecv` if its outermost observable action is a receive. A type is `ObsEnd` if it terminates.

## Roundtrip Theorem

The `toCoind` function converts an inductive type to its coinductive expansion. The `toInductive` function converts a regular coinductive type back to an inductive type with explicit `mu` binders. The roundtrip theorem states that composing these conversions yields a bisimilar type.

```lean
theorem toCoind_toInductive_eq2ce (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf ...) (toCoind (toInductive t h)) t
```

The proof uses `EQ2CE_coind` with an explicit bisimulation relation. The relation tracks visited nodes, closed sets, and environment substitutions. The proof handles back-edges from revisited nodes, mu-wrappers for cycles, and all constructor cases. It is approximately 500 lines of coinductive reasoning spread across the `SessionCoTypes/Coinductive/Roundtrip/` directory.

The regularity hypothesis requires that the coinductive type has finitely many distinct subtrees. This is a standard condition for session types arising from finite protocol specifications.

## Decidable Bisimulation

The `BisimDecidable` module provides a decision procedure for coinductive type equality. The algorithm explores pairs of subtrees with a visited set. It terminates because regular types have finitely many reachable subtree pairs.

```lean
lemma reachablePairs_finite {a b : LocalTypeC} (ha : Regular a) (hb : Regular b) :
    Set.Finite (ReachablePairs a b)
```

Each step of the algorithm either revisits a pair already in the visited set or adds a new pair. Since the set of reachable pairs is finite, the visited set reaches a fixed point. Soundness uses paco coinduction to extract a bisimulation from a successful run. Completeness uses the finite pair bound to show that bisimilar types are always accepted.

The decision procedure operates directly on coinductive types. It does not require conversion to inductive form first. This makes it usable as a standalone equality check for the coinductive representation.

## Parametrized Coinduction

The EQ2 and bisimulation proofs use paco-lean for parametrized coinduction. Paco provides a monotone accumulation parameter that avoids the need for explicit guardedness arguments in coinductive proofs. The `CoinductiveRel.lean` and `CoinductiveRelPaco.lean` files define the interface. The `EQ2Paco.lean` file instantiates paco for equi-recursive equality.

This technique simplifies proofs that would otherwise require intricate guardedness reasoning. Transitivity and substitution lemmas for `EQ2` are substantially shorter when using paco than with direct coinduction.

## De Bruijn Conversions

The `SessionTypes/LocalTypeDB/` module provides a de Bruijn indexed representation with clean substitution. The conversion between named recursive types and de Bruijn types is defined in `LocalTypeConv.lean`. Three proof files establish the roundtrip.

`Helpers.lean` proves soundness of the named-to-de-Bruijn direction. `ClosedRoundtrip.lean` proves completeness for closed types. `Roundtrip.lean` proves substitution equivalence under conversion. Together these ensure that the two syntactic representations are interchangeable without loss of information.

## Summary

The representation theory layer sits beneath the session type metatheory. It provides the formal justification for using either inductive or coinductive types in proofs and implementations. The roundtrip theorem and decidable bisimulation together span approximately 14,000 lines across 63 files with no axioms and no sorries. See [Lean Verification](19_lean_verification.md) for the complete file listing.
