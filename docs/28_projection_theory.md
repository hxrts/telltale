# Projection Theory

The Choreography library formalizes the projection of global protocols to local session types. Three projection algorithms serve complementary roles. The Harmony theorem proves that projection commutes with operational semantics. Supporting predicates for blindness, erasure, and embedding decompose projectability into decidable components. The entire library contains no axioms and no sorries.

## Three Projection Algorithms

Standard formalizations define projection as a single partial function from global types to local types. This formalization decomposes projection into three algorithms that separate candidate generation, decidable checking, and certificate production.

### Trans Projection

The `trans` function is a total function from global types and roles to local types. It always produces output, even for non-projectable types. For projectable inputs the output is the correct local type. For non-projectable inputs the output may not correspond to a valid projection.

This algorithm follows the Coq-style approach to projection. It serves as a candidate generator. The `Projection/Trans/Core.lean` file defines the core algorithm. The `Participation.lean` file handles participant filtering. The `Contractive.lean` file provides guardedness analysis for recursive projection.

### Boolean Checker

The `projectb` function checks whether a given local type is a valid projection of a global type for a given role. It returns a boolean. The soundness proof shows that `projectb` returning true implies the relational projection predicate holds. The completeness proof shows the converse.

```lean
theorem projectb_sound : projectb G r = true → CProject G r L
theorem projectb_complete : CProject G r L → projectb G r = true
```

These theorems are in `Projection/Projectb/Soundness.lean` and `Completeness.lean`. The checker handles branch merging for non-participants and mu-type unfolding. The coinductive cases are in `Projection/Projectb/Coinductive.lean`.

### Proof-Carrying Projection

The `projectR?` function returns `Option (LocalTypeR × CProject proof)`. When it succeeds, the result includes the local type and a machine-checked proof that it is the correct projection. When it fails, the global type is not projectable for the given role.

```lean
def projectR? (G : GlobalType) (r : Role) : Option { L : LocalTypeR // CProject G r L }
```

This API enables verified projection in compiled code. The caller receives both the result and its correctness certificate. The implementation is in `Projection/Project/` across 20 files covering base cases, mu-unfolding elimination, constructor cases, completeness, observable preservation, and head preservation.

## Blindness

The blindness predicate provides a decidable sufficient condition for projectability. A global type is blind with respect to a role when the role cannot observe which branch was taken at any choice point where it is not a participant.

```lean
theorem projectable_of_wellFormedBlind :
    Closed G → WellFormed G → isBlind G r → ∃ L, CProject G r L
```

This theorem states that a closed, well-formed, blind global type is projectable for the given role. The proof is in `Projection/Blind/Core.lean` and `Preservation.lean`.

Blindness replaces the traditional approach where merge is undefined for incompatible branches. Instead of failing with an error, the formalization provides a syntactic check that succeeds exactly when projection is defined. This makes projectability a decidable property.

## Erasure

The erasure relation replaces ad-hoc merge definitions with an algebraic structure for combining local types at non-participant branches. In standard formulations, two branches are mergeable when a partial merge function happens to succeed, but there is no independent characterization of when this holds. The `Erases` relation provides that characterization. It defines the exact conditions under which a common lower bound exists for two local types, making mergeability a structurally transparent property rather than an artifact of a particular algorithm.

Send erasure requires identical label sets. A non-participant cannot choose which message to send based on a choice it did not observe. Receive erasure takes the union of label sets. A non-participant can receive any message regardless of which branch was taken.

This asymmetry between send and receive is critical for protocol safety. It captures the fundamental constraint that sending requires knowledge of the branch while receiving does not. The definition is in `Projection/Erasure/Core.lean`. Soundness is in `Projection/Erasure/MergeSoundness.lean`.

## Embedding

The embedding relation `CEmbed` provides a coinductive inverse of projection. Given a local type for a specific role, embedding reconstructs a global type that projects to it. The relation is intentionally partial. It is defined only for participants, since non-participant local types do not contain enough information to reconstruct the global protocol.

The embedding properties in `Projection/EmbedProps.lean` establish that embedding composes correctly with projection. For a participant, embedding the projected local type and then projecting again recovers the original local type up to `EQ2`.

## Harmony

The Harmony theorem is the central correctness result for projection. It states that projection commutes with operational semantics. Stepping a global type and then projecting yields the same result as projecting and then stepping the local type.

The proof is structured across several files in `Choreography/Harmony/`.

`StepHarmony.lean` contains the main proof structure. It dispatches to helper lemmas based on the step type. `Substitution.lean` handles communication cases where a send-receive pair reduces. `ParticipantSteps.lean` handles branching cases for participants. `NonParticipantHelpers.lean` and `NonParticipantSteps.lean` handle recursion and non-participant cases.

A key supporting result is `trans_subst_comm`, which proves that projection commutes with substitution. Paper treatments of recursive projection typically leave this commutativity implicit. The formal proof requires paco coinduction to handle the mu-unfolding cases. The `MuUnfoldLemmas.lean` and `SubstEndUnguarded.lean` files provide the supporting lemmas for unfolding and guardedness.

The Harmony proof connects the global stepping semantics in `SessionTypes/GlobalType/WellFormedLemmas.lean` to the environment stepping semantics in `Semantics/EnvStep.lean`. This establishes that the projection pipeline correctly transforms global protocol behavior into local endpoint behavior.

## Summary

The projection theory spans 69 files and approximately 16,250 lines. It provides three projection algorithms (candidate generation, boolean checking, proof-carrying), three supporting predicates (blindness, erasure, embedding), and a complete Harmony proof. All results are axiom-free. See [Lean Verification](19_lean_verification.md) for the module listing and [Choreographic Projection Patterns](05_projection.md) for the Rust implementation.
