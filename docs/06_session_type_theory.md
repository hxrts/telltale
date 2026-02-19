# Session Type Theory

This document covers the formal session type theory implemented in the Lean verification libraries. It includes the coherence metatheory for asynchronous buffered MPST, representation theory for recursive session types, and projection theory for global-to-local transformations.

## Coherence Metatheory

The Protocol library provides a machine-checked metatheory for asynchronous buffered multiparty session types. The formalization covers preservation, progress, determinism, deadlock freedom, runtime monitoring, and deployment composition. The central technical device is the Coherence invariant, a per-edge consumption predicate that replaces binary duality. The contribution here is an operational formulation in which the exact invariant survives erasure to executable code.

### Coherence Invariant

Standard session type systems use duality to relate the two endpoints of a binary channel. Duality does not generalize to multiparty protocols with asynchronous communication and unbounded message buffers. The Coherence invariant addresses this by defining correctness per directed edge.

For each directed edge from sender to receiver, Coherence requires that consuming the in-flight message trace against the receiver's local type succeeds. The `Consume` function models this. It takes a receiver's local type and a sequence of buffered messages and returns the local type that remains after processing those messages.

```lean
def Consume (sender : Role) (L : LocalType) (trace : List Label) : Option LocalType
```

This function steps through the trace one label at a time. At each step it checks that the receiver's local type expects a receive from the sender with the matching label.

The `EdgeCoherent` predicate applies `Consume` to a single directed edge. The top-level `Coherent` predicate universally quantifies over all directed edges in all sessions. A configuration is coherent when every edge satisfies `EdgeCoherent`.

### Three-Way Edge Analysis

Coherence preservation proofs use a case split on any edge relative to the edge modified by a protocol step. The three cases are the edge being modified, an edge sharing an endpoint with the modified edge, and an unrelated edge. This technique generalizes the binary case where the split is between the active edge, its dual, and unrelated edges. In the multiparty setting, edges sharing an endpoint require more complex handling because they are not in a simple dual relationship.

### Preservation

The `Protocol/Preservation.lean` file contains the main safety theorems. These are unconditional properties of well-typed configurations.

```lean
theorem preservation_typed : WTConfigN cfg → Step cfg cfg' → WTConfigN cfg'

theorem progress_send : ...
theorem progress_recv : ...
theorem progress_select : ...
theorem progress_branch : ...
```

The `preservation_typed` theorem states that a well-typed configuration remains well-typed after any valid step. The `subject_reduction` theorem states that typing is preserved through reduction sequences. Each progress theorem states that a well-typed process with a matching local type can execute its next communication operation.

### Determinism and Session Isolation

The `Protocol/Determinism.lean` file establishes determinism properties. The `stepBase_det` theorem states that base reduction steps are deterministic. The `diamond_independent` theorem provides a diamond property for independent steps. The `session_isolation` theorem states that steps on different sessions commute.

### Deadlock Freedom

The `Protocol/DeadlockFreedom.lean` file establishes deadlock freedom under explicit assumptions. The result is conditional, not unconditional.

The `Guarded` predicate captures that a process has a reachable communication action. The `ReachesComm` predicate specifies reachability through a sequence of steps. The `deadlock_free` theorem states that a well-typed configuration satisfying guardedness and fairness assumptions does not get stuck on communication.

The fairness assumption states that the scheduler eventually delivers enqueued messages and schedules all active processes. These assumptions are stated explicitly as hypotheses, not hidden in the semantics.

### Deployment Composition

The deployment framework in `Protocol/Deployment/` supports compositional protocol verification. The `DeployedProtocol` structure bundles a protocol with its interface and proof of well-typedness. The `ProtocolBundle` structure groups deployed protocols for linking.

```lean
theorem link_preserves_WTMon : LinkOK dp1 dp2 → WTMon dp1 → WTMon dp2 → WTMon (link dp1 dp2)
theorem compose_deadlock_free : LinkOK dp1 dp2 → DeadlockFree dp1 → DeadlockFree dp2 →
    DeadlockFree (link dp1 dp2)
```

These theorems enable verifying protocols separately and composing the results. The `LinkOK` predicate captures interface compatibility conditions.

### Runtime Monitoring

The `Protocol/Monitor/` files define a runtime monitor that tracks protocol compliance. The `WTMon` judgment bundles coherence, head coherence, valid labels, buffer typing, linear context validity, and freshness into a single well-typedness predicate. Linear capability tokens enforce that each endpoint operation is authorized.

## Representation Theory

The SessionTypes and SessionCoTypes libraries establish a formal equivalence between two representations of recursive session types. The inductive representation uses explicit `mu` binders and de Bruijn variables. The coinductive representation uses infinite trees defined as polynomial functor M-types.

### Inductive Representation

The `LocalTypeR` type represents recursive local session types with named recursion variables.

```lean
inductive LocalTypeR where
  | send (role : Role) (label : Label) (cont : LocalTypeR)
  | recv (role : Role) (label : Label) (cont : LocalTypeR)
  | end
  | mu (body : LocalTypeR)
  | var (idx : Nat)
```

Substitution replaces the outermost bound variable with a given type. Well-formedness requires that all variables are bound by an enclosing `mu`. The de Bruijn representation in `SessionTypes/LocalTypeDB/` provides an alternative with clean substitution properties.

### Coinductive Representation

The `LocalTypeC` type represents session types as infinite trees. It is defined as an M-type of a polynomial functor with constructors for send, recv, and end. Recursive types unfold to their infinite expansion.

The equi-recursive equality `EQ2` captures when two coinductive types have the same observable behavior. Two types are `EQ2`-equal when they produce the same sequence of send and receive actions under all possible unfoldings.

### Roundtrip Theorem

The `toCoind` function converts an inductive type to its coinductive expansion. The `toInductive` function converts a regular coinductive type back to an inductive type with explicit `mu` binders.

```lean
theorem toCoind_toInductive_eq2ce (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf ...) (toCoind (toInductive t h)) t
```

The regularity hypothesis requires that the coinductive type has finitely many distinct subtrees. This is a standard condition for session types arising from finite protocol specifications.

### Decidable Bisimulation

The `BisimDecidable` module provides a decision procedure for coinductive type equality. The algorithm explores pairs of subtrees with a visited set. It terminates because regular types have finitely many reachable subtree pairs.

```lean
lemma reachablePairs_finite {a b : LocalTypeC} (ha : Regular a) (hb : Regular b) :
    Set.Finite (ReachablePairs a b)
```

The decision procedure operates directly on coinductive types without requiring conversion to inductive form first.

### Parametrized Coinduction

The EQ2 and bisimulation proofs use paco-lean for parametrized coinduction. Paco provides a monotone accumulation parameter that avoids the need for explicit guardedness arguments in coinductive proofs. This technique simplifies proofs that would otherwise require intricate guardedness reasoning.

## Projection Theory

The Choreography library formalizes the projection of global protocols to local session types. Three projection algorithms serve complementary roles. The Harmony theorem proves that projection commutes with operational semantics.

### Three Projection Algorithms

Standard formalizations define projection as a single partial function from global types to local types. This formalization decomposes projection into three algorithms that separate candidate generation, decidable checking, and certificate production.

The `trans` function is a total function from global types and roles to local types. It always produces output, even for non-projectable types. This algorithm serves as a candidate generator.

The `projectb` function checks whether a given local type is a valid projection of a global type for a given role. It returns a boolean. The soundness and completeness proofs connect this to the relational projection predicate.

```lean
theorem projectb_sound : projectb G r = true → CProject G r L
theorem projectb_complete : CProject G r L → projectb G r = true
```

The `projectR?` function returns `Option (LocalTypeR × CProject proof)`. When it succeeds, the result includes the local type and a machine-checked proof that it is the correct projection.

### Blindness

The blindness predicate provides a decidable sufficient condition for projectability. A global type is blind with respect to a role when the role cannot observe which branch was taken at any choice point where it is not a participant.

```lean
theorem projectable_of_wellFormedBlind :
    Closed G → WellFormed G → isBlind G r → ∃ L, CProject G r L
```

Blindness replaces the traditional approach where merge is undefined for incompatible branches. This makes projectability a decidable property.

### Erasure

The erasure relation replaces ad-hoc merge definitions with an algebraic structure for combining local types at non-participant branches. Send erasure requires identical label sets because a non-participant cannot choose which message to send based on a choice it did not observe. Receive erasure takes the union of label sets because a non-participant can receive any message regardless of which branch was taken.

This asymmetry between send and receive is critical for protocol safety. It captures the fundamental constraint that sending requires knowledge of the branch while receiving does not.

### Embedding

The embedding relation `CEmbed` provides a coinductive inverse of projection. Given a local type for a specific role, embedding reconstructs a global type that projects to it. The relation is intentionally partial because non-participant local types do not contain enough information to reconstruct the global protocol.

### Harmony

The Harmony theorem states that projection commutes with operational semantics. Stepping a global type and then projecting yields the same result as projecting and then stepping the local type.

The proof is structured across several files in `Choreography/Harmony/`. The `StepHarmony.lean` file contains the main proof structure. Supporting files handle communication cases, branching for participants, recursion, and non-participant cases.

A key supporting result is `trans_subst_comm`, which proves that projection commutes with substitution. The formal proof requires paco coinduction to handle the mu-unfolding cases.

## Summary

The session type theory spans approximately 34,000 lines across 130 files in the SessionTypes, SessionCoTypes, Choreography, and Protocol libraries. The representation theory provides the formal justification for using either inductive or coinductive types. The coherence metatheory establishes safety properties for async buffered MPST. The projection theory connects global specifications to local implementations. All results are axiom-free with no sorries.

## Related Docs

- [Background](00_introduction.md)
- [Choreographic Projection Patterns](05_projection.md)
- [Lean Verification](18_lean_verification.md)
