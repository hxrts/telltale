# Coherence Metatheory

The Protocol library provides a machine-checked metatheory for asynchronous buffered multiparty session types. The formalization covers preservation, progress, determinism, deadlock freedom, runtime monitoring, and deployment composition. The central technical device is the Coherence invariant, which replaces binary duality with a per-edge consumption predicate.

## Coherence Invariant

Standard session type systems use duality to relate the two endpoints of a binary channel. Duality does not generalize to multiparty protocols with asynchronous communication and unbounded message buffers. The Coherence invariant addresses this by defining correctness per directed edge.

For each directed edge from sender to receiver, Coherence requires that consuming the in-flight message trace against the receiver's local type succeeds. The `Consume` function models this. It takes a receiver's local type and a sequence of buffered messages and returns the local type that remains after processing those messages.

```lean
def Consume (sender : Role) (L : LocalType) (trace : List Label) : Option LocalType
```

This function steps through the trace one label at a time. At each step it checks that the receiver's local type expects a receive from the sender with the matching label.

The `EdgeCoherent` predicate applies `Consume` to a single directed edge. The top-level `Coherent` predicate universally quantifies over all directed edges in all sessions. A configuration is coherent when every edge satisfies `EdgeCoherent`.

The composition property of `Consume` is central to the preservation proofs. Consuming a concatenated trace equals consuming the first segment and then consuming the second segment against the resulting type. This property enables modular reasoning about individual protocol steps.

## Three-Way Edge Analysis

Coherence preservation proofs use a case split on any edge relative to the edge modified by a protocol step. The three cases are:

1. The edge is the one being modified. The proof shows that the step updates the type and trace consistently.
2. The edge shares an endpoint with the modified edge but is not the same. The proof handles the indirect effect on related edges.
3. The edge is unrelated to the modified edge. Preservation is immediate.

This technique generalizes the binary case, where the split is between the active edge, its dual, and unrelated edges. In the multiparty setting, case 2 is more complex because edges sharing an endpoint are not in a simple dual relationship.

## Preservation

The `Protocol/Preservation.lean` file contains the main safety theorems. These are unconditional properties of well-typed configurations.

The `preservation_typed` theorem states that a well-typed configuration remains well-typed after any valid step. The `subject_reduction` theorem states that typing is preserved through reduction sequences. The progress theorems cover all four communication primitives.

```lean
theorem preservation_typed : WTConfigN cfg → Step cfg cfg' → WTConfigN cfg'

theorem progress_send : ...
theorem progress_recv : ...
theorem progress_select : ...
theorem progress_branch : ...
```

Each progress theorem states that a well-typed process with a matching local type can execute its next communication operation. These theorems hold unconditionally for single-protocol configurations.

The typing infrastructure includes `HasTypeProcN` for process typing and `WTConfigN` for configuration typing. The frame lemmas in `Typing/Framing.lean` handle environment splitting for parallel composition. The compatibility lemmas in `Typing/Compatibility.lean` manage session environment operations.

## Determinism and Session Isolation

The `Protocol/Determinism.lean` file establishes determinism properties. The `stepBase_det` theorem states that base reduction steps are deterministic. The `diamond_independent` theorem provides a diamond property for independent steps. The `session_isolation` theorem states that steps on different sessions commute.

These properties ensure that protocol execution is predictable. Two independent steps can be reordered without changing the result.

## Deadlock Freedom

The `Protocol/DeadlockFreedom.lean` file establishes deadlock freedom under explicit assumptions. The result is conditional, not unconditional.

The `Guarded` predicate captures that a process has a reachable communication action. The `ReachesComm` predicate specifies reachability through a sequence of steps. The `deadlock_free` theorem states that a well-typed configuration satisfying guardedness and fairness assumptions does not get stuck on communication. The `not_stuck` theorem provides the corresponding local property.

The fairness assumption states that the scheduler eventually delivers enqueued messages and schedules all active processes. These assumptions are stated explicitly as hypotheses, not hidden in the semantics.

## Deployment Composition

The deployment framework in `Protocol/Deployment/` supports compositional protocol verification. The `InterfaceType` structure defines the boundary type of a deployed protocol. The `DeployedProtocol` structure bundles a protocol with its interface and proof of well-typedness. The `ProtocolBundle` structure groups deployed protocols for linking.

The `MergeDEnv` operation combines deployment environments from two protocols with disjoint session sets. The linking theorems in `Deployment/Linking.lean` establish that composition preserves well-typedness and deadlock freedom.

```lean
theorem link_preserves_WTMon : LinkOK dp1 dp2 → WTMon dp1 → WTMon dp2 → WTMon (link dp1 dp2)
theorem compose_deadlock_free : LinkOK dp1 dp2 → DeadlockFree dp1 → DeadlockFree dp2 →
    DeadlockFree (link dp1 dp2)
```

These theorems enable verifying protocols separately and composing the results. The `LinkOK` predicate captures interface compatibility conditions.

## Runtime Monitoring

The `Protocol/Monitor/` files define a runtime monitor that tracks protocol compliance. The `WTMon` judgment bundles coherence, head coherence, valid labels, buffer typing, linear context validity, and freshness into a single well-typedness predicate.

The `MonStep` inductive type defines valid monitor transitions for send, receive, select, and branch operations. The `MonStep_preserves_WTMon` theorem states that valid monitor steps preserve well-typedness.

Linear capability tokens enforce that each endpoint operation is authorized. Tokens are consumed and produced as the protocol advances. The `lin_valid` condition ensures token-type consistency. The `lin_unique` condition prevents duplicate endpoints.

## Relationship to Prior Work

The standard references for multiparty session type metatheory are Coppo, Dezani-Ciancaglini, Yoshida, and Padovani (2016) and Scalas and Yoshida (2019). These works establish preservation and progress for synchronous and asynchronous multiparty session types on paper.

The Coherence invariant differs from these works in two ways. It replaces the traditional duality-based approach with a consumption-based per-edge predicate. It also handles unbounded asynchronous buffers directly, without encoding them into synchronous communication.

The formalization is approximately 18,500 lines of Lean 4 across 41 files. The core single-protocol metatheory contains no sorry-free gaps. See [Lean Verification](19_lean_verification.md) for the complete module map and axiom inventory.
