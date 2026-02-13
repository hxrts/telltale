# Coherence for Asynchronous Buffered MPST: A Mechanized Metatheory

## Abstract

We recast preservation for asynchronous buffered multiparty session types from global re-derivation to `Coherence`, an active-edge local invariant of receiver-buffer compatibility.

We prove two central results. The first gives a reusable preservation architecture based on a three-way edge split. The second result proves session evolution under asynchronous subtype replacement through `Consume_mono`.

The metatheory is parametric in delivery semantics through `DeliveryModel`, with FIFO, causal, and lossy instances. The core claims are mechanized in Lean 4. A supporting artifact bridges choreography obligations to VM obligations through typed effect handlers.

## 1. Introduction

Asynchronous buffered MPST proofs are typically organized around repeated global re-derivation after each transition (Honda et al., 2008, and Tirore, Bengtson, and Carbone, 2025). That structure is costly and brittle when step relations grow.

This paper replaces that structure with active-edge local reasoning. The local invariant is `Coherence`, and preservation is proved by composing edge-local obligations in a style compatible with local proof decomposition used in program logics (Hinrichsen et al., 2020).

The local-to-global shape follows a standard invariant method. Local obligations are proved on small footprints and then lifted to global safety by composition. What is new here is the active-edge specialization for asynchronous buffered MPST, where the lift is carried by one explicit three-way edge split and one reusable `Consume` alignment kernel.

An information-theoretic reading is also useful. Projection and monitoring act as observation channels from executions to externally visible traces (Shannon, 1948). This paper establishes the zero-loss baseline for that channel at the Coherence layer, so later envelope results can add controlled distortion contracts (Cover and Thomas, 2006).

The paper has two central claims. Claim one is Coherence preservation through a reusable proof skeleton. Claim two is session evolution through subtype replacement via `Consume_mono`.

The three-paper dependency is direct. This paper defines the invariant kernel, *Computable Dynamics for Asynchronous MPST* builds quantitative and decision procedures on that kernel, and *Harmony from Coherence in Asynchronous MPST* adds reconfiguration commutation and envelope exactness.

Scope is restricted to asynchronous buffered semantics, active-edge quantification, classical payloads, and `DeliveryModel` parameterization. Quantitative fairness-dependent bounds are deferred to *Computable Dynamics for Asynchronous MPST*. Reconfiguration and envelope claims are deferred to *Harmony from Coherence in Asynchronous MPST*. Byzantine safety in this paper series is tracked through shared notation $H_{\mathrm{byz}}$, $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, and $\mathcal E_{\mathrm{byz}}$. Figure 1 shows the proof architecture shift.

Our contributions are as follows:

1. A local preservation architecture based on active-edge `Coherence` and a reusable three-way edge split.
2. A message-alignment proof kernel through `Consume` and the lemmas `Consume_append` and `Consume_cons`.
3. A session-evolution theorem under asynchronous subtype replacement via `Consume_mono`.
4. A delivery-parametric mechanization profile with a typed effect-bridge artifact scope.

Figure 1. Legacy global proof loop and Coherence-local proof loop. The figure contrasts per-step global obligations with edge-local obligations that compose.

```text
Legacy global-rederivation loop
  (G,D) --step--> (G',D')
     |               |
  rederive global typing + consistency obligations
     |               |
  discharge large cross-edge obligations per step
     v               v
   preservation holds if all global obligations close

Coherence-local loop (this paper)
  (G,D) --step--> (G',D')
      |
  edge_case_split on each checked edge e
      |
  +------------------+-------------------------+----------------------+
  | updated edge     | shared-endpoint edges   | unrelated edges      |
  | local rule lemma | irrelevance transport   | frame transport      |
  +------------------+-------------------------+----------------------+
      |
  Consume_append / Consume_cons discharge alignment obligations
      |
   Coherent(G',D')
```

## 2. Model and Semantics

Configurations are represented by endpoint and edge environments. `GEnv` maps endpoints to local types. `DEnv` maps directed edges to buffered type traces. `Buffers` map directed edges to runtime payload queues.

Table 1 records the model assumptions used for exact statements in this paper.

| Assumption                       | Status                    |
|----------------------------------|---------------------------|
| asynchronous buffered semantics  | required                  |
| active-edge quantification       | required                  |
| fair scheduling profile          | assumed where stated      |
| `DeliveryModel` parameterization | required                  |
| crash-stop and Byzantine claims  | not claimed in this paper |

**Assumption Block 0. Core Model Premises.** Core claims in this paper assume asynchronous buffered semantics, active-edge quantification, and `DeliveryModel` parameterization. Fair scheduling assumptions apply where stated.

**Definition 1. Active Edge.** `ActiveEdge G e` holds when both endpoints of edge `e` are present in `G`.

**Definition 2. Edge Coherence.** `EdgeCoherent G D e` holds when the receiver side can consume the buffered trace on edge `e` under the local type in `G`.

**Definition 3. Coherence.** `Coherent G D` holds when every active edge is edge coherent.

**Definition 4. Consume.** `Consume` is the recursive alignment function that interprets buffered traces against receiver expectations.

Delivery behavior is parameterized by `DeliveryModel`. This gives one theorem shape across FIFO, causal, and lossy instances. Figure 2 shows which edges are checked by `Coherent`.

Figure 2. Active-edge Coherence scope. The figure marks edges that are quantified by `Coherent` and excludes inactive edges.

```text
Session sid = s

  P ---------> C      active (both endpoints present): checked by EdgeCoherent
  ^           |
  |           v
  M <---------+

If endpoint for role M is absent from G:
  edges involving M are inactive and excluded from ActiveEdge quantification.

Formal scope:
  Coherent G D := forall e, ActiveEdge G e -> EdgeCoherent G D e
```

Table 2 fixes shared notation used across all three papers.

| Symbol                                        | Meaning                                                           |
|-----------------------------------------------|-------------------------------------------------------------------|
| $H_{\mathrm{byz}}$                            | Byzantine characterization assumption bundle used in later papers |
| $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$ | Byzantine safety-visible observation projection                   |
| $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$  | Byzantine safety-visible observational equality                   |
| $\mathcal E_{\mathrm{byz}}$                   | Byzantine determinism-envelope relation                           |

Table 3 fixes paper-specific notation used in this paper.

| Symbol               | Meaning                                           |
|----------------------|---------------------------------------------------|
| `Coherent G D`       | global active-edge compatibility invariant        |
| `EdgeCoherent G D e` | edge-local compatibility check                    |
| `Consume`            | trace-to-local-type alignment function            |
| `ActiveEdge G e`     | endpoint-presence guard for coherence obligations |

No aliases are used for shared notation symbols.

### 2.1 Why Coherence

The term follows the linear-logic compatibility tradition from coherence-space semantics and session typing foundations, including Girard (1987), Caires and Pfenning (2010), and Wadler (2012). Usage in this paper is operational rather than denotational.

The key structural correspondence is compatibility. A coherence-space token corresponds to an edge-local communication view, and a clique corresponds to a globally coherent configuration over active edges.

| Coherence-space object  | MPST operational object                          |
|-------------------------|--------------------------------------------------|
| token                   | directed edge with buffered trace and local type |
| coherence relation      | `EdgeCoherent`                                   |
| clique                  | `Coherent` configuration                         |
| linear-map preservation | step preservation theorem                        |

## 3. Worked Example

The worked example is a single-pool capacity protocol with roles `P` for pool, `C` for client, and `M` for monitor. This example is used as a concrete witness for both preservation and subtype-evolution claims.

```text
C -> P : Request(n)
P -> C : Grant(k)
C -> M : Report(k)
M -> P : Confirm
P -> C : Token(t)
```

We focus on one in-flight point where buffer `(P,C)` contains `Grant(k)` and other buffers are empty. At this point the updated edge for the next send or receive action is explicit, and the shared-endpoint versus unrelated-edge cases are explicit. This keeps the preservation proof obligations concrete.

The proof checkpoints are:
1. Send checkpoint on `P -> C : Grant(k)`. The updated-edge obligation is discharged by send lemmas. Shared-endpoint and unrelated-edge obligations are discharged by transport lemmas from the three-way split.
2. Receive checkpoint at `C`. `Consume_cons` reduces the local receive obligation to continuation coherence after consuming `Grant(k)`.
3. Replacement checkpoint for `Grant` refinement. `Consume_mono` with replacement lemmas lifts local receive-side refinement to global coherence preservation.

## 4. Coherence Preservation Architecture

**Theorem 1. Coherence Preservation.** For all environments $G,D,G',D'$, if $(G,D) \to (G',D')$ is a well-typed step in the send and recv and select and branch fragment, then
$$
\mathsf{Coherent}(G,D) \implies \mathsf{Coherent}(G',D').
$$
This claim is exact for one-step preservation in the stated core rule fragment.

*Proof sketch.* The argument is a reusable case-analysis pipeline over edges.

1. Fix a typed one-step transition and an arbitrary edge `e` that is active after the step.
2. Apply `edge_case_split` to partition `e` into:
   - updated edge (`e = e_step`),
   - shared-endpoint edge (`e ≠ e_step ∧ EdgeShares e ep_step`),
   - unrelated edge (`e ≠ e_step ∧ ¬ EdgeShares e ep_step`).
3. Updated-edge case:
   - send/recv/select/branch obligations are discharged by rule-local preservation lemmas,
   - message-to-type alignment is reduced to `Consume_append` (enqueue-facing) or `Consume_cons` (dequeue-facing).
4. Shared-endpoint case:
   - use store/buffer irrelevance lemmas to show unaffected projections are preserved,
   - transport pre-state `EdgeCoherent` to post-state `EdgeCoherent`.
5. Unrelated-edge case:
   - apply frame-style transport (no touched endpoint, no touched buffer segment),
   - conclude edge-local coherence is unchanged.
6. Reassemble all cases to obtain `Coherent(G',D')`.

The same skeleton is used uniformly across send/recv/select/branch, which is the main proof-reuse gain in this paper. ∎

The split operator is implemented by `edge_case_split`. Rule-level preservation lemmas are grouped by send, recv, select, and branch cases. Appendix E provides the file-level inventory.

The architecture is quotient-first. The concrete step relation induces dynamics on equivalence classes once coherence-preserving symmetries are quotiented out.

The quotienting step should be read as symmetry reduction. Distinct interleavings that are equivalent under the symmetry relation are identified as one observable class. This removes schedule noise while preserving the safety-relevant semantics proved in this paper.

```text
     C  --step-->  C'
     |            |
  quotient     quotient
     |            |
    [C] --step--> [C']
```

The square states the commuting condition used across these three papers. This paper establishes the preservation side needed to make the quotient dynamics well-defined.

Figure 3. Three-way edge split for one transition. The figure partitions edges into updated, shared-endpoint, and unrelated classes.

```text
Given step edge u = (A -> B, sid s) and checked edge e:

  Case 1: e = u
    obligation: rule-local preservation on updated edge

  Case 2: e ≠ u and e shares A or B
    obligation: shared-endpoint transport / irrelevance lemmas

  Case 3: e ≠ u and e shares neither endpoint
    obligation: unrelated-edge frame transport

Partition theorem:
  e = u  ∨  (e ≠ u ∧ EdgeShares e ep)  ∨  (e ≠ u ∧ ¬ EdgeShares e ep)
```

## 5. Message-Type Alignment via `Consume`

`Consume` is the proof kernel for message-type alignment. It removes most rule-specific structural complexity from preservation proofs.

**Lemma 1 (`Consume_append`).** Consumption over concatenated traces factors through sequential consumption.

**Lemma 2 (`Consume_cons`).** Head consumption reduces to one-step alignment plus recursive continuation alignment.

*Proof sketch.* The library is centered on `consumeOne` and structural recursion on trace shape.

1. `Consume_append`:
   - induction on trace prefix `ts`,
   - base case `ts = []` is immediate by simplification (`L' = Lr`),
   - step case peels one `consumeOne` transition and applies induction hypothesis to the residual local type.
2. `Consume_cons`:
   - unfold one `Consume` step on head `T`,
   - case split on `consumeOne from T Lr`,
   - resulting equation is definitional in both branches.
3. Preservation integration:
   - send/select proofs use `Consume_append` to justify extending buffered traces,
   - recv/branch proofs use `Consume_cons` to justify consuming the head message and continuing.

This isolates alignment complexity into two reusable lemmas rather than duplicating ad-hoc trace reasoning in each operational rule. ∎

For the worked example, `Consume_cons` discharges the `Grant` receive step at `C` by reducing the obligation to continuation coherence after one aligned message.

## 6. Session Evolution via Subtyping

Session evolution replaces one endpoint local type with a compatible refinement and asks whether coherence is preserved.

This replacement argument follows a standard commutation intuition from trace-equivalence and commuting-conversion lines. The standard point is that local reorderings or local refinements should preserve observable behavior when compatibility conditions hold. What is new here is an operational criterion for asynchronous subtype replacement that is stated directly through `Consume_mono` and discharged with edge-local coherence obligations.

**Assumption Block 1. Replacement Compatibility.** The subtype-evolution theorem assumes endpoint replacement at `ep` satisfies typing-domain preservation, receive-side monotonicity side conditions, and environment consistency for unaffected endpoints.

**Theorem 2. Session Evolution via `Consume_mono`.** For all endpoints $ep$ and environments $G,D,G_{\mathrm{rep}}$, if Assumption Block 1 holds for replacement at $ep$, then
$$
\mathsf{Coherent}(G,D) \implies \mathsf{Coherent}(G_{\mathrm{rep}},D).
$$
This claim is exact for type replacement steps covered by Assumption Block 1.

*Proof sketch.* The replacement theorem is proved by a monotonicity-to-global-lift chain.

1. Local monotonicity:
   - establish receive-compatibility (`RecvCompatible`) between old and replacement local types,
   - apply `Consume_mono` to show every successful old consumption remains successful after replacement.
2. Edge lift:
   - use `EdgeCoherent_type_replacement` on edges targeting the replaced endpoint,
   - for non-target edges, transport coherence by environment agreement.
3. Global lift:
   - combine edge cases to derive `Coherent_type_replacement`.
4. Progress compatibility:
   - use liveness-side lemmas (`progress_conditions_type_replacement`) to preserve operational side conditions.

Hence compatible subtype replacement preserves Coherence without re-running global derivations. ∎

Core artifacts are the subtype-replacement core and liveness layers. Figure 4 shows the commuting replacement argument. Appendix E provides the file-level mapping.

Figure 4. Replacement commuting argument. The figure compares replace-then-check with check-then-monotonicity.

```text
            replacement at ep
   (G,D) ----------------------------> (G_rep,D)
     |                                    |
     | Coherent check                     | Coherent check
     v                                    v
  true/false  ---------monotonicity----> true/false

Commuting reading:
  check(Coherent, replace(ep, G), D)
    follows from
  check(Coherent, G, D) + Consume_mono + replacement side conditions
```

## 7. Mechanization and Artifact Summary

Table 4 maps each core claim to concrete modules and representative theorem anchors.

| Claim                                                    | Primary modules                                                                                               | Representative anchors |
|----------------------------------------------------------|----------------------------------------------------------------------------------------------------------------|------------------------|
| Definitions of `ActiveEdge`, `EdgeCoherent`, `Coherent` | `lean/Protocol/Coherence/Consume.lean`, `lean/Protocol/Coherence/EdgeCoherenceCore.lean`                    | `Consume`, `EdgeCoherent`, `Coherent` |
| `Consume` kernel                                         | `lean/Protocol/Coherence/Consume.lean`                                                                        | `Consume_append`, `Consume_cons` |
| Three-way split infrastructure                           | `lean/Protocol/Coherence/Unified.lean`                                                                        | `edge_case_split` |
| Preservation family                                      | `lean/Protocol/Coherence/Preservation.lean`, `lean/Protocol/Coherence/PreservationRecv.lean`, `lean/Protocol/Coherence/SelectPreservation.lean` | `Coherent_send_preserved`, `Coherent_recv_preserved`, `Coherent_select_preserved`, `Coherent_branch_preserved` |
| Delivery-model variants                                  | `lean/Protocol/DeliveryModel.lean`, `lean/Protocol/Coherence/PreservationDeliveryModels.lean`               | `FIFODelivery_laws`, `CausalDelivery_laws`, `LossyDelivery_laws` |
| Subtype replacement and evolution                        | `lean/Protocol/Coherence/SubtypeReplacementCore.lean`, `lean/Protocol/Coherence/SubtypeReplacementLiveness.lean` | `Consume_mono`, `Coherent_type_replacement`, `CoherenceTransform_preserves_coherent` |

Table 5 adds runtime bridge artifacts referenced in Section 8.

| Bridge claim                                   | Primary modules                                                                 | Representative anchors |
|------------------------------------------------|----------------------------------------------------------------------------------|------------------------|
| effect-observation bridge                      | `lean/Runtime/Proofs/EffectBisim/Bridge.lean`                                  | `effectBisim_implies_observationalEquivalence` |
| quotient/effect compatibility                  | `lean/Runtime/Proofs/EffectBisim/ConfigEquivBridge.lean`                       | `configEquiv_iff_effectBisim_silent` |
| runtime monitoring and handler typing boundary | `lean/Runtime/VM/Runtime/Monitor.lean`                                         | `monitor_sound`, `unified_monitor_preserves` |

## 8. Extended Artifact: Effect-Typed Bridge

`EffectSpec.handlerType` records typed effect obligations at the VM boundary. Runtime typing uses these obligations in the VM execution layer.

**Proposition 1. Bridge Soundness, Artifact Scope.** For any selected handler $h$, if choreography obligations for $h$ are discharged and `EffectSpec.handlerType` holds for $h$, then VM-side typing obligations generated from $h$ are satisfied in the corresponding runtime instruction layer.

Scope note on coinduction: in this architecture, coinductive runtime theorems are used for extensional observer-level equivalence and quotient compatibility (for example `effectBisim_implies_observationalEquivalence` and `configEquiv_iff_effectBisim_silent`). Finite-step preservation internals remain in the inductive Coherence/`Consume` stack of Sections 4-6.

Table 6 gives bridge intent.

| Bridge item             | Role                        |
|-------------------------|-----------------------------|
| choreography obligation | source protocol obligation  |
| effect handler typing   | typed executable obligation |
| VM runtime typing check | enforcement layer           |

The bridge is included to keep the protocol proof layer and executable layer aligned.

**Assumption Block 2. Byzantine Interface Premises.** The interface statements in this section assume shared notation for $H_{\mathrm{byz}}$, $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, and $\mathcal E_{\mathrm{byz}}$, plus theorem-pack capability naming consistency between abstract and runtime layers.

**Theorem BZ-1. Byzantine Interface Well-Formedness.** Under Assumption Block 2, Byzantine safety-track statements are well-formed over the same Coherence domain used in Sections 4-6: the safety-visible symbols $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, and $\mathcal E_{\mathrm{byz}}$ are interpreted over configurations whose edge-local obligations are exactly those discharged by `Coherent` and `Consume`.

*Proof sketch.* This is a domain-compatibility theorem. Section 2 fixes shared symbols and their domains; Sections 4-6 prove that Coherence obligations are preserved under the core step and replacement transformations; Section 8 bridges configuration equivalence and observational interfaces at runtime (`configEquiv_iff_effectBisim_silent`). Therefore the Byzantine symbols are anchored to a stable, step-preserved state domain. ∎

**Corollary BZ-1.1. Dropped-Assumption Witness Interface.** Let $\mathcal A$ be any assumption class named in $H_{\mathrm{byz}}$. If a later construction provides a witness violating $\mathsf{ByzSafe}$ when $\mathcal A$ is dropped, then that witness can be expressed against the same active-edge Coherence interface used in this paper.

*Proof sketch.* The witness obligation is purely interface-level here: violating traces/configurations are represented in the same configuration language and observation interface fixed above, and local compatibility obligations are phrased with `EdgeCoherent`/`Consume`. No new base semantics is required at this layer. ∎

**Proposition BZ-1.2. Capability-Gated VM Interface.** If a runtime profile includes Byzantine characterization and envelope-adherence capability artifacts, then safety-visible runtime obligations are interpreted through $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$ modulo $\mathcal E_{\mathrm{byz}}$, and profile admission is blocked when required artifacts are absent.

*Proof sketch.* The profile gate is a conjunction of named capability artifacts. Section 8 supplies the protocol-to-runtime typing bridge (`EffectSpec.handlerType` and monitor soundness) plus observational quotient compatibility (`effectBisim_implies_observationalEquivalence`, `configEquiv_iff_effectBisim_silent`). Hence interpretation is well-defined when bits are present and intentionally unavailable when missing. ∎

## 9. Related Work

Binary duality and global re-derivation lines established important foundations for session safety (Honda et al., 2008). Recent mechanization work highlights brittleness in large MPST proof stacks and motivates reusable proof kernels (Tirore, Bengtson, and Carbone, 2025).

Program-logical lines such as Actris operate at a different verification layer and target program proofs over protocol resources (Hinrichsen et al., 2020). Event-structure and partial-order lines provide alternate macro views of concurrency (Castellan et al., 2023).

The delta in this paper is a single local invariant kernel with a reusable proof split and a monotonic evolution theorem. Our contribution is structural and mechanized.

Table 7 gives the concrete prior-work delta used by this paper.

| Prior limitation                                       | This paper's delta                                |
|--------------------------------------------------------|---------------------------------------------------|
| preservation tied to repeated global re-derivation     | reusable edge-local preservation skeleton         |
| weak abstraction boundary between theory and execution | explicit effect-typed bridge as artifact layer    |
| FIFO-centric semantics in many developments            | one theorem shape under `DeliveryModel` instances |
| fragmented preservation proof structure                | one split kernel plus `Consume` alignment lemmas  |

The first row isolates the primary metatheory delta. The proof kernel is local by construction and avoids per-step global re-derivation.

The second and third rows isolate engineering deltas. The effect-typed bridge keeps theorem obligations aligned with runtime typing, and the delivery-model abstraction keeps one theorem shape across FIFO, causal, and lossy variants.

The fourth row isolates proof-architecture reuse. One split kernel plus one alignment kernel supports the preservation family and the evolution theorem.

## 10. Limitations and Scope

This paper proves preservation-style safety only: active-edge coherence is preserved for the core asynchronous rule family, and coherence is stable under subtype replacement when replacement preserves typing domains, satisfies receive-side monotonicity, and keeps unaffected endpoints environment-consistent.

Quantitative, fault-characterization, and envelope-level claims are proved in later papers within this series.

## 11. Conclusion

The paper isolates a reusable preservation kernel for asynchronous buffered MPST. The kernel is active-edge coherence plus `Consume`-based alignment. The same kernel supports subtype-driven session evolution through `Consume_mono`. The result is a mechanized foundation that is small, compositional, and extensible.

## 12. Works Cited

Caires, L., and Pfenning, F. (2010). Session Types as Intuitionistic Linear Propositions. CONCUR 2010.

Castellan, S., et al. (2023). Event-structure and partial-order semantics for session-based concurrency. Journal of Logic and Algebraic Methods in Programming.

Cover, T. M., and Thomas, J. A. (2006). Elements of Information Theory (2nd ed.). Wiley.

Girard, J.-Y. (1987). Linear Logic. Theoretical Computer Science, 50(1), 1-101.

Hinrichsen, J., et al. (2020). Actris: Session-type based reasoning in separation logic. POPL 2020.

Honda, K., Yoshida, N., and Carbone, M. (2008). Multiparty Asynchronous Session Types. POPL 2008.

Shannon, C. E. (1948). A Mathematical Theory of Communication. Bell System Technical Journal, 27(3), 379-423 and 27(4), 623-656.

Tirore, L., Bengtson, J., and Carbone, M. (2025). Mechanized MPST metatheory with subject-reduction robustness analysis. ECOOP 2025.

Wadler, P. (2012). Propositions as Sessions. ICFP 2012.

## Appendices

## Appendix A. Syntax and Judgments

### A.1 Local Types

We use local types generated by:

```text
L ::= end
    | send r T L
    | recv r T L
    | select r {li : Li}i
    | branch r {li : Li}i
    | mu L
```

### A.2 Configurations and Active Edges

A configuration is a pair `(G, D)` where `G` is an endpoint-typing environment and `D` is a delayed-trace environment indexed by directed edges. The predicate `ActiveEdge G e` identifies edges whose local obligations must be checked after a transition.

### A.3 Coherence Judgment

The global invariant is:

```text
Coherent G D := forall e, ActiveEdge G e -> EdgeCoherent G D e
```

The transition fragment considered in this paper is the asynchronous send/recv/select/branch core with the side conditions stated in Section 4.

## Appendix B. Deferred Proof of Theorem 1

This appendix gives the deferred proof structure for coherence preservation.

**Lemma B.1 (Edge Partition).** For any checked edge `e`, updated edge `u`, and endpoint `ep`, exactly one of the following holds:

```text
e = u  or  (e != u and EdgeShares e ep)  or  (e != u and not EdgeShares e ep)
```

*Proof sketch.* Case analysis by edge equality and endpoint incidence (`edge_case_split`).

**Lemma B.2 (Updated-Edge Preservation).** In each core operational rule, the updated edge satisfies post-step coherence.

*Proof sketch.* Reduce queue and trace alignment obligations to `Consume_append` and `Consume_cons`.

**Lemma B.3 (Shared-Endpoint Transport).** If an edge shares one endpoint with the updated edge but is not updated itself, coherence transports across the step.

*Proof sketch.* Apply endpoint-sharing irrelevance and unchanged-component lemmas.

**Lemma B.4 (Unrelated-Edge Transport).** If an edge shares no endpoint with the updated edge, coherence is preserved by frame-style extensionality.

*Proof sketch.* Unchanged maps and domains imply unchanged edge-local obligations.

**Proof of Theorem 1.** By Lemma B.1, split on updated/shared/unrelated cases. Discharge each branch with Lemmas B.2-B.4. Therefore `Coherent` is preserved by each core transition. ∎

## Appendix C. Deferred Proof of Theorem 2

### C.1 `Consume` Algebra

`Consume` is defined by the primitive matcher `consumeOne`:

```text
Consume from L []      = some L
Consume from L (t::ts) =
  match consumeOne from t L with
  | none    => none
  | some L' => Consume from L' ts
```

**Lemma C.1 (`Consume_append`).** Consumption over concatenated traces factors through sequential consumption.

**Lemma C.2 (`Consume_cons`).** Consumption of a non-empty trace factors through one head-step and recursive tail consumption.

### C.2 Replacement Monotonicity

Receive compatibility is captured by `RecvCompatible`; replacement monotonicity is captured by `Consume_mono`.

**Proposition C.3 (Edge Lift).** `Consume_mono` lifts to `EdgeCoherent_type_replacement` on affected edges.

**Proposition C.4 (Global Lift).** Under replacement side conditions, edge lift induces `Coherent_type_replacement`.

**Proof of Theorem 2.** Combine Lemmas C.1-C.2 with Propositions C.3-C.4 and the replacement side conditions from Section 6. ∎

## Appendix D. Delivery Parametricity and Runtime Bridge

### D.1 Delivery-Model Interface

Preservation is parameterized by a `ConsumeM` law family (`nil`, `append`, `cons`, and renaming stability). FIFO, causal, and lossy models are instances of this interface.

### D.2 Effect-Typed Bridge

Runtime obligations are encoded by `EffectSpec.handlerType` and discharged against VM monitor/adherence checks.

**Proposition D.1 (Bridge Soundness).** If choreography-side obligations hold for handler `h` and `EffectSpec.handlerType` holds for `h`, then generated VM typing obligations for `h` are satisfied.

**Proposition D.2 (Observation/Quotient Compatibility).** The effect-bisimulation bridge and configuration-equivalence bridge preserve compatibility with the protocol-level quotient.

Byzantine-facing statements in Section 8 are interface commitments in this paper: domain alignment and capability contracts, not a full downstream Byzantine liveness development.

## Appendix E. Mechanization Map

| Result family | Primary modules |
|---------------|-----------------|
| Coherence core and `Consume` | `lean/Protocol/Coherence/Consume.lean`, `lean/Protocol/Coherence/EdgeCoherenceCore.lean` |
| Preservation split and rule cases | `lean/Protocol/Coherence/Unified.lean`, `lean/Protocol/Coherence/Preservation*.lean`, `lean/Protocol/Coherence/SelectPreservation.lean` |
| Delivery-parametric preservation | `lean/Protocol/DeliveryModel.lean`, `lean/Protocol/Coherence/PreservationDeliveryModels.lean` |
| Subtype replacement and liveness lift | `lean/Protocol/Coherence/SubtypeReplacementCore.lean`, `lean/Protocol/Coherence/SubtypeReplacementLiveness.lean` |
| Runtime bridge | `lean/Runtime/VM/Runtime/Monitor.lean`, `lean/Runtime/Proofs/EffectBisim/Bridge.lean`, `lean/Runtime/Proofs/EffectBisim/ConfigEquivBridge.lean` |

## Appendix F. Reproducibility

Reproduction uses the repository-pinned Lean toolchain and manifest. The appendix modules in Appendix E are rebuilt with `lake build`; project-level consistency checks use `just escape` and `just verify-protocols`.

## Appendix G. Index of Main Results

| Claim | Main section | Assumption scope | Formal location |
|-------|--------------|------------------|-----------------|
| Theorem 1. Coherence Preservation | Section 4 | Assumption Block 0 + send/recv/select/branch fragment | `Preservation*.lean`, `SelectPreservation.lean`; Appendix B |
| Theorem 2. Session Evolution via `Consume_mono` | Section 6 | Assumption Block 1 replacement compatibility | `SubtypeReplacementCore.lean`, `SubtypeReplacementLiveness.lean`; Appendix C |
| Proposition 1. Bridge Soundness (artifact scope) | Section 8 | Assumption Block 0 + discharged choreography obligations | runtime bridge modules; Appendix D |
| Theorem BZ-1. Byzantine Interface Well-Formedness | Section 8 | Assumption Block 2 Byzantine interface premises | interface contract in Section 8; Appendix D |
| Corollary BZ-1.1. Dropped-Assumption Witness Interface | Section 8 | Assumption Block 2 + witness premise | interface contract in Section 8; Appendix D |
| Proposition BZ-1.2. Capability-Gated VM Interface | Section 8 | Assumption Block 2 + capability-gating assumptions | interface contract in Section 8; Appendix D |
