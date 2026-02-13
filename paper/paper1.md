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

The contributions are explicit.

1. A local preservation architecture based on active-edge `Coherence` and a reusable three-way edge split.
2. A message-alignment proof kernel through `Consume` and the lemmas `Consume_append` and `Consume_cons`.
3. A session-evolution theorem under asynchronous subtype replacement via `Consume_mono`.
4. A delivery-parametric mechanization profile with a typed effect-bridge artifact scope.

Figure 1. Legacy global proof loop and Coherence-local proof loop. The figure contrasts per-step global obligations with edge-local obligations that compose.

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

*Proof sketch.* The proof performs a three-way split on the checked edge. Case one is the updated edge. Case two shares one endpoint with the updated edge. Case three is unrelated. Cases two and three use irrelevance transport lemmas and the updated-edge case uses rule-specific local obligations. ∎

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

## 5. Message-Type Alignment via `Consume`

`Consume` is the proof kernel for message-type alignment. It removes most rule-specific structural complexity from preservation proofs.

**Lemma 1 (`Consume_append`).** Consumption over concatenated traces factors through sequential consumption.

**Lemma 2 (`Consume_cons`).** Head consumption reduces to one-step alignment plus recursive continuation alignment.

*Proof sketch.* Both lemmas are proved by structural recursion on local type and trace shape with case splits on constructors. The recursion exposes the precise alignment obligations used in send and recv preservation proofs. ∎

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

*Proof sketch.* The proof first applies monotonicity of `Consume` via `Consume_mono`. It then lifts edge-local replacement to global coherence through `EdgeCoherent_type_replacement` and `Coherent_type_replacement`. Finally it transports progress-side obligations through the replacement layer in `SubtypeReplacementLiveness`. ∎

Core artifacts are the subtype-replacement core and liveness layers. Figure 4 shows the commuting replacement argument. Appendix E provides the file-level mapping.

Figure 4. Replacement commuting argument. The figure compares replace-then-check with check-then-monotonicity.

## 7. Mechanization and Artifact Summary

Table 4 maps paper claims to artifact groups.

| Claim                                                   | Artifact group                                     |
|---------------------------------------------------------|----------------------------------------------------|
| Definitions of `ActiveEdge`, `EdgeCoherent`, `Coherent` | Edge-coherence core definitions                    |
| `Consume` kernel                                        | Consume alignment library                          |
| Three-way split infrastructure                          | Unified edge-case split infrastructure             |
| Preservation family                                     | Send, recv, select, and branch preservation layers |
| Delivery-model variants                                 | Delivery-parametric preservation layer             |
| Subtype replacement and evolution                       | Subtype-replacement core and liveness layers       |

Build commands are listed in Appendix F. Full artifact indexing is deferred to Appendix E and Appendix F.

## 8. Extended Artifact: Effect-Typed Bridge

`EffectSpec.handlerType` records typed effect obligations at the VM boundary. Runtime typing uses these obligations in the VM execution layer.

**Proposition 1. Bridge Soundness, Artifact Scope.** For any selected handler $h$, if choreography obligations for $h$ are discharged and `EffectSpec.handlerType` holds for $h$, then VM-side typing obligations generated from $h$ are satisfied in the corresponding runtime instruction layer.

Scope note on coinduction: in this architecture, coinductive runtime theorems are used for extensional observer-level equivalence and quotient compatibility (for example `effectBisim_implies_observationalEquivalence` and `configEquiv_iff_effectBisim_silent`). Finite-step preservation internals remain in the inductive Coherence/`Consume` stack of Sections 4-6.

Table 5 gives bridge intent.

| Bridge item             | Role                        |
|-------------------------|-----------------------------|
| choreography obligation | source protocol obligation  |
| effect handler typing   | typed executable obligation |
| VM runtime typing check | enforcement layer           |

The bridge is included to keep the protocol proof layer and executable layer aligned.

**Assumption Block 2. Byzantine Interface Premises.** The interface statements in this section assume shared notation for $H_{\mathrm{byz}}$, $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, and $\mathcal E_{\mathrm{byz}}$, plus theorem-pack capability naming consistency between abstract and runtime layers.

**Theorem BZ-1. Exact Byzantine Characterization Interface.** Under assumption bundle $H_{\mathrm{byz}}$, later papers prove an exact Byzantine safety characterization
$$
\mathsf{ByzSafe} \iff \mathsf{ByzChar}.
$$
This paper provides the Coherence and `Consume` interfaces consumed by that theorem.

**Corollary BZ-1.1. Converse Counterexample Interface.** If a required assumption class in $H_{\mathrm{byz}}$ is dropped, later papers provide counterexample families violating $\mathsf{ByzSafe}$. This paper provides the local-invariant interfaces needed for those constructions.

**Proposition BZ-1.2. VM Bridge Interface.** If a runtime profile carries Byzantine characterization and envelope-adherence capability artifacts, then safety-visible obligations are interpreted through $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$ modulo $\mathcal E_{\mathrm{byz}}$. Full adherence packaging is discharged in later papers.

## 9. Related Work

Binary duality and global re-derivation lines established important foundations for session safety (Honda et al., 2008). Recent mechanization work highlights brittleness in large MPST proof stacks and motivates reusable proof kernels (Tirore, Bengtson, and Carbone, 2025).

Program-logical lines such as Actris operate at a different verification layer and target program proofs over protocol resources (Hinrichsen et al., 2020). Event-structure and partial-order lines provide alternate macro views of concurrency (Castellan et al., 2023).

The delta in this paper is a single local invariant kernel with a reusable proof split and a monotonic evolution theorem. Our contribution is structural and mechanized.

Table 6 gives the concrete prior-work delta used by this paper.

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

## Appendix A. Formal Preliminaries and Notation

Full syntax and environment definitions. Step rules and typing judgments. Lookup and update support lemmas.

## Appendix B. Full Preservation Proof Details

Updated-edge proofs. Shared-endpoint irrelevance lemmas. Unrelated-edge transport lemmas.

## Appendix C. `Consume` and Session Evolution Library

`Consume` definition and recursion setup. `Consume_append` and `Consume_cons` proofs. Replacement and evolution theorem chain.

## Appendix D. Delivery and Effect Bridge Details

`DeliveryModel` laws and instance obligations. FIFO, causal, and lossy notes. Effect typing obligations for handlers.

## Appendix E. Mechanization Inventory

File-level inventory and theorem index mapping.

## Appendix F. Reproducibility Notes

Build commands, theorem index by file, and artifact checklist.

Toolchain pinning is part of reproducibility. The exact Lean toolchain version, dependency revisions, and repository commit hash are recorded in the artifact metadata and `lake` manifest files.

```bash
lake build Protocol.Coherence.Preservation
lake build Protocol.Coherence.SubtypeReplacement
lake build Protocol.Coherence.PreservationDeliveryModels
```

The commands above reproduce the primary theorem modules for this paper.

## Appendix G. Theorem Index

| Claim                                                    | Main section | Assumption scope                                                                                                                    | Proof location                                            |
|----------------------------------------------------------|--------------|-------------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------|
| Theorem 1. Coherence Preservation                        | Section 4    | Assumption Block 0 core model premises plus send and recv and select and branch fragment                                            | Section 4 proof sketch, Appendix B                        |
| Theorem 2. Session Evolution via `Consume_mono`          | Section 6    | Assumption Block 1 replacement compatibility                                                                                        | Section 6 proof sketch, Appendix C                        |
| Proposition 1. Bridge Soundness, Artifact Scope          | Section 8    | Assumption Block 0 core model premises plus discharged choreography obligations and `EffectSpec.handlerType` for selected handler   | Section 8 statement, Appendix D                           |
| Theorem BZ-1. Exact Byzantine Characterization Interface | Section 8    | Assumption Block 2 Byzantine interface premises                                                                                     | Section 8 statement                                       |
| Corollary BZ-1.1. Converse Counterexample Interface      | Section 8    | Assumption Block 2 premises plus theorem BZ-1 premises                                                                              | Section 8 statement                                       |
| Proposition BZ-1.2. VM Bridge Interface                  | Section 8    | Assumption Block 2 premises plus capability and envelope-notation interface assumptions                                             | Section 8 statement                                       |
