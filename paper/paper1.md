# Coherence for Asynchronous Buffered MPST: A Mechanized Metatheory

## Abstract

We recast preservation for asynchronous buffered multiparty session types from global re-derivation to `Coherence`, an active-edge local invariant of receiver-buffer compatibility.

We prove two central results. The first gives a reusable preservation architecture based on a three-way edge split. The second result proves session evolution under asynchronous subtype replacement through `Consume_mono`.

The metatheory is parametric in delivery semantics through `DeliveryModel`, with FIFO, causal, and lossy instances. The core claims are mechanized in Lean 4. A supporting bridge relates choreography obligations to VM obligations through typed effect handlers.

## 1. Introduction

Asynchronous buffered MPST proofs are typically organized around repeated global re-derivation after each transition (Honda, 1993; Honda, Vasconcelos, and Kubo, 1998; Honda et al., 2008; Tirore, Bengtson, and Carbone, 2025). That structure is costly and brittle when step relations grow.

This paper replaces that structure with active-edge local reasoning. The local invariant is `Coherence`, and preservation is proved by composing edge-local obligations in a style compatible with local proof decomposition used in program logics and local-reasoning traditions (Reynolds, 2002; O'Hearn, 2007; Hinrichsen et al., 2020).

The local-to-global shape follows a standard invariant method. Local obligations are proved on small footprints and then lifted to global safety by composition. This proof organization also aligns with structural operational and process-calculus decompositions (Plotkin, 1981; Milner, Parrow, and Walker, 1992; Milner, 1999). What is new here is the active-edge specialization for asynchronous buffered MPST, where the lift is carried by one explicit three-way edge split and one reusable `Consume` alignment kernel.

An information-theoretic reading is also useful. Projection and monitoring act as observation channels from executions to externally visible traces (Shannon, 1948). This paper establishes the zero-loss baseline for that channel at the Coherence layer, so later envelope results can add controlled distortion contracts (Cover and Thomas, 2006).

The paper has two central claims. Claim one is Coherence preservation through a reusable proof skeleton. Claim two is session evolution through subtype replacement via `Consume_mono`.

The three-paper dependency is direct. This paper defines the invariant kernel, *Computable Dynamics for Asynchronous MPST* builds quantitative and decision procedures on that kernel, and *Harmony from Coherence in Asynchronous MPST* adds reconfiguration commutation and envelope exactness.

Scope is restricted to asynchronous buffered semantics, active-edge quantification, classical payloads, and `DeliveryModel` parameterization. Quantitative fairness-dependent bounds are deferred to *Computable Dynamics for Asynchronous MPST*. Reconfiguration and envelope claims are deferred to *Harmony from Coherence in Asynchronous MPST*. Byzantine safety in this paper appears as a supporting interface claim (Section 8) over shared symbols $H_{\mathrm{byz}}$, $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, and $\mathcal E_{\mathrm{byz}}$; exact Byzantine characterization is deferred to later papers in the series. Figure 1 shows the proof architecture shift.

Our contributions are as follows:

1. A local preservation architecture based on active-edge `Coherence` and a reusable three-way edge split.
2. A message-alignment proof kernel through `Consume` and the lemmas `Consume_append` and `Consume_cons`.
3. A session-evolution theorem under asynchronous subtype replacement via `Consume_mono`.
4. A delivery-parametric mechanization profile with a typed effect bridge to the VM layer.

Figure 1 (schematic). The preservation argument is reorganized from global re-derivation to local case analysis. For each step $(G,D)\to(G',D')$, we prove edge-local obligations for updated/shared/unrelated edges and reassemble
$$
\forall e,\ \mathsf{ActiveEdge}(G',e) \to \mathsf{EdgeCoherent}(G',D',e),
$$
that is, $\mathsf{Coherent}(G',D')$.

## 2. Model and Semantics

Configurations are represented by endpoint and edge environments. `GEnv` maps endpoints to local types. `DEnv` maps directed edges to buffered type traces. `Buffers` map directed edges to runtime payload queues.

Table 1 records the model assumptions used for exact statements in this paper.

| Assumption                       | Status                    |
|----------------------------------|---------------------------|
| asynchronous buffered semantics  | required                  |
| active-edge quantification       | required                  |
| fair scheduling profile          | assumed where stated      |
| `DeliveryModel` parameterization | required                  |
| crash-stop and Byzantine claims  | supporting interface claim only |

**Assumption Block 0. Core Model Premises.** Core claims in this paper assume asynchronous buffered semantics, active-edge quantification, and `DeliveryModel` parameterization. Fair scheduling assumptions apply where stated.

**Definition 1. Active Edge.** `ActiveEdge G e` holds when both endpoints of edge `e` are present in `G`.

**Definition 2. Edge Coherence.** `EdgeCoherent G D e` holds when the receiver side can consume the buffered trace on edge `e` under the local type in `G`.

**Definition 3. Coherence.** `Coherent G D` holds when every active edge is edge coherent.

**Definition 4. Consume.** `Consume` is the recursive alignment function that interprets buffered traces against receiver expectations.

**Definition 5. Byzantine Interface Well-Formedness.** `ByzIfaceWF G D` is the interface predicate used for Byzantine-facing statements in this paper, and is mechanized as a definitional alias of `Coherent G D`.

Delivery behavior is parameterized by `DeliveryModel`. This gives one theorem shape across FIFO, causal, and lossy instances. Figure 2 records the active-edge quantification boundary:
$$
\mathsf{Coherent}(G,D)\ :=\ \forall e,\ \mathsf{ActiveEdge}(G,e)\to\mathsf{EdgeCoherent}(G,D,e).
$$
Edges incident to absent endpoints are excluded by `ActiveEdge`.

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

Operationally, our edge-local notion also sits in the lineage connecting session typing, subtyping, and communicating-automata views (Gay and Hole, 2005; Deniélou and Yoshida, 2012; Brand and Zafiropulo, 1983).

The key structural correspondence is compatibility. A coherence-space token corresponds to an edge-local communication view, and a clique corresponds to a globally coherent configuration over active edges.

| Coherence-space object  | MPST operational object                          |
|-------------------------|--------------------------------------------------|
| token                   | directed edge with buffered trace and local type |
| coherence relation      | `EdgeCoherent`                                   |
| clique                  | `Coherent` configuration                         |
| linear-map preservation | step preservation theorem                        |

## 3. Worked Example

We use one running example throughout the paper.

**Running Example 3.1 (Single-Pool Capacity Session).**
Roles are `C` (client), `P` (pool), and `M` (monitor), with global interaction:

```text
C -> P : Request(n)
P -> C : Grant(k)
C -> M : Report(k)
M -> P : Confirm
P -> C : Token(t)
```

Fix local continuations:

```text
L_C := recv P Grant(k); send M Report(k); recv P Token(t); end
L_P := recv M Confirm; send C Token(t); end
L_M := recv C Report(k); send P Confirm; end
```

and in-flight configuration `(G_0,D_0)`:

```text
G_0(C) = L_C
G_0(P) = L_P
G_0(M) = L_M
D_0(P,C) = [Grant(k)]
D_0(e)   = []    for e != (P,C)
```

Assume typing judgment `\Gamma \vdash (G_0,D_0)\ \mathsf{wf}`.

The active-edge obligation is:
$$
\forall e,\ \mathsf{ActiveEdge}(G_0,e)\to \mathsf{EdgeCoherent}(G_0,D_0,e).
$$

The example is used via the following derived rule instances.

$$
\dfrac{
  \Gamma \vdash (G_0,D_0)\ \mathsf{wf}
  \quad
  D_0(P,C)=[\mathrm{Grant}(k)]
  \quad
  \mathsf{Consume\_cons}
}{
  \Gamma \vdash (G_0,D_0)\to_{\mathsf{recv}\ C}(G_1,D_1)
  \quad\land\quad
  \mathsf{EdgeCoherent}(G_1,D_1,(P,C))
}
\;(\textsc{Ex-RecvGrant})
$$

$$
\dfrac{
  \Gamma \vdash (G_1,D_1)\ \mathsf{wf}
  \quad
  \mathsf{Consume\_append}
}{
  \Gamma \vdash (G_1,D_1)\to_{\mathsf{send}\ C\to M:\mathrm{Report}(k)}(G_2,D_2)
  \quad\land\quad
  \mathsf{EdgeCoherent}(G_2,D_2,(C,M))
}
\;(\textsc{Ex-SendReport})
$$

$$
\dfrac{
  \mathsf{Coherent}(G_0,D_0)
  \quad
  \mathsf{RecvCompatible}(G_0(C),G'_0(C))
  \quad
  \mathsf{Consume\_mono}
}{
  \mathsf{Coherent}(G'_0,D_0)
}
\;(\textsc{Ex-ReplaceC})
$$

For the step edge `u=(C,M)`, the case split used later is:
updated (`e=u`), shared-endpoint (`e\neq u \land EdgeShares(e,C\ \text{or}\ M)`), and unrelated (`e\neq u` and no shared endpoint).

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

The quotienting step should be read as symmetry reduction. Distinct interleavings that are equivalent under the symmetry relation are identified as one observable class. Formally, the induced square is:
$$
q(\mathsf{step}(C))\ =\ \mathsf{step}_{/ \sim}(q(C)).
$$

The square states the commuting condition used across these three papers. This paper establishes the preservation side needed to make the quotient dynamics well-defined.

Figure 3 (case partition). For step edge $u$ and checked edge $e$:
$$
e = u\ \lor\ (e\neq u\land \mathsf{EdgeShares}(e,\mathit{ep}))\ \lor\ (e\neq u\land \neg \mathsf{EdgeShares}(e,\mathit{ep})).
$$
The three branches are discharged by updated-edge preservation, shared-endpoint transport, and unrelated-edge frame transport, respectively.

## 5. Message-Type Alignment via `Consume`

`Consume` is the proof kernel for message-type alignment. It removes most rule-specific structural complexity from preservation proofs.

**Lemma 1. Consume_append.** Consumption over concatenated traces factors through sequential consumption.

**Lemma 2. Consume_cons.** Head consumption reduces to one-step alignment plus recursive continuation alignment.

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

Core lemmas are in the subtype-replacement core and liveness layers. Figure 4 expresses the replacement commutation principle used in Section 6:
$$
\mathsf{Coherent}(G,D)\ \land\ \mathsf{Compat}_{ep}(G,G_{\mathrm{rep}})
\Longrightarrow
\mathsf{Coherent}(G_{\mathrm{rep}},D),
$$
with compatibility discharged by `Consume_mono` and replacement side conditions.

## 7. Mechanization Summary

Table 4 maps each core claim to concrete modules and representative theorem anchors.

| Claim                                                    | Primary modules                                                                                               | Representative anchors |
|----------------------------------------------------------|----------------------------------------------------------------------------------------------------------------|------------------------|
| Definitions of `ActiveEdge`, `EdgeCoherent`, `Coherent` | `lean/Protocol/Coherence/Consume.lean`, `lean/Protocol/Coherence/EdgeCoherenceCore.lean`                    | `Consume`, `EdgeCoherent`, `Coherent` |
| `Consume` kernel                                         | `lean/Protocol/Coherence/Consume.lean`                                                                        | `Consume_append`, `Consume_cons` |
| Three-way split infrastructure                           | `lean/Protocol/Coherence/Unified.lean`                                                                        | `edge_case_split` |
| Preservation family                                      | `lean/Protocol/Coherence/Preservation.lean`, `lean/Protocol/Coherence/PreservationRecv.lean`, `lean/Protocol/Coherence/SelectPreservation.lean` | `Coherent_send_preserved`, `Coherent_recv_preserved`, `Coherent_select_preserved`, `Coherent_branch_preserved` |
| Delivery-model variants                                  | `lean/Protocol/DeliveryModel.lean`, `lean/Protocol/Coherence/PreservationDeliveryModels.lean`               | `FIFODelivery_laws`, `CausalDelivery_laws`, `LossyDelivery_laws` |
| Subtype replacement and evolution                        | `lean/Protocol/Coherence/SubtypeReplacementCore.lean`, `lean/Protocol/Coherence/SubtypeReplacementLiveness.lean` | `Consume_mono`, `Coherent_type_replacement`, `CoherenceTransform_preserves_coherent` |

Table 5 adds runtime bridge components referenced in Section 8.

| Bridge claim                                   | Primary modules                                                                 | Representative anchors |
|------------------------------------------------|----------------------------------------------------------------------------------|------------------------|
| effect-observation bridge                      | `lean/Runtime/Proofs/EffectBisim/Bridge.lean`                                  | `effectBisim_implies_observationalEquivalence` |
| quotient/effect compatibility                  | `lean/Runtime/Proofs/EffectBisim/ConfigEquivBridge.lean`                       | `configEquiv_iff_effectBisim_silent` |
| runtime monitoring and handler typing boundary | `lean/Runtime/VM/Runtime/Monitor.lean`                                         | `monitor_sound`, `unified_monitor_preserves` |

## 8. Effect-Typed Bridge

`EffectSpec.handlerType` records typed effect obligations at the VM boundary. Runtime typing uses these obligations in the VM execution layer.

**Proposition 1. Bridge Soundness.** For any selected handler $h$, if choreography obligations for $h$ are discharged and `EffectSpec.handlerType` holds for $h$, then VM-side typing obligations generated from $h$ are satisfied in the corresponding runtime instruction layer.

*Proof sketch.* Let $h$ satisfy choreography-side obligations and `EffectSpec.handlerType`. Use the monitor contracts `monitor_sound` and `unified_monitor_preserves` for the instruction sequence generated from $h$ to obtain preservation of VM typing obligations at runtime transitions for that handler fragment. Compose with the configuration-equivalence/effect-bisimulation bridge to transfer this local typing fact to the observational interface used in Section 8. Hence VM obligations generated from $h$ are satisfied. ∎

Scope note on coinduction: in this architecture, coinductive runtime theorems are used for extensional observer-level equivalence and quotient compatibility (for example `effectBisim_implies_observationalEquivalence` and `configEquiv_iff_effectBisim_silent`). Finite-step preservation internals remain in the inductive Coherence/`Consume` stack of Sections 4-6.

Table 6 gives bridge intent.

| Bridge item             | Role                        |
|-------------------------|-----------------------------|
| choreography obligation | source protocol obligation  |
| effect handler typing   | typed executable obligation |
| VM runtime typing check | enforcement layer           |

The bridge is included to keep the protocol proof layer and executable layer aligned.

**Assumption Block 2. Byzantine Interface Premises.** The interface statements in this section assume shared notation for $H_{\mathrm{byz}}$, $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, and $\mathcal E_{\mathrm{byz}}$, plus theorem-pack capability naming consistency between abstract and runtime layers.

**Theorem BZ-1. Byzantine Interface Well-Formedness.** Under Assumption Block 2, Byzantine safety-track statements in this paper are interpreted on configurations $(G,D)$ satisfying `ByzIfaceWF G D` (definitional alias of `Coherent G D`). For any active edge, this interface yields the same sender-existence and `Consume` obligations as the Coherence layer.

*Proof sketch.* In Lean, `ByzIfaceWF` is definitionally `Coherent`, and theorem `bz1_byzantineInterfaceWellFormedness` extracts the edge-local witness: if receiver lookup is defined on an active edge, then sender lookup exists and `Consume` succeeds on that edge trace. Sections 4-6 provide preservation of the Coherence obligations, and Section 8 provides the observational bridge (`configEquiv_iff_effectBisim_silent`). Therefore the Byzantine symbols are anchored to the same step-preserved active-edge domain. ∎

**Corollary BZ-1.1. Dropped-Assumption Witness Interface.** Let $\mathcal A$ be any assumption class named in $H_{\mathrm{byz}}$. If a later construction provides a witness violating $\mathsf{ByzSafe}$ when $\mathcal A$ is dropped, then that witness can be expressed against the same active-edge Coherence interface used in this paper.

*Proof sketch.* The witness obligation is purely interface-level here: violating traces/configurations are represented in the same configuration language and observation interface fixed above, and local compatibility obligations are phrased with `EdgeCoherent`/`Consume`. No new base semantics is required at this layer. ∎

**Proposition BZ-1.2. Capability-Gated VM Interface.** If a runtime profile includes Byzantine characterization and envelope-adherence capability evidence, then safety-visible runtime obligations are interpreted through $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$ modulo $\mathcal E_{\mathrm{byz}}$, and profile admission is blocked when required evidence is absent.

*Proof sketch.* The profile gate is a conjunction of named capability checks. Section 8 supplies the protocol-to-runtime typing bridge (`EffectSpec.handlerType` plus monitor contracts `monitor_sound` and `unified_monitor_preserves`) and observational quotient compatibility (`effectBisim_implies_observationalEquivalence`, `configEquiv_iff_effectBisim_silent`). Hence interpretation is well-defined when capability checks pass and unavailable otherwise. ∎

## 9. Related Work

Binary duality and global re-derivation lines established important foundations for session safety (Honda et al., 2008). Recent mechanization work highlights brittleness in large MPST proof stacks and motivates reusable proof kernels (Tirore, Bengtson, and Carbone, 2025).

Program-logical lines such as Actris operate at a different verification layer and target program proofs over protocol resources (Hinrichsen et al., 2020). Event-structure and partial-order lines provide alternate macro views of concurrency (Castellan et al., 2023).

Broader background includes process-calculus and communication-structure foundations (Hoare, 1985; Milner, 1999), programming-language typing baselines (Pierce, 2002), and model-checking perspectives on state-space reasoning (Baier and Katoen, 2008).

The main difference from prior work is a single local invariant kernel with a reusable proof split and a monotonic evolution theorem.

Table 7 summarizes the comparison with prior work.

| Prior limitation                                       | Contribution in this paper                        |
|--------------------------------------------------------|---------------------------------------------------|
| preservation tied to repeated global re-derivation     | reusable edge-local preservation skeleton         |
| weak abstraction boundary between theory and execution | explicit effect-typed bridge layer                |
| FIFO-centric semantics in many developments            | one theorem shape under `DeliveryModel` instances |
| fragmented preservation proof structure                | one split kernel plus `Consume` alignment lemmas  |

The first row isolates the primary metatheory difference. The proof kernel is local by construction and avoids per-step global re-derivation.

The second and third rows isolate engineering differences. The effect-typed bridge keeps theorem obligations aligned with runtime typing, and the delivery-model abstraction keeps one theorem shape across FIFO, causal, and lossy variants.

The fourth row isolates proof-architecture reuse. One split kernel plus one alignment kernel supports the preservation family and the evolution theorem.

## 10. Limitations and Scope

This paper proves preservation-style safety only: active-edge coherence is preserved for the core asynchronous rule family, and coherence is stable under subtype replacement when replacement preserves typing domains, satisfies receive-side monotonicity, and keeps unaffected endpoints environment-consistent.

Quantitative, fault-characterization, and envelope-level claims are proved in later papers within this series.

## 11. Conclusion

The paper isolates a reusable preservation kernel for asynchronous buffered MPST. The kernel is active-edge coherence plus `Consume`-based alignment. The same kernel supports subtype-driven session evolution through `Consume_mono`. The result is a mechanized foundation that is small, compositional, and extensible.

## 12. Works Cited

Baier, C., and Katoen, J.-P. (2008). Principles of Model Checking. MIT Press.

Brand, D., and Zafiropulo, P. (1983). On Communicating Finite-State Machines. Journal of the ACM, 30(2), 323-342.

Caires, L., and Pfenning, F. (2010). Session Types as Intuitionistic Linear Propositions. CONCUR 2010.

Castellan, S., et al. (2023). Event-structure and partial-order semantics for session-based concurrency. Journal of Logic and Algebraic Methods in Programming.

Cover, T. M., and Thomas, J. A. (2006). Elements of Information Theory (2nd ed.). Wiley.

Deniélou, P.-M., and Yoshida, N. (2012). Multiparty Session Types Meet Communicating Automata. ESOP 2012.

Gay, S. J., and Hole, M. (2005). Subtyping for Session Types in the Pi Calculus. Acta Informatica, 42(2-3), 191-225.

Girard, J.-Y. (1987). Linear Logic. Theoretical Computer Science, 50(1), 1-101.

Hinrichsen, J., et al. (2020). Actris: Session-type based reasoning in separation logic. POPL 2020.

Hoare, C. A. R. (1985). Communicating Sequential Processes. Prentice Hall.

Honda, K. (1993). Types for Dyadic Interaction. CONCUR 1993.

Honda, K., Vasconcelos, V. T., and Kubo, M. (1998). Language Primitives and Type Discipline for Structured Communication-Based Programming. ESOP 1998.

Honda, K., Yoshida, N., and Carbone, M. (2008). Multiparty Asynchronous Session Types. POPL 2008.

Milner, R. (1999). Communicating and Mobile Systems: The Pi-Calculus. Cambridge University Press.

Milner, R., Parrow, J., and Walker, D. (1992). A Calculus of Mobile Processes, I and II. Information and Computation, 100(1), 1-77.

O'Hearn, P. W. (2007). Resources, Concurrency, and Local Reasoning. Theoretical Computer Science, 375(1-3), 271-307.

Pierce, B. C. (2002). Types and Programming Languages. MIT Press.

Plotkin, G. D. (1981). A Structural Approach to Operational Semantics. DAIMI FN-19.

Reynolds, J. C. (2002). Separation Logic: A Logic for Shared Mutable Data Structures. LICS 2002.

Shannon, C. E. (1948). A Mathematical Theory of Communication. Bell System Technical Journal, 27(3), 379-423 and 27(4), 623-656.

Tirore, L., Bengtson, J., and Carbone, M. (2025). Mechanized MPST metatheory with subject-reduction robustness analysis. ECOOP 2025.

Wadler, P. (2012). Propositions as Sessions. ICFP 2012.

## Appendices

## Appendix A. Syntax and Judgments

This appendix fixes the formal objects and judgment forms used in Sections 2-6.

### A.1 Roles, Endpoints, and Edges

Let `Role` be the finite set of role names. An endpoint is a pair `(sid,r)` of session identifier and role. A directed edge is a triple `(sid, rs, rr)` with sender role `rs` and receiver role `rr`.

We write:

- `src(e)` for the sender endpoint of edge `e`,
- `dst(e)` for the receiver endpoint of edge `e`,
- `role(ep)` for the role component of endpoint `ep`,
- `EdgeShares(e, ep)` when endpoint `ep` is either `src(e)` or `dst(e)`.

### A.2 Local Types and Environments

Local types are generated by:

```text
L ::= end
    | send r T L
    | recv r T L
    | select r {li : Li}i
    | branch r {li : Li}i
    | mu L
```

A typing environment `G` maps endpoints to local types. A delayed-trace environment `D` maps directed edges to buffered type traces.

### A.3 Active Edges and Coherence

An edge is active exactly when both its endpoints are present in `G`:

```text
ActiveEdge G e := (G (src e) != none) and (G (dst e) != none)
```

Edge coherence is a local receive-side compatibility judgment:

```text
EdgeCoherent G D e :=
  exists Lr,
    G (dst e) = some Lr and
    Consume (role (src e)) Lr (D e) != none
```

Global coherence is active-edge quantification:

```text
Coherent G D := forall e, ActiveEdge G e -> EdgeCoherent G D e
```

### A.4 Core Judgment Forms

The proof layer uses the following forms.

1. Typed-step judgment: `(G,D) -> (G',D')`.
2. Preservation premise: `Coherent G D`.
3. Postcondition target: `Coherent G' D'`.
4. Replacement premise family for Section 6:
   - endpoint-domain preservation,
   - receive compatibility,
   - agreement on unaffected endpoints.

The operational fragment is the asynchronous send/recv/select/branch core with side conditions stated in Section 4.

## Appendix B. Deferred Proof of Theorem 1 (Coherence Preservation)

This appendix expands the proof of Theorem 1.

### B.1 Structural Split

**Lemma B.1. Edge Partition.** For any checked edge `e`, updated edge `u`, and endpoint `ep`, exactly one of the following holds:

```text
e = u  or  (e != u and EdgeShares e ep)  or  (e != u and not EdgeShares e ep)
```

*Proof sketch.* Perform classical case analysis on `e = u`. In the negative branch, case-analyze `EdgeShares e ep`. The three resulting branches are disjoint and exhaustive, which is exactly the decomposition implemented by `edge_case_split`. ∎

### B.2 Updated-Edge Obligations

**Lemma B.2. Updated-Edge Preservation.** If `e = u` is the updated edge of a typed core transition, then `EdgeCoherent G' D' e`.

*Proof sketch.* Proceed by inversion on the typed transition rule. For send and select, post-step coherence follows from `Consume_append` together with the rule-local continuation typing judgment. For recv and branch, post-step coherence follows from `Consume_cons` and the corresponding receive-side continuation typing judgment. These are the only updated-edge rule forms, so `EdgeCoherent` holds for the updated edge. ∎

### B.3 Non-Updated Edges

**Lemma B.3. Shared-Endpoint Transport.** If `e != u` and `EdgeShares e ep`, then pre-step `EdgeCoherent G D e` transports to post-step `EdgeCoherent G' D' e`.

*Proof sketch.* Use the shared-endpoint transport lemmas to relate pre-step and post-step projections on the checked edge. The operational rule modifies only the updated edge footprint, so untouched queue segments and unchanged endpoint projections are definitional equalities. Substituting these equalities transports the pre-step `EdgeCoherent` witness to a post-step witness. ∎

**Lemma B.4. Unrelated-Edge Transport.** If `e != u` and `not EdgeShares e ep`, then `EdgeCoherent G D e` iff `EdgeCoherent G' D' e`.

*Proof sketch.* The unrelated-edge premise implies that neither endpoint of `e` is in the transition footprint. By frame-style extensionality, both endpoint projections and delayed traces on `e` are unchanged. Unfolding `EdgeCoherent` on both sides then gives logical equivalence directly. ∎

### B.4 Active-Edge Quantification

**Lemma B.5. Active-Edge Coverage.** Every active post-step edge is covered by one branch of Lemma B.1.

*Proof sketch.* Apply Lemma B.1 to the checked active post-step edge. Its disjunction is exhaustive, and each branch corresponds to one of the three proof obligations used in the preservation proof. Therefore every active post-step edge is covered. ∎

### B.5 Proof of Theorem 1

Fix a typed step `(G,D) -> (G',D')` and assume `Coherent G D`. Let `e` satisfy `ActiveEdge G' e`. By Lemma B.5 and Lemma B.1, split on the three edge classes.

1. `e = u`: use Lemma B.2.
2. shared-endpoint non-updated: use Lemma B.3 and pre-step coherence.
3. unrelated non-updated: use Lemma B.4 and pre-step coherence.

Thus `EdgeCoherent G' D' e` for arbitrary active `e`; therefore `Coherent G' D'`. ∎

## Appendix C. Deferred Proof of Theorem 2 (Replacement via `Consume_mono`)

### C.1 `Consume` Algebra

`Consume` is defined from one-step matcher `consumeOne`:

```text
Consume from L []      = some L
Consume from L (t::ts) =
  match consumeOne from t L with
  | none    => none
  | some L' => Consume from L' ts
```

**Lemma C.1. Consume_append.**
If `Consume from L ts1 = some L1` and `Consume from L1 ts2 = some L2`, then
`Consume from L (ts1 ++ ts2) = some L2`; conversely, any successful concatenated consumption factors through an intermediate `L1`.

*Proof sketch.* Use induction on `ts1`. The base case reduces by simplification of `Consume` on the empty prefix. In the step case, unfold one `consumeOne` step and apply the induction hypothesis to the residual trace. The converse factorization uses the same recursion in reverse to recover the intermediate continuation type `L1`. ∎

**Lemma C.2. Consume_cons.**
`Consume from L (t::ts)` succeeds iff there exists `L1` with `consumeOne from t L = some L1` and `Consume from L1 ts` succeeds.

*Proof sketch.* Unfold `Consume` at one constructor layer. Case-analyze `consumeOne from t L`. In the `none` branch both sides are false. In the `some L1` branch both sides reduce to success of `Consume from L1 ts`, which gives the equivalence. ∎

### C.2 Replacement Premises

For replaced endpoint `ep`, the proof assumes:

1. domain preservation of `G` outside `ep`,
2. receive compatibility (`RecvCompatible`) between old and replacement local types at `ep`,
3. environment agreement on unaffected endpoints.

### C.3 Monotonicity and Lifts

**Proposition C.3 (Edge Lift from `Consume_mono`).**
Under receive compatibility at `ep`, if an affected incoming edge is coherent under `G`, then it is coherent under `G_rep`.

*Proof sketch.* Fix an incoming edge targeting the replaced endpoint and take its pre-replacement `EdgeCoherent` witness. Apply `Consume_mono` under the receive-compatibility premise to transport successful consumption from the original endpoint type to the replacement type. This yields the required post-replacement edge coherence witness. ∎

**Proposition C.4 (Global Lift).**
Under replacement premises, `Coherent G D` implies `Coherent G_rep D`.

*Proof sketch.* Fix an active edge and split on whether its destination is `ep`. If the edge targets `ep`, apply Proposition C.3. If it does not target `ep`, use environment agreement and unchanged delayed traces to transport the original coherence witness. Quantify over active edges to obtain global coherence after replacement. ∎

### C.4 Proof of Theorem 2

Theorem 2 is Proposition C.4 plus preservation of progress-side side conditions from the liveness layer (`progress_conditions_type_replacement`). ∎

## Appendix D. Delivery Parametricity and Runtime Bridge

### D.1 Delivery-Model Law Interface

Preservation is parametric over `ConsumeM` laws. Required laws are:

1. `nil`: consumption over empty trace is identity,
2. `append`: compositionality over trace concatenation,
3. `cons`: one-step decomposition,
4. renaming stability under endpoint-preserving renamings.

FIFO, causal, and lossy instances satisfy this interface and therefore share one preservation theorem shape.

### D.2 Parametric Preservation Statement

**Proposition D.1 (Delivery-Parametric Preservation).**
For any delivery instance satisfying the `ConsumeM` laws, Theorem 1 holds for the corresponding step relation.

*Proof sketch.* Reuse the Appendix B preservation skeleton verbatim. Replace concrete queue equalities with the abstract `ConsumeM` interface laws `nil`, `append`, and `cons`, plus renaming stability. Each branch of the split discharges exactly as in Appendix B under these abstract laws, yielding delivery-parametric preservation. ∎

### D.3 Effect-Typed Runtime Bridge

Runtime obligations are encoded by `EffectSpec.handlerType` and discharged by monitor/adherence checks.

**Proposition D.2 (Bridge Soundness).** If choreography-side obligations hold for handler `h` and `EffectSpec.handlerType` holds for `h`, then generated VM typing obligations for `h` are satisfied.

*Proof sketch.* Use the monitor contracts `monitor_sound` and `unified_monitor_preserves` on the instruction fragment produced by handler `h`. This yields stepwise preservation of runtime typing obligations under `EffectSpec.handlerType`. Compose that result with the configuration-equivalence and effect-bisim bridges to transfer the statement to the protocol-facing observational interface. ∎

**Proposition D.3 (Observation/Quotient Compatibility).**
Effect-bisim and configuration-equivalence bridges preserve compatibility with the protocol-level quotient relation.

*Proof sketch.* Apply `effectBisim_implies_observationalEquivalence` to move from bisimulation to observational equality. Then apply `configEquiv_iff_effectBisim_silent` to identify the quotient relation with the same silent effect-bisim class. Composition yields compatibility between effect and quotient views. ∎

Byzantine-facing statements in Section 8 are interface commitments here: domain alignment and capability contracts, not a Byzantine liveness proof.

## Appendix E. Mechanization Map

| Result family | Primary modules | Representative theorem anchors |
|---------------|------------------|--------------------------------|
| Coherence core and `Consume` | `lean/Protocol/Coherence/Consume.lean`, `lean/Protocol/Coherence/EdgeCoherenceCore.lean` | `Consume`, `EdgeCoherent`, `Coherent` |
| Preservation split and rule cases | `lean/Protocol/Coherence/Unified.lean`, `lean/Protocol/Coherence/Preservation*.lean`, `lean/Protocol/Coherence/SelectPreservation.lean` | `edge_case_split`, `Coherent_send_preserved`, `Coherent_recv_preserved`, `Coherent_select_preserved`, `Coherent_branch_preserved` |
| Delivery-parametric preservation | `lean/Protocol/DeliveryModel.lean`, `lean/Protocol/Coherence/PreservationDeliveryModels.lean` | `FIFODelivery_laws`, `CausalDelivery_laws`, `LossyDelivery_laws` |
| Subtype replacement and liveness lift | `lean/Protocol/Coherence/SubtypeReplacementCore.lean`, `lean/Protocol/Coherence/SubtypeReplacementLiveness.lean` | `Consume_mono`, `EdgeCoherent_type_replacement`, `Coherent_type_replacement` |
| Runtime bridge | `lean/Runtime/VM/Runtime/Monitor.lean`, `lean/Runtime/Proofs/EffectBisim/Bridge.lean`, `lean/Runtime/Proofs/EffectBisim/ConfigEquivBridge.lean` | `monitor_sound`, `unified_monitor_preserves`, `configEquiv_iff_effectBisim_silent` |
| Byzantine interface well-formedness | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean` | `ByzIfaceWF`, `bz1_byzantineInterfaceWellFormedness` |

## Appendix F. Reproducibility

Reproduction uses the repository-pinned Lean toolchain and manifest.

1. Build paper modules listed in Appendix E via `lake build`.
2. Run project checks `just escape` and `just verify-protocols`.
3. Confirm theorem anchors in Appendix E resolve in the built environment.

Expected outcome:

The Appendix-E anchor set has no unresolved constants, the Coherence and replacement and bridge modules contain no proof holes, and theorem names remain consistent with the Appendix G index.

## Appendix G. Index of Main Results

| Claim | Main section | Assumption scope | Formal location |
|-------|--------------|------------------|-----------------|
| Theorem 1. Coherence Preservation | Section 4 | Assumption Block 0 + send/recv/select/branch fragment | `Preservation*.lean`, `SelectPreservation.lean`; Appendix B |
| Theorem 2. Session Evolution via `Consume_mono` | Section 6 | Assumption Block 1 replacement compatibility | `SubtypeReplacementCore.lean`, `SubtypeReplacementLiveness.lean`; Appendix C |
| Proposition 1. Bridge Soundness | Section 8 | Assumption Block 0 + discharged choreography obligations | runtime bridge modules; Appendix D |
| Theorem BZ-1. Byzantine Interface Well-Formedness | Section 8 | Assumption Block 2 Byzantine interface premises | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean` (`ByzIfaceWF`, `bz1_byzantineInterfaceWellFormedness`); Appendix D |
| Corollary BZ-1.1. Dropped-Assumption Witness Interface | Section 8 | Assumption Block 2 + witness premise | derived from Theorem BZ-1 interface in Section 8; Appendix D |
| Proposition BZ-1.2. Capability-Gated VM Interface | Section 8 | Assumption Block 2 + capability-gating assumptions | `lean/Runtime/Proofs/TheoremPack/API.lean` (`canOperateUnderByzantineEnvelope`) + Section 8 bridge contracts; Appendix D |
