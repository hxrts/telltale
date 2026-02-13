# Harmony from Coherence in Asynchronous MPST: A Minimal Erasure Invariant for Classical Dynamics

## Abstract

A *Reconfiguration Harmony Theorem* is established for asynchronous MPST: under well-formed `link` and delegation reconfiguration, projection commutes with reconfigured evolution. This gives a proof architecture for dynamic participant sets where topology change is a first-class semantic step.

The invariant kernel is characterized in both directions. Coherence is identified as an erasure characterization on active edges and as the weakest admissible invariant for delegation safety (relative minimality). Safe delegation and composed-system conservation then follow, including quantitative lift of the Computable Dynamics paper's Lyapunov framework with conservation for pure reconfiguration and descent or budget certificates for transition choreographies.

The behavioral boundary is characterized by an exact determinism envelope with soundness, realizability, and maximality. Exchange-normalized determinism with spatial-subtyping monotonicity is established. Observational adequacy links abstract and protocol proofs to VM adherence modulo envelope. All results are mechanized in Lean 4.

## 1. Introduction

Delegation and topology change are a primary failure point in MPST developments (Honda et al., 2008, and Tirore, Bengtson, and Carbone, 2025). Many systems exclude these operations, or admit them operationally without a theorem that connects choreography-level and local-level evolution. This paper addresses that gap with a commutation theorem for reconfiguration, in the broader process-semantic tradition of operational correspondence and mobility (Hoare, 1985; Plotkin, 1981; Milner, Parrow, and Walker, 1992; Milner, 1999).

The central statement is Harmony under reconfiguration:
$$
\mathsf{project}\circ \mathsf{step}_{\mathsf{reconfig}}
\;=\;
\mathsf{localStep}_{\mathsf{reconfig}}\circ \mathsf{project}.
$$

for well-formed `link` and delegation operations with enabled post-reconfiguration steps. The theorem development then proceeds from commutation to characterization and runtime adherence. It establishes erasure characterization of Coherence, safe delegation consequences, and relative minimality over admissible invariants. It then proves composed-system conservation, exact envelope characterization, exchange-normalized determinism with spatial monotonicity, and observational adequacy with VM adherence.

The determinism-envelope layer follows a standard refinement-bound idea. One defines an admissible behavior relation that captures implementation freedom while preserving safety-visible observations. What is new here is an exact characterization for asynchronous MPST reconfiguration with soundness, realizability, and maximality proved in one theorem stack and connected directly to runtime admission and adherence evidence (Abadi and Lamport, 1991; Alpern and Schneider, 1985).

Equivalently, the envelope is a coarse-grained observational equivalence. It is the maximal admissible blur between executions that still preserves certified safety-visible meaning, in the spirit of noninterference and hyperproperty viewpoints (Goguen and Meseguer, 1982; Clarkson and Schneider, 2010).

Sharding correspondence follows a standard simulation view for distributed execution. A split execution should preserve the same safety-visible meaning as a reference execution under explicit compatibility assumptions (Lamport, 1978; Chandy and Lamport, 1985; Lynch, 1996). What is new here is an explicit envelope contract for local and cross-machine sharding profiles that makes the admissible difference class theorem-checkable and capability-gated at the VM bridge.

The envelope layer also admits a rate-distortion style reading. The reference semantics is the source, VM and sharded executions are channels, and admission profiles are distortion constraints on safety-visible observations (Shannon, 1948, and Cover and Thomas, 2006). Maximality then states that no strictly larger distortion class preserves the same certified safety guarantees.

This paper closes the series architecture. *Coherence for Asynchronous Buffered MPST* supplies the invariant kernel. *Computable Dynamics for Asynchronous MPST* supplies bounds and decision procedures. This paper supplies reconfiguration commutation and envelope-level runtime adherence.

Scope is restricted to asynchronous buffered semantics with explicit reconfiguration side conditions, crash-stop fault assumptions where fault claims are stated, and declared envelope-admission profiles. Claims outside those assumptions are not made.

Our contributions are as follows:

1. A reconfiguration commutation theorem that covers both static composition and dynamic delegation.
2. An exact characterization of Coherence by active-edge erasure realizability and a relative-minimality theorem over admissible invariants.
3. A determinism-envelope theory with soundness, realizability, maximality, and exchange and spatial normalization consequences.
4. An abstract-to-VM adequacy bridge that ties profile claims to theorem-pack capability evidence.
5. A Byzantine envelope extension with exact characterization, converse counterexample families, and capability-gated VM adherence.

Figure 1 (commuting square) records the equality
$$
\mathsf{project}(\mathsf{step}_{\mathsf{reconfig}}(C,\rho))
\;=\;
\mathsf{localStep}_{\mathsf{reconfig}}(\mathsf{project}(C),\rho),
\qquad
\rho\in\{\mathsf{link},\mathsf{delegate}\}.
$$

## 2. Setup, Definitions, and Side Conditions

### 2.1 Base Recap

Assume the base model from *Coherence for Asynchronous Buffered MPST* and *Computable Dynamics for Asynchronous MPST*:

- asynchronous buffered steps,
- active-edge Coherence,
- fair scheduling assumptions stated per theorem,
- `DeliveryModel` parametricity,
- crash-stop setting for fault claims.

Table 1 records the model assumptions for exact claims in this paper.

| Assumption                                      | Status                        |
|-------------------------------------------------|-------------------------------|
| asynchronous buffered semantics                 | required                      |
| active-edge Coherence                           | required                      |
| reconfiguration side conditions `DelegationWF`  | required                      |
| fair scheduling profile                         | required where stated         |
| crash-stop fault model                          | required for fault-side claims |

**Assumption Block 0. Core Model Premises.** Core claims in this paper assume asynchronous buffered semantics, active-edge Coherence, reconfiguration side conditions through `DelegationWF`, and the stated fairness profile. Crash-stop premises apply where fault-side claims are stated.

Table 2 fixes shared notation used across all three papers.

| Symbol                                        | Meaning                                         |
|-----------------------------------------------|-------------------------------------------------|
| $H_{\mathrm{byz}}$                            | Byzantine characterization assumption bundle    |
| $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$ | Byzantine safety-visible observation projection |
| $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$  | Byzantine safety-visible observational equality |
| $\mathcal E_{\mathrm{byz}}$                   | Byzantine determinism-envelope relation         |

Table 3 fixes paper-specific notation used in this paper.

| Symbol          | Meaning                                                                                                                                                                |
|-----------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Admissible(I)` | candidate invariant admissibility condition                                                                                     |
| $W$             | weighted state function inherited from *Computable Dynamics for Asynchronous MPST* |
| $\mathcal E$    | determinism envelope relation                                                                                                   |
| `ConfigEquiv`   | erasure-stability equivalence relation                                                                                          |

No aliases are used for shared notation symbols.

### 2.2 Reconfiguration Operators

The paper distinguishes:

- static composition (`link`) in deployment-level composition,
- dynamic delegation (endpoint/capability transfer during execution).

Representative mechanized anchors are in the deployment-composition layer, the delegation-preservation layer, and the higher-order graph-delta layer. Appendix D provides the file-level mapping.

### 2.3 Dynamic Participant Sets

Participant sets are not fixed:

- joining through delegation,
- leaving through crash-stop or transfer-and-exit,
- topology change through composition.

The objective is to preserve Coherence/Harmony across these mutations.

### 2.4 Core Definitions

Write `envG(C)` and `envD(C)` for the global and delayed-trace environments extracted from configuration `C`, and `Obs` for the safety-visible observation map.

**Definition. Lifted Coherence.**
$$
\mathsf{Coherent}(C)\ :=\ \mathsf{Coherent}(\mathsf{envG}(C),\mathsf{envD}(C)).
$$

**Definition. Harmony.** For reconfiguration operator $\rho$,
$$
\mathsf{Harmony}(C,\rho)\ :\iff\ \mathsf{project}(\mathsf{step}_{\mathsf{reconfig}}(C,\rho))
=
\mathsf{localStep}_{\mathsf{reconfig}}(\mathsf{project}(C),\rho).
$$

**Definition. Joint Realizability on Active Edges.** `JointRealizable_active(project(C))` holds when projected local views admit witnesses for all active edges.

**Definition. Reconfiguration Well-Formedness.** Write $WF_\rho(C)$ for the side-condition predicate used by reconfiguration theorems: `LinkWF(C,\rho)` for static linking, `DelegationWF(C,\rho)` for delegation, and `TransitionWF(C,\rho)` for transition choreographies.

**Definition. Delegation Safety Predicates.**
`SafeDelegation(C,op)` is the global delegation-safety judgment, and
`SafeDelegationFootprint(C,op)` is its footprint-local form over edges touched by `op`.

**Definition. `Admissible(I)`.** Locality plus erasure stability (`ConfigEquiv`) plus frame stability plus delegation adequacy.

**Definition. Envelope Predicates.**
`EnvelopeRel(S_vm,S_ref)` is the envelope relation between VM and reference states.
`EnvelopeExact(C)` is exactness of the declared envelope (soundness and realizability and maximality) at configuration `C`.
`EnvelopeOK(C)` means `C` satisfies the envelope-admission obligations used in Theorems F-G.

**Definition. Capability/Adherence Predicates.**
`HasProfileCapabilities(P,\Pi)` means profile `(P,\Pi)` is backed by required theorem-pack capability evidence.
`VMAdheres(P,\Pi)` means executions admitted under `(P,\Pi)` satisfy the corresponding adherence obligations.

**Definition. Normalization Relations.**
`ExchangeEq(C_1,C_2)` is exchange equivalence modulo admissible reordering.
`C \sqsubseteq_{\mathsf{sp}} C'` is the spatial-subtyping preorder used in Theorem G.

Figure 2 (delegation footprint) states the update discipline: only footprint edges of the delegation endpoint are rewritten; session-disjoint and unrelated edges are preserved by frame transport.

## 3. Worked Example

We use one running example that carries all theorems B-H.

**Running Example 3.1 (Federated Capacity Pool with Delegation).**
Baseline choreography:

```text
C -> P : Request(n)
P -> C : Grant(k)
C -> M : Report(k)
M -> P : Confirm
P -> C : Token(t)
```

Extended system adds:
`link` federation (`P1`,`P2`), delegation `C -> C'`, and optimistic-to-coordinated transition choreography.

Fix configurations and reconfiguration operators:
$$
C_0 \xrightarrow{\rho_{\mathsf{link}}} C_1 \xrightarrow{\rho_{\mathsf{del}}} C_2 \xrightarrow{\rho_{\mathsf{tr}}} C_3.
$$
Assume well-formedness judgments `\Gamma \vdash C_i\ \mathsf{wf}` for `i=0,1,2,3`.

- `C_0`: coherent single-pool state before federation.
- `C_1`: linked/federated state.
- `C_2`: post-delegation state where token capability is held by `C'`.
- `C_3`: coordinated-mode state after transition choreography.

The running obligations are used through these derived rule instances.

$$
\dfrac{
  \Gamma \vdash C_0\ \mathsf{wf}
  \quad
  \mathsf{WF}_{\rho_{\mathsf{link}}}(C_0)
}{
  \mathsf{project}(\mathsf{step}_{\mathsf{reconfig}}(C_0,\rho_{\mathsf{link}}))
  =
  \mathsf{localStep}_{\mathsf{reconfig}}(\mathsf{project}(C_0),\rho_{\mathsf{link}})
}
\;(\textsc{Ex-LinkHarmony})
$$

$$
\dfrac{
  \mathsf{Coherent}(C_1)
  \quad
  \mathsf{DelegationWF}(C_1,\rho_{\mathsf{del}})
}{
  \mathsf{SafeDelegation}(C_1,\rho_{\mathsf{del}})
  \quad\land\quad
  \mathsf{SafeDelegationFootprint}(C_1,\rho_{\mathsf{del}})
}
\;(\textsc{Ex-DelegSafety})
$$

$$
\dfrac{
  \mathsf{WF}_{\rho_{\mathsf{link}}}(C_0)
  \quad
  \mathsf{Coherent}(C_0)
}{
  W(C_1)=W(C_0)
}
\;(\textsc{Ex-Conserve})
$$

$$
\dfrac{
  \mathsf{WF}_{\rho_{\mathsf{tr}}}(C_2)
  \quad
  \mathsf{Coherent}(C_2)
  \quad
  \text{transition-profile premises}
}{
  C_2 \to^\ast C_3
  \quad\land\quad
  \text{budget-certified descent}
}
\;(\textsc{Ex-Transition})
$$

$$
\dfrac{
  \mathsf{EnvelopeRel}(S_{\mathsf{vm}}(C_3),S_{\mathsf{ref}}(C_3))
  \quad
  \mathsf{HasProfileCapabilities}(P,\Pi)
}{
  \mathsf{Obs}(S_{\mathsf{vm}}(C_3))=\mathsf{Obs}(S_{\mathsf{ref}}(C_3))
  \quad\land\quad
  \mathsf{VMAdheres}(P,\Pi)
}
\;(\textsc{Ex-AdequacyAdherence})
$$

Table 4 gives the typed guard clauses used to discharge $WF_{\rho_{\mathsf{tr}}}$ for the optimistic-to-coordinated step.

| Guard clause                     | Static source                                                                                                                                               | Consequence                               |
|----------------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------|
| `conflict_detected`              | application-level trigger                                                                                                                                  | transition path enabled                   |
| `reachable(Coord)`               | crash-tolerance decider from *Computable Dynamics for Asynchronous MPST* | coordination path not disconnected        |
| $W \leq \text{transitionBudget}$ | quantitative bound from *Computable Dynamics for Asynchronous MPST*      | transition completes within budget        |
| $|F| \leq f$                     | fault-budget declaration                                                                                                                                   | bounded crash tolerance during transition |

Concrete reading: `C_0` pre-federation, `C_1` linked, `C_2` post-delegation handoff, `C_3` coordinated mode with preserved envelope obligations.

## 4. Theorem B: Reconfiguration Harmony (Static + Dynamic)

**Assumption Block A. Reconfiguration Well-Formedness Premises.** The reconfiguration theorems assume typed global and local states, reconfiguration witnesses satisfying `DelegationWF`, enabled post-reconfiguration steps, and compatibility side conditions for unaffected edges.

**Theorem B. Reconfiguration Harmony.**
For all configurations $C$ and reconfiguration operators $\rho \in \{\mathsf{link}, \mathsf{delegate}\}$, if Assumption Block A holds for $(C,\rho)$, then
$$
\mathsf{project}(\mathsf{step}_{\mathsf{reconfig}}(C,\rho))
=
\mathsf{localStep}_{\mathsf{reconfig}}(\mathsf{project}(C),\rho).
$$
Equivalently, the reconfiguration square commutes at the projection boundary.

The proof has two components.

1. Static Harmony via `link`. Composition-level commutation and coherence preservation are established in deployment theorems, for example `link_harmony_through_link` and `link_preserves_coherent`.
2. Dynamic Harmony via delegation. Delegation preservation and renaming and footprint lemmas establish commutation for topology-changing transfers.

At the effect-observation boundary, the coinductive bridge supplies the composition-facing congruence and quotient lift used by this section: `effectBisim_congr_link` and `configEquiv_iff_effectBisim_silent`.

Side-condition necessity is explicit. Dropped-condition counterexample interfaces are part of the reconfiguration bridge layer.

*Proof sketch.* The theorem is proved by decomposition over reconfiguration operators.

1. `link` case:
   - construct composed deployment object under link well-formedness,
   - apply composition-preservation and harmony lemmas (`link_preserves_coherent`, `link_harmony_through_link`),
   - transport equality to projected local-step view.
2. `delegate` case:
   - apply delegation-preservation and footprint-local update lemmas,
   - show only footprint edges are rewritten; unrelated edges are frame-preserved,
   - commute projection with the delegated local transition.
3. Quotient/effect boundary:
   - use effect-bisim congruence under link and quotient bridge (`effectBisim_congr_link`, `configEquiv_iff_effectBisim_silent`) to align protocol and observational views.

Hence reconfigured global evolution and projected local evolution commute under Assumption Block A. ∎

Figure 3 separates the two commutation instances:
$$
\mathsf{project}(\mathsf{linkStep}(C))
\;=\;
\mathsf{localLinkStep}(\mathsf{project}(C)),
\qquad
\mathsf{project}(\mathsf{delegateStep}(C))
\;=\;
\mathsf{localDelegateStep}(\mathsf{project}(C)).
$$

## 5. Theorem A: Erasure Characterization of Coherence

**Theorem A. Erasure Characterization of Coherence.**
For all configurations $C$ with global and delayed environments $(G,D)$,
$$
\mathsf{Coherent}(G,D)
\iff
\mathsf{JointRealizable}_{\mathsf{active}}(\mathsf{project}(C)).
$$
That is, Coherence holds exactly when projected local views admit a compatible active-edge witness assignment.

Mechanized anchors include `coherent_erasure_stable` and its companion characterization lemmas.

This theorem gives the formal content of the quotient-first claim: erasure is not a heuristic post-processing step but the semantic object preserved by the theorem stack.

*Proof sketch.* The two directions are proved separately.

1. `Coherent -> JointRealizable_active`:
   - from edge-local compatibility (`EdgeCoherent`) build per-edge witnesses for projected local obligations,
   - combine witnesses over active edges to obtain joint realizability.
2. `JointRealizable_active -> Coherent`:
   - invert witness assignment into edge-local consume compatibility,
   - reassemble edge obligations into global `Coherent`.
3. Erasure stability:
   - use `coherent_erasure_stable` to show equivalence is preserved across configuration erasure classes.

Therefore Coherence is exactly characterized by active-edge realizability of projected views. ∎

## 6. Theorem C: Safe Delegation Corollary

**Theorem C. Safe Delegation Sufficiency.**
For all configurations $C$ and delegation operations $op$,
$$
\mathsf{Coherent}(C) \land \mathsf{DelegationWF}(C,op)
\implies
\mathsf{SafeDelegation}(C,op).
$$

**Corollary C.1. Footprint Exactness Packaging.**
For all $C,op$ satisfying the stated step and well-formedness side conditions,
$$
\mathsf{SafeDelegation}(C,op)
\iff
\mathsf{SafeDelegationFootprint}(C,op).
$$
The converse direction is accompanied by strictness witnesses for dropped side conditions.

Mechanized anchors:

- `safeDelegation_local_necessity`
- `safeDelegation_to_footprint`
- `footprint_to_safeDelegation`
- `safeDelegation_iff_footprint`

These lemmas are grouped in the erasure-characterization layer.

*Proof sketch.* Sufficiency follows by composing:

1. Coherence on active edges,
2. delegation well-formedness side conditions (`DelegationWF`),
3. delegation-preservation lemmas that update only the delegation footprint.

Together these imply safe delegation without introducing additional global invariants. ∎

*Proof sketch.* For the forward direction, instantiate Theorem C and project its obligations to the declared delegation footprint. For the reverse direction, apply `footprint_to_safeDelegation` to reconstruct global safety from footprint obligations, then use strictness witnesses to show necessity of the side conditions. Combining both implications yields the stated equivalence. ∎

## 7. Theorem D: Relative Minimality

**Theorem D. Relative Minimality.**
For all invariants $I$,
$$
\mathsf{Admissible}(I)
\implies
\forall C, I(C) \implies \mathsf{Coherent}(C).
$$
Hence Coherence is the weakest admissible invariant that guarantees delegation safety under the stated model side conditions.

Mechanized anchors:

- `relative_minimality`
- supporting witness and counterexample lemmas in the minimality layer

This theorem prevents "stronger-than-needed" invariant inflation and pins down the architectural core.

*Proof sketch.* Assume any invariant `I` satisfying `Admissible(I)`.

1. Use admissibility clauses (locality, erasure stability, frame stability, delegation adequacy) to transport `I` along the same edge-local transformations used by Coherence.
2. Apply delegation-safety adequacy to derive local safety obligations on all active edges.
3. Convert these obligations into Coherence via erasure-characterization lemmas.

Hence every admissible safety-guaranteeing invariant implies Coherence, making Coherence relatively minimal. ∎

Figure 4 (admissible-invariant order) is summarized by Theorem D:
for every admissible invariant $I$, one has $I \Rightarrow \mathsf{Coherent}$.

## 8. Theorem E: Composed-System Conservation

**Theorem E. Composed-System Conservation.**
For all configurations $C$ and reconfiguration operators $\rho$, if $\mathsf{WF}_\rho(C)$ and $\mathsf{Coherent}(C)$ hold, then
$$
\mathsf{Coherent}(\mathsf{step}_{\mathsf{reconfig}}(C,\rho)).
$$
For all configurations $C$ and pure reconfiguration operators $\rho$,
$$
\mathsf{WF}_\rho(C) \land \mathsf{Coherent}(C)
\implies
W(\mathsf{step}_{\mathsf{reconfig}}(C,\rho)) = W(C).
$$
For transition choreographies $\rho_{\mathrm{tr}}$ with stated budget and scheduler premises, descent and budget certificates are preserved with conservative profile-dependent bounds.

The theorem separates conservation and dissipation roles. Pure reconfiguration preserves the weighted quantity exactly. Transition choreographies consume certified progress budget and are therefore dissipative with explicit bounds. This split keeps structural rewiring distinct from progress-consuming work.

Under composition and delegation:

1. Coherence and Harmony are preserved.
2. Quantitative lift from *Computable Dynamics for Asynchronous MPST* holds:
   - pure reconfiguration conserves the weighted measure,
   - transition choreographies are governed by descent and budget certificates.

Mechanized anchors:

- `flagship_composed_system_conservation`
- `lyapunov_conserved_under_balanced_delegation`

This theorem combines composition, delegation, and quantitative invariants in one package.

*Proof sketch.* Split reconfiguration into conservative and budgeted classes.

1. Pure reconfiguration (`link`/delegation):
   - preserve Coherence/Harmony by Theorem B-side machinery,
   - show weighted measure `W` is invariant under balanced delegation/rewiring (`lyapunov_conserved_under_balanced_delegation`).
2. Transition choreographies:
   - apply inherited quantitative descent/budget certificates from the dynamics layer,
   - conclude bounded dissipation under declared scheduler premises.
3. Compose both cases to obtain theorem statement and conservative profile-dependent quantitative side.

∎

**Corollary S2. Compositional Exactness Under Non-Interference.** For all compositions $C_1 \otimes C_2$, if non-interference premises hold across the composition boundary, then envelope exactness is preserved by composition:
$$
\mathsf{EnvelopeExact}(C_1) \land \mathsf{EnvelopeExact}(C_2)
\implies
\mathsf{EnvelopeExact}(C_1 \otimes C_2).
$$
Strictness witnesses are provided for dropped non-interference premises.

*Proof sketch.* Non-interference gives a factorization of composed traces into component traces with no cross-boundary interference steps. Apply envelope exactness to each component and recompose to obtain exactness of the composition. For strictness, use the dropped-assumption witness family to exhibit an interfering trace that violates factorization and therefore exactness. ∎

Figure 5 summarizes the quantitative split:
pure reconfiguration preserves $W$, while transition choreographies satisfy the inherited descent/budget inequality under stated profile assumptions.

## 9. Theorem F: Exact Characterization of Determinism Envelope

**Assumption Block B. Envelope Admissibility Premises.** Envelope theorems assume the declared admissibility profile with trace well-formedness, certified-step obligations, and the realizability witness schema used by the admission checker.

**Theorem F. Exact Determinism Envelope.**
Under Assumption Block B, there exists an envelope relation $\mathcal E$ such that:
1. Soundness: $\forall t, \mathsf{Certified}(t) \implies t \in \mathcal E$.
2. Realizability: $\forall t \in \mathcal E, \exists e, \mathsf{Trace}(e)=t$.
3. Maximality: $\forall \mathcal E'$, if $\mathcal E' \supsetneq \mathcal E$, then $\exists t \in \mathcal E' \setminus \mathcal E$ that violates admissibility constraints.

The envelope claim is exact under the stated model and assumption bundle:

1. soundness: certified executions lie within the envelope.
2. realizability and completeness: admitted envelope behaviors are witnessed.
3. maximality: strict supersets are rejected by witness counterexamples.

Conceptually, this is dual to Theorem D:

- D: weakest admissible invariant core,
- F: maximal admissible behavior envelope.

Mechanized envelope bridge layers include core foundations, admission logic, and reconfiguration bridge components.

*Proof sketch.* Exactness is obtained by packaging three envelope properties.

1. Soundness:
   - derive `Certified -> Envelope` from local/sharded envelope soundness definitions and profile extraction.
2. Realizability/completeness:
   - use realizability witness schemas to construct executions for admitted envelope behaviors.
3. Maximality:
   - show any strict envelope extension violates admissibility via explicit witness obligations.

Core formal structures come from envelope foundations (`LocalExactEnvelopeCharacterization`, `ShardedExactEnvelopeCharacterization`) and profile-level extraction theorems (`consensusEnvelope_exact_of_profile`, `failureEnvelope_maximality_of_profile`). ∎

**Corollary F.1. Finite-Erasure Transportability Boundary.** Under stated model assumptions,
$$
\forall t,\ \mathsf{FiniteErasureTransportable}(t) \iff \mathsf{RationalFiniteState}(t).
$$

*Proof sketch.* Apply the forward transport bridge to map each rational finite-state witness to a finite erasure-transport witness. Apply the converse boundary lemmas to map each finite erasure-transport witness back to a rational witness. The two implications give the required equivalence. ∎

**Corollary F.2. Strict Boundary Witness.** There exists $t$ such that
$$
\neg \mathsf{RationalFiniteState}(t) \land \neg \mathsf{FiniteErasureTransportable}(t).
$$

*Proof sketch.* Invoke `strict_boundary_witness_effect` to obtain a concrete trace outside the rational transportable fragment. By construction, the witness violates both `\mathsf{RationalFiniteState}` and `\mathsf{FiniteErasureTransportable}`. This gives the strict boundary instance. ∎

**Corollary F.3. Inductive-Embedding Exactness.** For all inductive states $x$, exact envelope characterization is preserved under `toCoind`:
$$
\mathsf{EnvelopeExact}_{\mathrm{ind}}(x)
\iff
\mathsf{EnvelopeExact}_{\mathrm{coind}}(\mathsf{toCoind}(x)).
$$

*Proof sketch.* Apply the coinductive-to-inductive bridge to transfer envelope exactness from `toCoind x` to `x`. Apply the inverse bridge under the same compatibility premises for the converse implication. Since envelope predicates are preserved by both directions of the embedding interface, equivalence follows. ∎

Appendix A and Appendix C provide the detailed witness constructions and transport lemmas for these boundary corollaries.

## 10. Theorem G: Exchange-Normalized Determinism and Spatial Monotonicity

**Theorem G. Exchange-Normalized Determinism and Spatial Monotonicity.**
For all configurations under envelope premises, the following properties hold:
1. Exchange normalization:
$$
\mathsf{ExchangeEq}(C_1,C_2) \implies \mathsf{Obs}(C_1)=\mathsf{Obs}(C_2).
$$
2. Spatial monotonicity:
$$
C \sqsubseteq_{\mathsf{sp}} C' \land \mathsf{EnvelopeOK}(C)
\implies
\mathsf{EnvelopeOK}(C').
$$

Theorem G combines two normalization properties.

1. Exchange normalization: admissible reorderings collapse to equivalent safety-visible outcomes.
2. Spatial monotonicity: envelope and safety obligations are preserved under admissible spatial refinement.

This is a symmetry-reduction statement. Different concrete traces can represent the same observable behavior class once exchange symmetries are quotiented. The theorem makes that collapse explicit and checkable at the envelope layer.

Mechanized anchors in the bridge layer include:

- `exchangeNormalization_of_e1BridgePremises`
- `spatialSubtypingMonotonicity_of_e1BridgePremises`

This theorem sharpens what "determinism modulo envelope" means operationally.

*Proof sketch.* Instantiate reconfiguration-bridge theorem forms with exchange and spatial premises.

1. Exchange normalization follows from bridge theorem `exchangeNormalization_of_e1BridgePremises`.
2. Spatial monotonicity follows from `spatialSubtypingMonotonicity_of_e1BridgePremises`.
3. Combine both to obtain determinism modulo envelope classes rather than raw traces.

∎

## 11. Theorem H: Observational Adequacy and VM Adherence Modulo Envelope

**Assumption Block C. Adequacy Bridge Premises.** Adequacy and adherence theorems assume envelope-related VM and reference states, trace-consistency premises for observable events, and profile extraction rules for capability reports.

**Theorem H. Observational Adequacy and VM Adherence Modulo Envelope.**
1. (Adequacy) For all VM/reference states $S_{\mathsf{vm}},S_{\mathsf{ref}}$, if the state-side premises of Assumption Block C hold and
$$
\mathsf{EnvelopeRel}(S_{\mathsf{vm}}, S_{\mathsf{ref}}),
$$
then
$$
\mathsf{Obs}(S_{\mathsf{vm}})=\mathsf{Obs}(S_{\mathsf{ref}}).
$$
2. (Adherence) For all profiles $(P,\Pi)$, if the profile-side premises of Assumption Block C hold and
$$
\mathsf{HasProfileCapabilities}(P,\Pi),
$$
then
$$
\mathsf{VMAdheres}(P,\Pi).
$$
Local and sharded variants are recovered as profile-specific instances under explicit collapse assumptions.

**Proposition 1. Capability-Bit Soundness.** For all runtime profiles $q$ and capability bits $b$, if $q$ advertises $b$, then there exists a corresponding theorem-pack object $a_b$ such that $a_b$ satisfies the same envelope-premise profile used by Theorem H.

Mechanized anchors:

- adequacy theorem layer, including `vm_adequacy_of_trace_consistency`
- VM adherence and admission layers
- profile extraction to theorem packs and distributed adapters

Coinductive adequacy bridge pack used here: `protocolOutcome_effectBisim_of_observationalEq`, `compile_refines_observationalEq_of_effectBisim`, `vmView_effectBisim_of_VMCEquiv`, `vmCEquiv_of_vmView_effectBisim`, and `topology_change_preserves_VMCEquiv_via_effectBisim`.

Runtime consequence: proof-carrying conformance between claimed profile bits and available theorem-pack evidence.

*Proof sketch.* By definition of capability extraction, each advertised bit is accepted only if the corresponding theorem-pack entry is present and typechecks against the same profile premises used by admission. Soundness of profile extraction then yields a witness object $a_b$ for each advertised bit. Therefore advertised capabilities are justified by theorem-pack evidence under the Theorem H premise profile. ∎

*Proof sketch.* The adequacy/adherence statement is obtained by composition of three bridges.

1. Protocol outcome bridge:
   - connect observational equality and effect-bisim (`protocolOutcome_effectBisim_of_observationalEq`).
2. Compile/runtime refinement bridge:
   - lift effect-bisim to compile-time observational refinement (`compile_refines_observationalEq_of_effectBisim`).
3. VM view bridge:
   - connect VM configuration equivalence and effect-bisim (`vmView_effectBisim_of_VMCEquiv`, converse, and topology-preservation lemmas).

Adequacy follows from trace-consistency theorem (`vm_adequacy_of_trace_consistency`). Adherence follows from profile-capability extraction and theorem-pack gating. ∎

**Corollary S1. Principal Capability and Admission Completeness.** Let $D_{\text{user}}$ be a requested envelope capability and let $D_{\text{prog}}$ be inferred from program and deployment profile. Under the admission premises,
$$
D_{\text{user}} \subseteq D_{\text{prog}} \subseteq \mathcal E
$$
and admission is complete with a principal inferred capability.

*Proof sketch.* Use principal-capability extraction to obtain the canonical inferred capability set from program and deployment profile. Admission soundness gives inclusion of admitted capabilities in the global envelope. Admission completeness gives that all admissible requested capabilities are included in the inferred principal set. These three facts yield the stated chain and completeness claim. ∎

**Assumption Block D. Byzantine Characterization Premises.** Byzantine characterization assumes explicit bundle $H_{\mathrm{byz}}$ with fault-model, authentication and evidence-validity, conflict-exclusion primitive consistency, and adversarial-budget side conditions.

Define
$$
\mathsf{ByzChar}
\;:=\;
\mathsf{ByzQuorumOK}\ \land\ \mathsf{ByzAuthEvidenceOK}\ \land\ \mathsf{ByzBudgetOK}\ \land\ \mathsf{ByzPrimitiveConsistent},
$$
where each conjunct names the corresponding requirement class in Assumption Block D.

**Theorem BZ. Exact Byzantine Safety Characterization.** Under Assumption Block D, profile extraction yields an exact-characterization package for the declared Byzantine model. At this paper interface, the package gives
$$
\mathsf{ByzChar} \Rightarrow \mathsf{ByzSafe},
\qquad
\mathsf{ByzSafe} \Rightarrow \mathsf{ByzChar},
$$
with relative maximality for the same characterization relation.

*Proof sketch.* Instantiate the Byzantine profile package under Assumption Block D and apply `byzantineSafety_exact_of_profile` to obtain `ExactByzantineSafetyCharacterization` for the profile model. Project soundness, completeness, and maximality from that package, and interpret soundness/completeness through the same safety-visible envelope observation interface used in Theorem H. This yields the stated exact interface characterization for the declared Byzantine profile. ∎

**Corollary BZ.1. Converse Counterexample Families.** If any required class in Assumption Block D is dropped, there exists a counterexample family violating $\mathsf{ByzSafe}$. Covered dropped classes are quorum or intersection obligations, authentication or evidence-validity obligations, adversarial-budget obligations, and primitive-consistency obligations.

*Proof sketch.* Fix a dropped assumption class from Assumption Block D and run profile extraction. The corresponding profile obligation fails, and the converse-sharpness interface returns a violation family for that class. Repeating this argument classwise gives the full converse counterexample family statement. ∎

**Proposition BZ.2. Byzantine VM Adherence and Admission Gating.** For runtime profile $(P,\Pi)$, if theorem-pack capability bits include Byzantine safety characterization and VM envelope adherence evidence, then admitted executions satisfy $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$ modulo $\mathcal E_{\mathrm{byz}}$ and rejected requests correspond to failed assumptions or missing evidence.

*Proof sketch.* Apply `vmByzantineEnvelopeAdherence_of_witness` to obtain adherence for admitted executions under supplied witness evidence. Combine this with `byzantineCrossTargetConformance_of_witnesses` to transfer the result across declared targets. Admission-gate theorems then separate positive conformance from rejected requests and certify that rejection corresponds to missing or failed prerequisites. ∎

## 12. Supporting Formal Layer

Three support packages make the main theorem stack executable and compositional.

1. Higher-order extension: channel-carrying payloads and graph-delta semantics.
2. Conservative extension: collapse back to first-order when no channel payloads are present.
3. Delegation-preservation microkernel: redirected, unrelated, and other-session edge coherence lemmas.

Concrete module anchors for these packages:

1. Higher-order/graph-delta semantics:
   - `lean/Protocol/Coherence/GraphDelta.lean`,
   - `lean/Protocol/Coherence/GraphDeltaHO.lean`.
2. First-order collapse and equivalence/renaming support:
   - `lean/Protocol/Coherence/ConfigEquiv.lean`,
   - `lean/Protocol/Coherence/ConfigEquivRenaming/*.lean`,
   - `lean/Protocol/Coherence/RoleSwap/*.lean`.
3. Delegation microkernel:
   - `lean/Protocol/Coherence/Delegation/Core/*.lean`,
   - `lean/Protocol/Coherence/Delegation/Preservation.lean`.

## 13. Worked Transport in Main Body

This section formalizes two transport instances from the generic schema in Appendix B.

**Assumption Block E. Transport Interface Premises.**
For each target claim, assume:
1. the structural theorem interface required by Theorems B-H at the relevant profile,
2. an external analytic package for the target claim,
3. interface compatibility between structural observables and analytic variables.

Fix the source execution family to the running-example transition slice from Section 3:
$$
C_2 \xrightarrow{\rho_{\mathsf{tr}}} C_3 \xrightarrow{} \cdots
$$
and let transported observables be computed from the safety-visible projection `Obs`.

**Theorem T1. Tail-Bound Transport.**
Let `T_comp` be completion time for the declared execution family and let `TailPkg(theta)` be an analytic package that yields a tail function `Psi_tail(.,theta)` for the transported observable. Under Assumption Block E and `TailPkg(theta)`,
$$
\forall t \ge 0,\ \Pr\!\big[T_{\mathrm{comp}}-\mathbb E[T_{\mathrm{comp}}]\ge t\big]\ \le\ \Psi_{\mathrm{tail}}(t;\theta).
$$
The bound is exact with respect to the imported analytic package and does not strengthen structural premises.

*Proof sketch.* Instantiate Appendix B.1 with target claim equal to the tail bound. Theorems B-H discharge the structural side of the transport interface, and `TailPkg(theta)` discharges the analytic inequality. Compatibility of observables identifies the transported random variable on both interfaces. Composition yields the stated tail inequality. ∎

**Instantiation 13.1 (Running Example Tail Witness).**
$$
\dfrac{
  C_2 \to^\ast C_3
  \quad
  \text{Section 3 guard obligations}
  \quad
  \text{Assumption Block E}
  \quad
  \text{TailPkg}(\theta)
}{
  \forall t\ge 0,\ \Pr[T_{\mathrm{comp}}-\mathbb E[T_{\mathrm{comp}}]\ge t]
  \le \Psi_{\mathrm{tail}}(t;\theta)
}
\;(\textsc{Ex-TransportTail})
$$

**Theorem T2. Mixing-Rate Transport.**
Let `mu_n` be the transported observable distribution at step `n`, `mu_*` its reference limit, and `MixPkg(eta)` an analytic package with rate function `Psi_mix(.,eta)`. Under Assumption Block E and `MixPkg(eta)`,
$$
\forall n \ge 0,\ \|\mu_n-\mu_*\|_{\mathrm{TV}}\ \le\ \Psi_{\mathrm{mix}}(n;\eta).
$$
Again, the conclusion imports analytic constants/rates without adding new semantic assumptions to the theorem stack.

*Proof sketch.* Apply Appendix B.1 with target claim equal to the mixing bound. Structural premises are identical to Theorem T1 and are discharged by the same theorem stack. `MixPkg(eta)` supplies the analytic contraction estimate, and interface compatibility maps the transported process to the analytic state space. The resulting inequality is exactly the stated total-variation bound. ∎

**Instantiation 13.2 (Running Example Mixing Witness).**
$$
\dfrac{
  \mu_n\ \text{from safety-visible outcomes after }n\text{ steps from }C_3
  \quad
  \text{Assumption Block E}
  \quad
  \text{MixPkg}(\eta)
}{
  \forall n\ge 0,\ \|\mu_n-\mu_\ast\|_{\mathrm{TV}}
  \le \Psi_{\mathrm{mix}}(n;\eta)
}
\;(\textsc{Ex-TransportMix})
$$

## 14. Discussion: The Classical Boundary

This section is interpretive and does not add theorem premises. Theorems A through H remain valid without this interpretation. The discussion explains why the proof architecture has its current shape. It also explains where the current model intentionally stops.

The formal layer establishes exchangeability through delegation-compatible symmetries, local compatibility through active-edge Coherence, and well-posed quotient dynamics through Harmony and envelope laws. These results define an erasure-safe regime for the model class in this paper. Within that regime, safety-visible behavior is invariant under the declared symmetries. This is the precise sense in which identity details are treated as gauge.

The boundary claim is exact for the stated assumptions. Safe erasures are exactly those justified by Coherence-preserving symmetries and envelope admissibility laws. Behaviors that depend on non-erasable state update mechanisms require a different semantic model. Examples include measurement backaction and entanglement-sensitive observables.

This interpretation is consistent with established coherence and session-typing lines in Girard (1987), Caires and Pfenning (2010), and Wadler (2012). The paper does not claim model identity with those frameworks. It claims an operational correspondence at the level of compatibility structure. That correspondence is sufficient for the theorem program in this manuscript.

## 15. Related Work

Work on reconfiguration and delegation established important safety baselines for dynamic session topologies. These lines often prove preservation-style properties for specific operators. They usually do not package commutation, minimality, and exact envelope bounds in one theorem stack. This paper targets that combined package.

Mechanized MPST developments established high-confidence metatheory and exposed proof fragility under richer operational features. The robustness analysis in Tirore, Bengtson, and Carbone (2025) is especially relevant to this pressure point. The present work responds by factoring the development into reusable assumption blocks and bridge theorems. This choice reduces repetition across reconfiguration, exactness, and adequacy layers.

Session foundations from Honda et al. (2008) and logical correspondences from Caires and Pfenning (2010) and Wadler (2012) remain the base for local and global consistency claims. Program-logical lines such as Hinrichsen et al. (2020) provide strong local reasoning for implementations. Event-structure and partial-order models such as Castellan et al. (2023) provide alternate macro semantics for concurrency. This paper works at the semantic-commutation layer and connects that layer to runtime adherence evidence.

Our refinement and adequacy framing is also consistent with classical correspondence and distributed-system baselines (Abadi and Lamport, 1991; Lamport, 1978; Chandy and Lamport, 1985), while Byzantine-facing interfaces inherit the standard adversarial formulation lineage (Lamport, Shostak, and Pease, 1982).

The main difference of this paper is theorem-level integration of reconfiguration Harmony, relative minimality, exact determinism-envelope characterization, and VM adherence modulo envelope in one proof program.


## 16. Limitations and Scope

Reconfiguration and delegation claims require Assumption Block A premises: typed global and local states, reconfiguration witnesses satisfying `DelegationWF`, enabled post-reconfiguration steps, and compatibility side conditions for unaffected edges.

Envelope exactness requires Assumption Block B premises, including trace well-formedness, certified-step obligations, and the realizability witness schema. VM adherence requires Assumption Block C premises, including envelope-related VM and reference states, trace-consistency obligations, and profile-extraction rules for capability reports.

Crash-stop and Byzantine safety claims are scoped to their explicit fault-model bundles. Byzantine liveness beyond the stated timing and fairness assumptions is out of scope.

Higher-order results depend on channel-payload semantics. First-order collapse is a projection result and does not replace higher-order proofs.

Quantitative constants and base decidability primitives are reused assumptions from earlier results in the series rather than re-derived in this paper.

## 17. Target Application: Unified Distributed Protocol Stacks

The target application is a unified typed protocol stack where networking, coordination, and state evolution are expressed in one choreographic VM framework. The stack uses proof-carrying conformance so capability claims are tied to theorem-pack evidence. This removes informal trust boundaries between layers. It also makes admission failures diagnosable as missing assumptions or missing evidence.

In this setting, typed mode transitions and decidable guard obligations become first-class runtime checks. Delegation supports typed handoff and failover without leaving the theorem scope. Composition theorems provide interoperability guarantees across linked subsystems. Upgrade choreography supports no-downtime migration with typed phase boundaries.

The engineering consequence is a single semantic contract across protocol lifecycle operations. Design-time proofs, deployment-time profile checks, and runtime adherence checks are aligned to the same assumption blocks. This alignment is the main practical payoff of the A through H theorem stack.


## 18. Conclusion

This paper completes the paper-series theorem arc by proving that reconfiguration can be first-class without sacrificing compositional safety. Harmony supplies commutation, Coherence supplies minimal invariant structure, envelope theorems supply exact behavioral boundaries, and adequacy supplies runtime adherence.

Open item: Byzantine liveness under weaker timing assumptions remains future work beyond this paper's exact safety characterization.

## 19. Works Cited

Abadi, M., and Lamport, L. (1991). The Existence of Refinement Mappings. Theoretical Computer Science, 82(2), 253-284.

Alpern, B., and Schneider, F. B. (1985). Defining Liveness. Information Processing Letters, 21(4), 181-185.

Caires, L., and Pfenning, F. (2010). Session Types as Intuitionistic Linear Propositions. CONCUR 2010.

Castellan, S., et al. (2023). Event-structure and partial-order semantics for session-based concurrency. Journal of Logic and Algebraic Methods in Programming.

Chandy, K. M., and Lamport, L. (1985). Distributed Snapshots: Determining Global States of Distributed Systems. ACM Transactions on Computer Systems, 3(1), 63-75.

Clarkson, M. R., and Schneider, F. B. (2010). Hyperproperties. Journal of Computer Security, 18(6), 1157-1210.

Cover, T. M., and Thomas, J. A. (2006). Elements of Information Theory (2nd ed.). Wiley.

Girard, J.-Y. (1987). Linear Logic. Theoretical Computer Science, 50(1), 1-101.

Goguen, J. A., and Meseguer, J. (1982). Security Policies and Security Models. IEEE Symposium on Security and Privacy.

Hinrichsen, J., et al. (2020). Actris: Session-type based reasoning in separation logic. POPL 2020.

Hoare, C. A. R. (1985). Communicating Sequential Processes. Prentice Hall.

Honda, K., Yoshida, N., and Carbone, M. (2008). Multiparty Asynchronous Session Types. POPL 2008.

Lamport, L. (1978). Time, Clocks, and the Ordering of Events in a Distributed System. Communications of the ACM, 21(7), 558-565.

Lamport, L., Shostak, R., and Pease, M. (1982). The Byzantine Generals Problem. ACM Transactions on Programming Languages and Systems, 4(3), 382-401.

Lynch, N. A. (1996). Distributed Algorithms. Morgan Kaufmann.

Milner, R. (1999). Communicating and Mobile Systems: The Pi-Calculus. Cambridge University Press.

Milner, R., Parrow, J., and Walker, D. (1992). A Calculus of Mobile Processes, I and II. Information and Computation, 100(1), 1-77.

Plotkin, G. D. (1981). A Structural Approach to Operational Semantics. DAIMI FN-19.

Shannon, C. E. (1948). A Mathematical Theory of Communication. Bell System Technical Journal, 27(3), 379-423 and 27(4), 623-656.

Telltale Project. (2026). Coherence for Asynchronous Buffered MPST. Project manuscript.

Telltale Project. (2026). Computable Dynamics for Asynchronous MPST. Project manuscript.

Tirore, L., Bengtson, J., and Carbone, M. (2025). Mechanized MPST metatheory with subject-reduction robustness analysis. ECOOP 2025.

Wadler, P. (2012). Propositions as Sessions. ICFP 2012.

## Appendices

## Appendix A. Assumption Regimes and Dependency Shape

This appendix records regime decomposition and theorem dependencies.

### A.1 Regime Classes

Define four premise classes.

1. `R_struct`: reconfiguration well-formedness + coherence transport assumptions.
2. `R_quant`: `R_struct` plus scheduler/budget assumptions for quantitative statements.
3. `R_env`: envelope admissibility + admission/adherence assumptions.
4. `R_byz`: Byzantine assumption bundle layered on `R_env`.

Write `Prem(R)` for the premise set of regime `R`, and define regime order by
$$
R \preceq R' \ :\iff\ \mathrm{Prem}(R)\subseteq \mathrm{Prem}(R').
$$

### A.2 Dependency Spine

The theorem spine is:

```text
B -> (A, C) -> D -> E -> F -> G -> H
                     \              \
                      \              -> S1
                       -> BZ family (with Assumption Block D)
```

**Proposition A.1 (Regime Monotonicity).** If a theorem requires regime `R`, then any stronger regime `R'` with $R \preceq R'$ preserves theorem validity.

*Proof sketch.* Assume `R \preceq R'`, so `\mathrm{Prem}(R) \subseteq \mathrm{Prem}(R')` by definition. Any derivation under `R` uses only premises from `\mathrm{Prem}(R)`, hence all of its premises are available under `R'`. Therefore theorem validity is monotone along the regime order. ∎

### A.3 Consequence of the Spine

Structural theorems (`A-D`) are insensitive to quantitative profile constants; quantitative and envelope/byzantine claims are regime-indexed exactly as declared in main text assumption blocks.

## Appendix B. Deferred Transport Schemas

Transport results in Section 13 factor into structural and analytic layers.

### B.1 Generic Transport Rule

**Theorem B.1 (Transport by Premise Separation).** If structural premises of Theorems B-H hold and analytic package `A_T` holds for target claim `T`, then `T` follows without strengthening structural premises.

*Proof sketch.* Map the structural side of Theorems B-H into the interface required by `A_T`. Apply the analytic theorem in that interface to obtain the target claim. Then transport the conclusion back to the protocol statement through the same interface map. No extra semantic premise is added during transport. ∎

### B.2 Interface Discipline

Transport statements must expose only:

1. structural interface obligations (coherence/harmony/envelope/adherence),
2. analytic assumptions external to this manuscript,
3. resulting transported consequence.

This prevents hidden strengthening of either side.

### B.3 Representative Schemas

1. Tail-bound transport schema:
$$
\text{Struct}_{B..H}\ \land\ \text{ConcentrationPkg}(\theta)
\;\Longrightarrow\;
\forall t\ge 0,\ \Pr[X-\mathbb E X \ge t]\le \Psi_{\mathrm{tail}}(t;\theta).
$$

2. Mixing/convergence transport schema:
$$
\text{Struct}_{B..H}\ \land\ \text{MixPkg}(\eta)
\;\Longrightarrow\;
\forall n\ge 0,\ \|\mu_n-\mu_*\|_{\mathrm{TV}}\le \Psi_{\mathrm{mix}}(n;\eta).
$$

3. Compositional exactness transport schema:
$$
\text{Struct}_{B..H}\ \land\ \text{NonInterference}
\;\Longrightarrow\;
\mathsf{EnvelopeExact}(C_1)\land \mathsf{EnvelopeExact}(C_2)\Rightarrow \mathsf{EnvelopeExact}(C_1\otimes C_2).
$$

4. Byzantine adherence transport schema:
$$
\text{Struct}_{B..H}\ \land\ \text{AssumptionBlockD}\ \land\ \text{RuntimeWitnessPkg}
\;\Longrightarrow\;
\mathsf{VMByzAdheres}\ \land\ \mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}\text{-conformance}.
$$

## Appendix C. Deferred Consequence Statements

### C.1 Reconfiguration and Minimality

**Proposition C.1.** Under Assumption Block A, Harmony (Theorem B) and Relative Minimality (Theorem D) imply that any admissible safe-reconfiguration invariant implies `Coherent` and therefore factors through the same canonical safety core.

*Proof sketch.* Theorem D shows that every admissible invariant factors through `Coherent`. Theorem B then gives commutation of reconfiguration steps over that common core. Chaining these two implications yields the proposition. ∎

### C.2 Envelope and Determinism Boundary

**Proposition C.2.** Under Assumption Block B, Theorem F and Theorem G jointly characterize determinism modulo exchange/spatial normalization and identify strict boundary witnesses for inadmissible envelope extensions.

*Proof sketch.* Apply Theorem F to obtain exact envelope characterization via soundness, realizability, and maximality. Apply Theorem G to identify the normalized observational equalities that hold inside that exact envelope. Combining both gives the claimed determinism boundary statement. ∎

### C.3 Runtime Adequacy and Admission

**Proposition C.3.** Under Assumption Block C, Theorem H plus Corollary S1 yields principal-capability admission completeness with explicit rejection diagnostics when premise evidence is missing.

*Proof sketch.* Theorem H yields adequacy and adherence under Assumption Block C. Corollary S1 then refines this with principal-capability inference and admission completeness. Together they imply the proposition. ∎

### C.4 Byzantine Scope Boundary

**Proposition C.4.** Under Assumption Block D, the `BZ` family establishes exact safety characterization and converse counterexample packaging, but does not establish Byzantine liveness outside declared timing/fairness assumptions.

*Proof sketch.* Theorem BZ and Corollary BZ.1 provide exact Byzantine safety characterization and converse counterexample packaging under Assumption Block D. Section 16 explicitly restricts scope away from weaker timing and fairness assumptions required for Byzantine liveness. Therefore the claimed boundary follows directly. ∎

## Appendix D. Mechanization and Reproducibility

### D.1 Module Map

| Theorem family | Primary modules | Representative theorem anchors |
|----------------|-----------------|--------------------------------|
| `B` | `lean/Protocol/Deployment/LinkingCore.lean`, `lean/Protocol/Deployment/LinkingTheorems.lean`, `lean/Runtime/Proofs/EffectBisim/Congruence.lean` | `link_harmony_through_link`, `link_preserves_coherent` |
| `A`, `C`, `D` | `lean/Protocol/Coherence/ErasureCharacterization.lean` | `coherent_erasure_stable`, `safeDelegation_iff_footprint`, `relative_minimality` |
| `E` | `lean/Protocol/Deployment/LinkingTheorems.lean`, `lean/Runtime/Proofs/Lyapunov.lean` | `flagship_composed_system_conservation`, `lyapunov_conserved_under_balanced_delegation` |
| `F`, `G` | `lean/Runtime/Adequacy/EnvelopeCore/*.lean`, `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean` | `consensusEnvelope_exact_of_profile`, `failureEnvelope_maximality_of_profile`, normalization theorems |
| `H`, `S1` | `lean/Runtime/Adequacy/Adequacy.lean`, `lean/Runtime/Adequacy/CompileRefinesEffectBisim.lean`, `lean/Runtime/Proofs/ObserverProjectionEffectBisim.lean`, `lean/Runtime/Proofs/HandlerEquivalence.lean`, `lean/Runtime/Proofs/TheoremPack/*.lean` | `protocolOutcome_effectBisim_of_observationalEq`, `vm_adequacy_of_trace_consistency`, profile-admission theorems |
| `BZ` family | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean`, `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems/AdmissionAndBridge.lean` | `byzantineSafety_exact_of_profile`, `Distributed.ByzantineSafety.ExactByzantineSafetyCharacterization`, `vmByzantineEnvelopeAdherence_of_witness`, `byzantineCrossTargetConformance_of_witnesses` |

### D.2 Reproducibility Protocol

Reproduction uses the pinned Lean toolchain and manifest.

1. Build theorem families listed in D.1.
2. Run `just escape` and `just verify-protocols`.
3. Validate that D.1 anchor names resolve and no proof holes remain.

Expected outcome:

Full theorem-spine compilation (`B` through `H`, `S1`, `BZ`) succeeds, profile extraction and admission modules compile, and bridge and adequacy modules compile under the pinned toolchain.

## Appendix E. Index of Main Results

| Claim | Main section | Assumption scope | Formal location |
|-------|--------------|------------------|-----------------|
| Theorem B. Reconfiguration Harmony | Section 4 | Assumption Block A reconfiguration well-formedness premises | linking/effect-bisim congruence modules; Appendix D |
| Theorem A. Erasure Characterization of Coherence | Section 5 | Assumption Block 0 core model premises | `ErasureCharacterization.lean`; Appendix D |
| Theorem C. Safe Delegation Sufficiency | Section 6 | Assumption Block A + coherence precondition | delegation/footprint lemmas; Appendix D |
| Corollary C.1. Footprint Exactness Packaging | Section 6 | Assumption Block A + theorem C + footprint side conditions | footprint equivalence chain; Appendix D |
| Theorem D. Relative Minimality | Section 7 | Assumption Block A + admissibility/delegation adequacy | `relative_minimality`; Appendix D |
| Theorem E. Composed-System Conservation | Section 8 | Assumption Block A + quantitative lift side conditions | linking conservation + Lyapunov modules; Appendix D |
| Corollary S2. Compositional Exactness Under Non-Interference | Section 8 | Assumption Block A + theorem E + non-interference assumptions | transport schema; Appendix B |
| Theorem F. Exact Determinism Envelope | Section 9 | Assumption Block B envelope-admissibility premises | envelope-core/extraction modules; Appendix D |
| Corollary F.1. Finite-Erasure Transportability Boundary | Section 9 | Assumption Block B rational finite-state premises | rational fragment bridge; Appendix B and D |
| Corollary F.2. Strict Boundary Witness | Section 9 | Assumption Block B strict-extension witness premises | strict-boundary witness module; Appendix B and D |
| Corollary F.3. Inductive-Embedding Exactness | Section 9 | Assumption Block B + embedding side conditions | coinductive-inductive bridge modules; Appendix B and D |
| Theorem G. Exchange-Normalized Determinism and Spatial Monotonicity | Section 10 | Assumption Block B + exchange/spatial side conditions | reconfiguration-bridge normalization theorems; Appendix D |
| Theorem H. Observational Adequacy and VM Adherence | Section 11 | Assumption Block C adequacy bridge premises | adequacy/refinement/VM-view bridge modules; Appendix D |
| Corollary S1. Principal Capability and Admission Completeness | Section 11 | Assumption Block C + admission-completeness assumptions | admission/profile extraction modules; Appendix D |
| Proposition 1. Capability-Bit Soundness | Section 11 | Assumption Block C + theorem-pack evidence/profile alignment | theorem-pack inventory/extraction modules; Appendix D |
| Theorem BZ. Exact Byzantine Safety Characterization | Section 11 | Assumption Block D Byzantine premises | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean` (`byzantineSafety_exact_of_profile`), `lean/Distributed/Families/ByzantineSafety/Core/Base.lean` (`ExactByzantineSafetyCharacterization`); Appendix D |
| Corollary BZ.1. Converse Counterexample Families | Section 11 | Assumption Block D + dropped-assumption witness classes | Section 11 packaging + Appendix B and D |
| Proposition BZ.2. Byzantine VM Adherence and Admission Gating | Section 11 | Assumption Block C and D + capability/admission premises | Byzantine adherence/conformance/admission modules; Appendix D |
