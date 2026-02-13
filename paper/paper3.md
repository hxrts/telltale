# Harmony from Coherence in Asynchronous MPST: A Minimal Erasure Invariant for Classical Dynamics

## Abstract

A *Reconfiguration Harmony Theorem* is established for asynchronous MPST: under well-formed `link` and delegation reconfiguration, projection commutes with reconfigured evolution. This gives a proof architecture for dynamic participant sets where topology change is a first-class semantic step.

The invariant kernel is characterized in both directions. Coherence is identified as an erasure characterization on active edges and as the weakest admissible invariant for delegation safety (relative minimality). Safe delegation and composed-system conservation then follow, including quantitative lift of the Computable Dynamics paper's Lyapunov framework with conservation for pure reconfiguration and descent or budget certificates for transition choreographies.

The behavioral boundary is characterized by an exact determinism envelope with soundness, realizability, and maximality. Exchange-normalized determinism with spatial-subtyping monotonicity is established. Observational adequacy links abstract and protocol proofs to VM adherence modulo envelope. All results are mechanized in Lean 4.

## 1. Introduction

Delegation and topology change are a primary failure point in MPST developments (Honda et al., 2008, and Tirore, Bengtson, and Carbone, 2025). Many systems exclude these operations, or admit them operationally without a theorem that connects choreography-level and local-level evolution. This paper addresses that gap with a commutation theorem for reconfiguration.

The central statement is Harmony under reconfiguration:

```text
project ∘ step_reconfig = local_step_reconfig ∘ project
```

for well-formed `link` and delegation operations with enabled post-reconfiguration steps. The theorem development then proceeds from commutation to characterization and runtime adherence. It establishes erasure characterization of Coherence, safe delegation consequences, and relative minimality over admissible invariants. It then proves composed-system conservation, exact envelope characterization, exchange-normalized determinism with spatial monotonicity, and observational adequacy with VM adherence.

The determinism-envelope layer follows a standard refinement-bound idea. One defines an admissible behavior relation that captures implementation freedom while preserving safety-visible observations. What is new here is an exact characterization for asynchronous MPST reconfiguration with soundness, realizability, and maximality proved in one theorem stack and connected directly to runtime admission and adherence artifacts.

Equivalently, the envelope is a coarse-grained observational equivalence. It is the maximal admissible blur between executions that still preserves certified safety-visible meaning.

Sharding correspondence follows a standard simulation view for distributed execution. A split execution should preserve the same safety-visible meaning as a reference execution under explicit compatibility assumptions. What is new here is an explicit envelope contract for local and cross-machine sharding profiles that makes the admissible difference class theorem-checkable and capability-gated at the VM bridge.

The envelope layer also admits a rate-distortion style reading. The reference semantics is the source, VM and sharded executions are channels, and admission profiles are distortion constraints on safety-visible observations (Shannon, 1948, and Cover and Thomas, 2006). Maximality then states that no strictly larger distortion class preserves the same certified safety guarantees.

This paper closes the series architecture. *Coherence for Asynchronous Buffered MPST: A Mechanized Metatheory* supplies the invariant kernel. *Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures* supplies bounds and decision procedures. This paper supplies reconfiguration commutation and envelope-level runtime adherence.

Scope is restricted to asynchronous buffered semantics with explicit reconfiguration side conditions, crash-stop fault assumptions where fault claims are stated, and declared envelope-admission profiles. Claims outside those assumptions are not made.

The contributions are explicit.

1. A reconfiguration commutation theorem that covers both static composition and dynamic delegation.
2. An exact characterization of Coherence by active-edge erasure realizability and a relative-minimality theorem over admissible invariants.
3. A determinism-envelope theory with soundness, realizability, maximality, and exchange and spatial normalization consequences.
4. An abstract-to-VM adequacy bridge that ties profile claims to theorem-pack capability evidence.
5. A Byzantine envelope extension with exact characterization, converse counterexample families, and capability-gated VM adherence.

Figure 1. Harmony commuting square. The figure shows commutation between reconfigured global steps and local projected steps.

## 2. Setup, Definitions, and Side Conditions

### 2.1 Base Recap

Assume the base model from *Coherence for Asynchronous Buffered MPST: A Mechanized Metatheory* and *Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures*:

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
| $W$             | weighted state function inherited from *Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures* |
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

**Definition. Harmony.** Projection commutes with reconfigured evolution.

**Definition. Joint Realizability on Active Edges.** Projected local views admit a compatible active-edge witness assignment.

**Definition. `Admissible(I)`.** Locality plus erasure stability (`ConfigEquiv`) plus frame stability plus delegation adequacy.

Figure 2. Delegation footprint before and after reconfiguration. The figure marks affected edges and unchanged edges.

## 3. Worked Example

Protocol family: Distributed Capacity Pool.

Single-pool baseline (from the preceding papers):

```text
C -> P : Request(n)
P -> C : Grant(k)
C -> M : Report(k)
M -> P : Confirm
P -> C : Token(t)
```

This paper's distributed extension:

- pool federation through `link`,
- optimistic -> coordinated mode transitions under typed guards,
- dynamic delegation `C -> C'` for token capability transfer,
- versioned migration (`P1 -> P2`) as a typed choreography.

Main checkpoints in this example:

1. Static link: projection commutes with federation composition.
2. Mode transition: guard conditions invoke the Computable Dynamics decidability and bounds and preserve Coherence.
3. Delegation handoff: redirected edges remain coherent, and local and global delegation steps commute.
4. Upgrade choreography: version boundary is controlled by subtype and guard obligations, and no invariant breakage occurs at phase edges.

Table 4 gives the typed guard clauses for the optimistic-to-coordinated transition.

| Guard clause                     | Static source                                                                                                                                               | Consequence                               |
|----------------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------|
| `conflict_detected`              | application-level trigger                                                                                                                                  | transition path enabled                   |
| `reachable(Coord)`               | crash-tolerance decider from *Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures* | coordination path not disconnected        |
| $W \leq \text{transitionBudget}$ | quantitative bound from *Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures*      | transition completes within budget        |
| $|F| \leq f$                     | fault-budget declaration                                                                                                                                   | bounded crash tolerance during transition |

The delegation trace is the concrete witness pattern used in Sections 4 and 6. State zero has `C` holding `Token(t)` and `C'` without rights. State one executes delegation and updates the footprint edges. State two has `C'` holding delegated rights with preserved coherence at affected active edges.

The transition trace is the concrete witness pattern used in Sections 8 and 11. State zero is optimistic mode with pending local grants. State one satisfies guard clauses and fires the transition choreography. State two reaches coordinated mode with bounded transition cost and preserved envelope obligations.

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

Figure 3. Static and dynamic Harmony cases. The figure separates `link` commutation from delegation commutation.

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

Figure 4. Admissible-invariant lattice. The figure places Coherence as the weakest admissible invariant node.

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
2. Quantitative lift from *Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures* holds:
   - pure reconfiguration conserves the weighted measure,
   - transition choreographies are governed by descent and budget certificates.

Mechanized anchors:

- `flagship_composed_system_conservation`
- `lyapunov_conserved_under_balanced_delegation`

This theorem combines composition, delegation, and quantitative invariants in one package.

**Corollary S2. Compositional Exactness Under Non-Interference.** For all compositions $C_1 \otimes C_2$, if non-interference premises hold across the composition boundary, then envelope exactness is preserved by composition:
$$
\mathsf{EnvelopeExact}(C_1) \land \mathsf{EnvelopeExact}(C_2)
\implies
\mathsf{EnvelopeExact}(C_1 \otimes C_2).
$$
Strictness witnesses are provided for dropped non-interference premises.

Figure 5. Composed-system conservation of $W$ under pure reconfiguration. The figure contrasts preserved and budgeted phases.

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

**Corollary F.1. Finite-Erasure Transportability Boundary.** Under stated model assumptions,
$$
\forall t,\ \mathsf{FiniteErasureTransportable}(t) \iff \mathsf{RationalFiniteState}(t).
$$

**Corollary F.2. Strict Boundary Witness.** There exists $t$ such that
$$
\neg \mathsf{RationalFiniteState}(t) \land \neg \mathsf{FiniteErasureTransportable}(t).
$$

**Corollary F.3. Inductive-Embedding Exactness.** For all inductive states $x$, exact envelope characterization is preserved under `toCoind`:
$$
\mathsf{EnvelopeExact}_{\mathrm{ind}}(x)
\iff
\mathsf{EnvelopeExact}_{\mathrm{coind}}(\mathsf{toCoind}(x)).
$$

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

## 11. Theorem H: Observational Adequacy and VM Adherence Modulo Envelope

**Assumption Block C. Adequacy Bridge Premises.** Adequacy and adherence theorems assume envelope-related VM and reference states, trace-consistency premises for observable events, and profile extraction rules for capability reports.

**Theorem H. Observational Adequacy and VM Adherence Modulo Envelope.**
For all VM states $S_{\mathsf{vm}}$, reference states $S_{\mathsf{ref}}$, and profiles $(P,\Pi)$ that satisfy Assumption Block C, the following hold:
$$
\mathsf{EnvelopeRel}(S_{\mathsf{vm}}, S_{\mathsf{ref}})
\implies
\mathsf{Obs}(S_{\mathsf{vm}})=\mathsf{Obs}(S_{\mathsf{ref}}).
$$
$$
\mathsf{HasProfileCapabilities}(P,\Pi)
\implies
\mathsf{VMAdheres}(P,\Pi).
$$
Local and sharded variants are recovered as profile-specific instances under explicit collapse assumptions.

**Proposition 1. Capability-Bit Soundness.** For all runtime profiles $q$ and capability bits $b$, if $q$ advertises $b$, then there exists a corresponding theorem-pack artifact $a_b$ such that $a_b$ satisfies the same envelope-premise profile used by Theorem H.

Mechanized anchors:

- adequacy theorem layer, including `vm_adequacy_of_trace_consistency`
- VM adherence and admission layers
- profile extraction to theorem packs and distributed adapters

Coinductive adequacy bridge pack used here: `protocolOutcome_effectBisim_of_observationalEq`, `compile_refines_observationalEq_of_effectBisim`, `vmView_effectBisim_of_VMCEquiv`, `vmCEquiv_of_vmView_effectBisim`, and `topology_change_preserves_VMCEquiv_via_effectBisim`.

Runtime consequence: proof-carrying conformance between claimed profile bits and available theorem artifacts.

This theorem is the formal bridge from abstract proofs to runtime capability claims. If an implementation advertises a profile capability bit, the corresponding theorem-pack artifact must exist and validate the same envelope obligations. This prevents profile over-claiming and makes runtime conformance checkable at artifact granularity.

**Corollary S1. Principal Capability and Admission Completeness.** Let $D_{\text{user}}$ be a requested envelope capability and let $D_{\text{prog}}$ be inferred from program and deployment profile. Under the admission premises,
$$
D_{\text{user}} \subseteq D_{\text{prog}} \subseteq \mathcal E
$$
and admission is complete with a principal inferred capability.

**Assumption Block D. Byzantine Characterization Premises.** Byzantine characterization assumes explicit bundle $H_{\mathrm{byz}}$ with fault-model, authentication and evidence-validity, conflict-exclusion primitive consistency, and adversarial-budget side conditions.

**Theorem BZ. Exact Byzantine Safety Characterization.** Under Assumption Block D, there exists a characterization predicate $\mathsf{ByzChar}$ such that
$$
\mathsf{ByzSafe} \iff \mathsf{ByzChar}.
$$
The statement is exact for the declared Byzantine model profile.

**Corollary BZ.1. Converse Counterexample Families.** If any required class in Assumption Block D is dropped, there exists a counterexample family violating $\mathsf{ByzSafe}$. Covered dropped classes are quorum or intersection obligations, authentication or evidence-validity obligations, adversarial-budget obligations, and primitive-consistency obligations.

**Proposition BZ.2. Byzantine VM Adherence and Admission Gating.** For runtime profile $(P,\Pi)$, if theorem-pack capability bits include Byzantine safety characterization and VM envelope adherence artifacts, then admitted executions satisfy $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$ modulo $\mathcal E_{\mathrm{byz}}$ and rejected requests correspond to failed assumptions or missing artifacts.

## 12. Supporting Formal Layer

Three support packages make the main theorem stack executable and compositional.

1. Higher-order extension: channel-carrying payloads and graph-delta semantics.
2. Conservative extension: collapse back to first-order when no channel payloads are present.
3. Delegation-preservation microkernel: redirected, unrelated, and other-session edge coherence lemmas.

## 13. Worked Transport in Main Body

This section contains two worked transport exemplars that instantiate the theorem stack. The goal is to make the assumption split explicit in the main text. Structural premises come from typing, Harmony, and envelope-admission results. Analytic premises are discharged separately in each instance.

The first exemplar is a completion-time tail bound in a large-deviation style. The structural side is provided by Theorems B through H and the declared profile assumptions. The analytic side is a standard tail bound package for the chosen stochastic model. The transport step composes these two layers without changing either layer's proof obligations.

The second exemplar is a convergence-to-baseline bound in a mixing-time style. The structural side is the same theorem stack used in the first exemplar. The analytic side is a spectral or contraction package specified for the selected transition kernel. The resulting statement isolates exactly which premises are semantic and which premises are analytic.

## 14. Discussion: The Classical Boundary

This section is interpretive and does not add theorem premises. Theorems A through H remain valid without this interpretation. The discussion explains why the proof architecture has its current shape. It also explains where the current model intentionally stops.

The formal layer establishes exchangeability through delegation-compatible symmetries, local compatibility through active-edge Coherence, and well-posed quotient dynamics through Harmony and envelope laws. These results define an erasure-safe regime for the model class in this paper. Within that regime, safety-visible behavior is invariant under the declared symmetries. This is the precise sense in which identity details are treated as gauge.

The boundary claim is exact for the stated assumptions. Safe erasures are exactly those justified by Coherence-preserving symmetries and envelope admissibility laws. Behaviors that depend on non-erasable state update mechanisms require a different semantic model. Examples include measurement backaction and entanglement-sensitive observables.

This interpretation is consistent with established coherence and session-typing lines in Girard (1987), Caires and Pfenning (2010), and Wadler (2012). The paper does not claim model identity with those frameworks. It claims an operational correspondence at the level of compatibility structure. That correspondence is sufficient for the theorem program in this manuscript.

## 15. Related Work

Work on reconfiguration and delegation established important safety baselines for dynamic session topologies. These lines often prove preservation-style properties for specific operators. They usually do not package commutation, minimality, and exact envelope bounds in one theorem stack. This paper targets that combined package.

Mechanized MPST developments established high-confidence metatheory and exposed proof fragility under richer operational features. The robustness analysis in Tirore, Bengtson, and Carbone (2025) is especially relevant to this pressure point. The present work responds by factoring the development into reusable assumption blocks and bridge theorems. This choice reduces repetition across reconfiguration, exactness, and adequacy layers.

Session foundations from Honda et al. (2008) and logical correspondences from Caires and Pfenning (2010) and Wadler (2012) remain the base for local and global consistency claims. Program-logical lines such as Hinrichsen et al. (2020) provide strong local reasoning for implementations. Event-structure and partial-order models such as Castellan et al. (2023) provide alternate macro semantics for concurrency. This paper works at the semantic-commutation layer and connects that layer to runtime adherence artifacts.

The delta of this paper is theorem-level integration of reconfiguration Harmony, relative minimality, exact determinism-envelope characterization, and VM adherence modulo envelope in one coherent proof program.


## 16. Limitations and Scope

Reconfiguration and delegation claims require Assumption Block A premises: typed global and local states, reconfiguration witnesses satisfying `DelegationWF`, enabled post-reconfiguration steps, and compatibility side conditions for unaffected edges.

Envelope exactness requires Assumption Block B premises, including trace well-formedness, certified-step obligations, and the realizability witness schema. VM adherence requires Assumption Block C premises, including envelope-related VM and reference states, trace-consistency obligations, and profile-extraction rules for capability reports.

Crash-stop and Byzantine safety claims are scoped to their explicit fault-model bundles. Byzantine liveness beyond the stated timing and fairness assumptions is out of scope.

Higher-order results depend on channel-payload semantics. First-order collapse is a projection result and does not replace higher-order proofs.

Quantitative constants and base decidability primitives are reused assumptions from earlier results in the series rather than re-derived in this paper.

## 17. Target Application: Unified Distributed Protocol Stacks

The target application is a unified typed protocol stack where networking, coordination, and state evolution are expressed in one choreographic VM framework. The stack uses proof-carrying conformance so capability claims are tied to theorem-pack artifacts. This removes informal trust boundaries between layers. It also makes admission failures diagnosable as missing assumptions or missing artifacts.

In this setting, typed mode transitions and decidable guard obligations become first-class runtime checks. Delegation supports typed handoff and failover without leaving the theorem scope. Composition theorems provide interoperability guarantees across linked subsystems. Upgrade choreography supports no-downtime migration with typed phase boundaries.

The engineering consequence is a single semantic contract across protocol lifecycle operations. Design-time proofs, deployment-time profile checks, and runtime adherence checks are aligned to the same assumption blocks. This alignment is the main practical payoff of the A through H theorem stack.


## 18. Conclusion

This paper completes the paper-series theorem arc by proving that reconfiguration can be first-class without sacrificing compositional safety. Harmony supplies commutation, Coherence supplies minimal invariant structure, envelope theorems supply exact behavioral boundaries, and adequacy supplies runtime adherence.

Open item: Byzantine liveness under weaker timing assumptions remains future work beyond this paper's exact safety characterization.

## 19. Works Cited

Caires, L., and Pfenning, F. (2010). Session Types as Intuitionistic Linear Propositions. CONCUR 2010.

Castellan, S., et al. (2023). Event-structure and partial-order semantics for session-based concurrency. Journal of Logic and Algebraic Methods in Programming.

Cover, T. M., and Thomas, J. A. (2006). Elements of Information Theory (2nd ed.). Wiley.

Girard, J.-Y. (1987). Linear Logic. Theoretical Computer Science, 50(1), 1-101.

Hinrichsen, J., et al. (2020). Actris: Session-type based reasoning in separation logic. POPL 2020.

Honda, K., Yoshida, N., and Carbone, M. (2008). Multiparty Asynchronous Session Types. POPL 2008.

Shannon, C. E. (1948). A Mathematical Theory of Communication. Bell System Technical Journal, 27(3), 379-423 and 27(4), 623-656.

Telltale Project. (2026). Coherence for Asynchronous Buffered MPST: A Mechanized Metatheory. Project manuscript.

Telltale Project. (2026). Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures. Project manuscript.

Tirore, L., Bengtson, J., and Carbone, M. (2025). Mechanized MPST metatheory with subject-reduction robustness analysis. ECOOP 2025.

Wadler, P. (2012). Propositions as Sessions. ICFP 2012.

## Appendices

## Appendix A. Full Regime Analysis

- scheduling/failure regime matrix,
- structural versus regime-sensitive theorem families,
- crash-stop capability analysis for composed/delegated systems,
- heavy-tail/non-normal boundary notes.

## Appendix B. Expanded Practical Payoff Tables

- transported-result payoff matrix,
- regime interpretation guide,
- deployment-level reading notes.

## Appendix C. Full Theorem-Transport Catalog

- transport-only theorem matrix,
- assumption profiles with necessity tags,
- fully discharged exemplars,
- limitation statement for analytic side conditions.

## Appendix D. Formal Mechanization and Runtime Realization (Supporting)

- supporting theorem decomposition,
- coinductive effect-bisim bridge index (`effectBisim_implies_observationalEquivalence`, `effectBisim_congr_link`, `configEquiv_iff_effectBisim_silent`, `rationalEffect_transport_bridge`, `strict_boundary_witness_effect`),
- cross-layer impact map,
- theorem-to-file index,
- proof dependency DAG,
- build/check reproducibility commands.

## Appendix E. Theorem Index

| Claim                                                               | Main section | Assumption scope                                                                            | Proof location                                       |
|---------------------------------------------------------------------|--------------|---------------------------------------------------------------------------------------------|----------------------------------------------------- |
| Theorem B. Reconfiguration Harmony                                  | Section 4    | Assumption Block A reconfiguration well-formedness premises                                 | Section 4 proof sketch, Appendix D                   |
| Theorem A. Erasure Characterization of Coherence                    | Section 5    | Assumption Block 0 core model premises                                                      | Section 5 statement and proof sketch, Appendix D     |
| Theorem C. Safe Delegation Sufficiency                              | Section 6    | Assumption Block A premises plus Coherence precondition                                     | Section 6 statement and proof sketch, Appendix D     |
| Corollary C.1. Footprint Exactness Packaging                        | Section 6    | Assumption Block A premises plus theorem C premises and footprint side conditions           | Section 6 statement, Appendix D                      |
| Theorem D. Relative Minimality                                      | Section 7    | Assumption Block A premises plus admissibility and delegation adequacy definitions          | Section 7 statement and proof sketch, Appendix D     |
| Theorem E. Composed-System Conservation                             | Section 8    | Assumption Block A premises plus quantitative lift side conditions                          | Section 8 statement and proof sketch, Appendix A and Appendix D |
| Corollary S2. Compositional Exactness Under Non-Interference        | Section 8    | Assumption Block A premises plus theorem E premises and non-interference assumptions        | Section 8 statement, Appendix C                      |
| Theorem F. Exact Determinism Envelope                               | Section 9    | Assumption Block B envelope admissibility premises                                          | Section 9 statement and proof sketch, Appendix A and Appendix C |
| Corollary F.1. Finite-Erasure Transportability Boundary             | Section 9    | Assumption Block B premises on rational finite-state fragment                               | Section 9 statement, Appendix C                      |
| Corollary F.2. Strict Boundary Witness                              | Section 9    | Assumption Block B premises and strict extension witness conditions                         | Section 9 statement, Appendix C                      |
| Corollary F.3. Inductive-Embedding Exactness                        | Section 9    | Assumption Block B premises and `toCoind` embedding side conditions                         | Section 9 statement, Appendix C                      |
| Theorem G. Exchange-Normalized Determinism and Spatial Monotonicity | Section 10   | Assumption Block B premises plus exchange and spatial refinement side conditions            | Section 10 statement and proof sketch, Appendix C    |
| Theorem H. Observational Adequacy and VM Adherence                  | Section 11   | Assumption Block C adequacy bridge premises                                                 | Section 11 statement and proof sketch, Appendix D    |
| Corollary S1. Principal Capability and Admission Completeness       | Section 11   | Assumption Block C premises plus admission-completeness assumptions                         | Section 11 statement, Appendix D                     |
| Proposition 1. Capability-Bit Soundness                             | Section 11   | Assumption Block C premises plus theorem-pack artifact existence and profile-premise alignment | Section 11 statement, Appendix D                     |
| Theorem BZ. Exact Byzantine Safety Characterization                 | Section 11   | Assumption Block D Byzantine characterization premises                                      | Section 11 statement, Appendix D                     |
| Corollary BZ.1. Converse Counterexample Families                    | Section 11   | Assumption Block D premises with dropped-assumption witnesses                               | Section 11 statement, Appendix D                     |
| Proposition BZ.2. Byzantine VM Adherence and Admission Gating       | Section 11   | Assumption Block C and D premises with capability-bit and admission-diagnostic assumptions  | Section 11 statement, Appendix D                     |
