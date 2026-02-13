# Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures

## Abstract

We prove that quotient dynamics for asynchronous MPST are computable in two coordinated senses. The first is quantitative and uses a weighted Lyapunov measure. The second is algorithmic and uses finite-reachability decision schemas over regular fragments.

The weighted measure is $W = 2 \cdot \Sigma\text{depth} + \Sigma\text{buffer}$. Productive steps strictly decrease $W$, which yields explicit productive-step bounds and scheduler-lifted total-step bounds under stated assumptions. Finite-reachability schemas then yield decidability for asynchronous subtyping, regular type equivalence, crash-stop tolerance, and branching feasibility.

All core claims are mechanized in Lean 4. This paper builds directly on *Coherence for Asynchronous Buffered MPST* and provides the quantitative and decision layer used by *Harmony from Coherence in Asynchronous MPST*.

## 1. Introduction

The preceding manuscript establishes Coherence as the local invariant kernel. This paper studies what can be computed from that kernel at runtime and analysis time.

The contribution has two parts. One part gives explicit quantitative bounds. The second part gives uniform decidability transfer through one finite-state schema.

The quantitative branch uses a classical Lyapunov template from stability theory (Lyapunov, 1892). The method chooses a nonnegative potential and proves strict decrease under productive transitions. In stochastic-process terms, this aligns with Foster-style drift arguments and modern Markov-stability treatments that lift local decrease to global bounds (Foster, 1953; Meyn and Tweedie, 2009). The weighted measure $W$ in this paper is the protocol-level potential for that template.

Here the Lyapunov potential is an energy-like ranking function on states, not physical energy. The core proof pattern is nonnegative potential plus strict decrease on productive steps, which yields bounded productive progress.

The scheduler assumptions play the role of a drift condition. Under a declared fairness profile, productive decrease has an expected directional effect along traces, which is what justifies lifting local decrease to conservative total-step bounds.

The algorithmic branch follows a standard regularity-to-decidability strategy from finite-state analysis. Regularity assumptions are used to bound reachable structure, then one terminating exploration yields decision procedures by soundness and completeness transfer (Karp and Miller, 1969; Brand and Zafiropulo, 1983; Hopcroft and Ullman, 1979; Baier and Katoen, 2008). What is new here is a single reusable schema that instantiates to asynchronous subtyping, regular equivalence, crash tolerance, and branching feasibility without changing the core proof pattern.

Capacity thresholds follow a standard phase-boundary intuition in buffered and queue-like systems, where behavior classes change when load or backlog crosses a boundary. The standard point is qualitative phase separation between safe and unstable regions. What is new here is a theorem-level threshold boundary $B_c$ with an exact interface-level characterization under explicit MPST assumptions.

Operationally, $B_c$ is a regime split. Below $B_c$ one behavior class is admitted by the theorem profile. Above $B_c$ a different class appears and may require stronger conditions. The boundary statement is exact under the paper's assumptions.

An information-theoretic view helps interpret the decision layer. Regularity hypotheses induce finite summaries that preserve exactly the predicates this paper decides, which is a sufficiency claim rather than heuristic compression (Cover and Thomas, 2006). In that sense the finite exploration graph is an analysis channel with no decision loss for the targeted properties.

The paper presents a single regularity-driven method that generates both numeric and algorithmic claims.

Dependency across the three papers is explicit. *Coherence for Asynchronous Buffered MPST* supplies the invariant kernel, this paper supplies computable dynamics and decision procedures, and *Harmony from Coherence in Asynchronous MPST* lifts these components to reconfiguration and envelope theorems.

Scope is restricted to regular finite-reachability fragments for decision claims and explicit scheduler profiles for total-step bounds. Fault claims in this paper include crash-stop exactness and an explicit Byzantine safety characterization under a separate assumption bundle $H_{\mathrm{byz}}$, in the broader distributed-fault context of FLP-style impossibility, partial synchrony, and failure-detector stratification (Fischer, Lynch, and Paterson, 1985; Dwork, Lynch, and Stockmeyer, 1988; Chandra and Toueg, 1996), plus distributed-algorithm baselines (Lynch, 1996) and Byzantine baselines (Lamport, Shostak, and Pease, 1982; Castro and Liskov, 1999). Reconfiguration commutation and determinism-envelope maximality are deferred to *Harmony from Coherence in Asynchronous MPST*.

Our contributions are as follows:

1. A quantitative descent theorem with explicit productive-step and scheduler-lifted total-step bounds from one weighted measure.
2. A uniform algorithmic schema that turns regular finite reachability into reusable decidability procedures.
3. A crash-stop tolerance characterization with decision and residual-graph exactness under stated side conditions.
4. A Byzantine safety characterization interface with exact iff form, converse counterexample families, and VM-bridge handoff obligations.
5. A mechanized architecture that shares one regularity kernel across quantitative and algorithmic branches.

Related liveness lines often emphasize qualitative progress in session-typed settings (Honda et al., 2008, and Caires and Pfenning, 2010). Related mechanized lines expose proof brittleness and motivate reusable proof architecture (Tirore, Bengtson, and Carbone, 2025). Figure 1 records the proof split used in this paper: one shared regularity kernel induces both the quantitative branch (descent and bounds) and the algorithmic branch (finite exploration and deciders).

## 2. Model Summary

The model uses asynchronous buffered semantics with active-edge Coherence from *Coherence for Asynchronous Buffered MPST*. Delivery behavior is parameterized by `DeliveryModel`.

Table 1 records the assumptions used for exact statements in this paper.

| Assumption                                      | Status                                   |
|-------------------------------------------------|------------------------------------------|
| asynchronous buffered semantics                 | required                                 |
| active-edge Coherence                           | required                                 |
| regular finite-reachability fragment            | required for decidability claims         |
| fairness profile                                | required for scheduler-lifted bounds     |
| crash-stop fault model                          | required for Theorem 3                   |
| Byzantine assumption bundle $H_{\mathrm{byz}}$  | required for Theorem 4 and Corollary 4.1 |

**Assumption Block 0. Core Model Premises.** Core claims in this paper assume asynchronous buffered semantics, active-edge Coherence, regular finite reachability for decision results, and the stated fairness profile for scheduler-lifted bounds.

Table 2a fixes shared notation used across all three papers.

| Symbol                                        | Meaning                                          |
|-----------------------------------------------|--------------------------------------------------|
| $H_{\mathrm{byz}}$                            | Byzantine characterization assumption bundle     |
| $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$ | Byzantine safety-visible observation projection  |
| $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$  | Byzantine safety-visible observational equality  |
| $\mathcal E_{\mathrm{byz}}$                   | Byzantine determinism-envelope relation          |

Table 2b fixes paper-specific notation used in this paper.

| Symbol          | Meaning                                  |
|-----------------|------------------------------------------|
| $W$             | weighted measure on state                |
| $W_0$           | initial weighted measure                 |
| $B_c$           | critical capacity threshold              |
| `DeliveryModel` | parametric delivery semantics interface  |

No aliases are used for shared notation symbols.

**Definition 1. Productive Step.** For the one-step transition relation $s \to s'$, a step is productive iff $W(s') < W(s)$, where $W$ is Definition 2.

**Definition 2. Weighted Measure.** For a session state, $W = 2 \cdot \Sigma\text{depth} + \Sigma\text{buffer}$. In the mechanization this function is `weightedMeasure`.

The factor two is required for strict decrease on send and select steps where one enqueue occurs. The same definition is used for global lifts and scheduler bounds.

Table 3 lists scheduler profiles used by the bound statements.

| Scheduler profile | Assumption form                                              | Bound class                      |
|-------------------|--------------------------------------------------------------|----------------------------------|
| round-robin       | bounded delay between enabled steps                          | total-step conservative bound    |
| $k$-fair          | each continuously enabled action scheduled within $k$ slots  | total-step conservative bound    |
| adversarial fair  | fairness only                                                | productive-step exact bound only |

## 3. Worked Example

We use one running example with explicit trace witnesses.

**Running Example 3.1 (Quantitative Witness Trace).**
Protocol (as in the first paper):

```text
C -> P : Request(n)
P -> C : Grant(k)
C -> M : Report(k)
M -> P : Confirm
P -> C : Token(t)
```

Let the initial state be $s_0$ with one pending request on edge `(C,P)` and local depths `5`, `5`, and `2` for `P`, `C`, and `M`. Then
$$
W_0 = W(s_0)=2\cdot(5+5+2)+1=25.
$$
Assume the typing/well-formedness judgment `\Gamma \vdash s_0 \ \mathsf{wf}` and step judgments `s_i \to s_{i+1}` for the trace below.

Define witness trace
$$
\tau_{\mathrm{ex}}:\ s_0 \to s_1 \to s_2 \to s_3 \to s_4
$$
with step kinds `recv Request`, `send Grant`, `recv Grant`, `send Report`.

The quantitative facts are used through the following derivation forms.

$$
\dfrac{
  \Gamma \vdash \tau_{\mathrm{ex}}: s_0 \to^\ast s_4
  \quad
  \forall i<4,\ \Delta W(s_i,s_{i+1})=-1
}{
  W(s_4)=W_0-4=21
  \quad\land\quad
  P(\tau_{\mathrm{ex}})=4\le W_0
}
\;(\textsc{Ex-Descent})
$$

$$
\dfrac{
  \mathsf{Profile}(\sigma)
  \quad
  \kappa_\sigma=2
  \quad
  W_0=25
}{
  \forall \tau,\ T(\tau)\le \kappa_\sigma W_0 = 50
}
\;(\textsc{Ex-SchedulerLift})
$$

$$
\dfrac{
  B_c=2
  \quad
  \mathsf{Phase}\ \text{as in Theorem C.3}
}{
  \mathsf{Phase}(1)=\mathsf{Low}
  \quad
  \mathsf{Phase}(2)=\mathsf{Critical}
  \quad
  \mathsf{Phase}(3)=\mathsf{High}
}
\;(\textsc{Ex-PhaseBoundary})
$$

Table 4 records the per-rule $\Delta W$ facts used in this witness.

| Rule instance     |      $\Delta W$ |
|-------------------|----------------:|
| send `Request`    | $-2 + 1 = -1$   |
| receive `Request` | $-1$            |
| send `Grant`      | $-2 + 1 = -1$   |
| receive `Grant`   | $-1$            |

## 4. Theorem 1: Quantitative Dynamics

**Assumption Block 1. Quantitative Descent Premises.** The descent theorem assumes well-typed asynchronous buffered transitions, active-edge Coherence preservation from *Coherence for Asynchronous Buffered MPST*, non-negativity of $W$, and a scheduler profile from Table 3 when total-step lifting is claimed.

**Theorem 1. Quantitative Dynamics.** For any initial state $s_0$ and finite trace $\tau : s_0 \to \cdots \to s_n$ satisfying Assumption Block 1, let $P(\tau)$ be the productive-step count and $T(\tau)$ be the total-step count. Then
$$
P(\tau) \le W(s_0) = W_0.
$$
If the selected scheduler profile provides lift constant $\kappa_\sigma$, then
$$
T(\tau) \le \kappa_\sigma \cdot W_0.
$$
The productive bound is exact under the model assumptions. The scheduler-lifted bound is conservative and profile-dependent.

*Proof sketch.* Define `weightedMeasure = 2*sumDepths + sumBuffers`. First prove rule-local decrease lemmas for send/recv/select/branch (`send_step_decreases`, `recv_step_decreases`, `select_step_decreases`, `branch_step_decreases`). Lift these to the configuration step relation using `total_measure_decreasing`. Since $W\ge 0$ and each productive step decreases $W$ by at least one, productive-step count is bounded by $W_0$. Under a scheduler profile with lift constant $\kappa_\sigma$, apply the scheduler-lift theorem to obtain $T(\tau)\le \kappa_\sigma W_0$. ∎

The local decrease lemmas are `send_step_decreases`, `recv_step_decreases`, `select_step_decreases`, and `branch_step_decreases`. The configuration-level lift is `total_measure_decreasing`.

Figure 2 and Figure 3 summarize the decomposition
$$
W(s)=2\cdot \Sigma\mathrm{depth}(s)+\Sigma\mathrm{buffer}(s),
$$
with per-rule net change bounded by $\Delta W\le -1$ on productive send/recv/select/branch steps.

## 5. Theorem 2: Algorithmic Dynamics Schema

**Assumption Block 2. Regular Finite-Reachability Premises.** The decision schema assumes regularity hypotheses that produce finite reachable-state spaces and predicate reductions expressed by total decision procedures on those spaces.

**Theorem 2. Algorithmic Dynamics Schema.** For any predicate family $\mathcal P$ that satisfies Assumption Block 2, there exists a total decider $\mathsf{dec}_{\mathcal P}$ such that
$$
\forall x,\ \mathsf{dec}_{\mathcal P}(x)=\mathsf{true} \iff \mathcal P(x).
$$
In particular, asynchronous subtyping and regular type equivalence are decidable on the regular fragment.

Coinductive boundary note: effect-level transport is restricted to the witness-carrying rational subclass via `rationalEffect_transport_bridge`; witness-check soundness/completeness is provided by `checkRationalEffectWitness_sound` and `checkRationalEffectWitness_complete`; strict outside non-transportability is witnessed by `strict_boundary_witness_effect`. These do not alter Theorem 2 assumptions and are used in the Paper 3 boundary layer.

*Proof sketch.* The argument is uniform. Build finite reachable triple/pair structures from regularity (`reachable_triples_finite`, `reachablePairs_finite`), run terminating exploration/checkers, and prove soundness/completeness for each reduction. Instantiating this schema yields deciders for async subtyping and regular equivalence (`async_subtype_decidable`, `regularTypeEqDecide_spec`). ∎

Async subtyping instantiation appears through `reachable_triples_finite` and `async_subtype_decidable`. Regular type-equivalence instantiation appears through `regularTypeEqCheck_sound` and `regularTypeEqDecide_spec`.

Figure 4 records the generic workflow: regularity assumptions induce finite exploration; soundness and completeness then yield
$$
\mathsf{dec}_P(x)=\mathsf{true}\ \Longleftrightarrow\ P(x).
$$

## 6. Decidability Layer

**Assumption Block 3. Crash-Stop Characterization Premises.** Crash-tolerance characterization assumes crash-stop faults, finite role graphs, and the residual-graph side conditions used by the decision profile.

**Theorem 3. Crash-Stop Tolerance Characterization.** Under Assumption Block 3, there exists a total decider $\mathsf{decCrash}$ such that
$$
\forall (R,F),\ \mathsf{decCrash}(R,F)=\mathsf{true} \iff \mathsf{CrashTolerant}(R,F).
$$
Moreover crash tolerance satisfies an exact residual-graph characterization:
$$
\mathsf{CrashTolerant}(R,F) \iff \mathsf{ResidualReachable}(R,F).
$$
The theorem also includes witness families where topology changes flip tolerance outcomes within the stated side-condition class.

*Proof sketch.* Construct the residual graph after removing crashed roles and edges, and define `crashTolerantDec` as reachability over that residual object. Soundness is provided by `crashTolerantDec_sound`, which turns a positive decider result into crash tolerance. Completeness and exact characterization come from `crash_tolerance_iff`, and witness families are obtained by topology perturbations that cross the connectivity boundary. ∎

**Assumption Block 4. Byzantine Characterization Premises.** Byzantine characterization assumes explicit bundle $H_{\mathrm{byz}}$ with fault-model, authentication and evidence-validity, conflict-exclusion primitive consistency, and adversarial-budget side conditions.

Define
$$
\mathsf{ByzChar}
\;:=\;
\mathsf{ByzQuorumOK}\ \land\ \mathsf{ByzAuthEvidenceOK}\ \land\ \mathsf{ByzBudgetOK}\ \land\ \mathsf{ByzPrimitiveConsistent},
$$
where each conjunct names the corresponding requirement class in $H_{\mathrm{byz}}$.

**Theorem 4. Exact Byzantine Safety Characterization.** Under Assumption Block 4, profile extraction yields an exact-characterization package for the declared Byzantine model. At this paper interface, the package gives
$$
\mathsf{ByzChar} \Rightarrow \mathsf{ByzSafe},
\qquad
\mathsf{ByzSafe} \Rightarrow \mathsf{ByzChar},
$$
with relative maximality for the same characterization relation.

*Proof sketch.* Fix the Byzantine assumption bundle as a typed profile and apply `byzantineSafety_exact_of_profile` to obtain `ExactByzantineSafetyCharacterization` for the profile model.

1. Pin the Byzantine assumption bundle as a typed profile (`H_byz` components).
2. Project soundness, completeness, and maximality from the extracted exact-characterization object.
3. Interpret soundness and completeness as the two interface implications between $\mathsf{ByzChar}$ and $\mathsf{ByzSafe}$ in this paper's model scope.
4. Record explicit assumption classes for converse sharpness (Corollary 4.1).

The full envelope-maximality development is deferred to Paper 3. ∎

**Corollary 4.1. Converse Counterexample Families.** If any required class in $H_{\mathrm{byz}}$ is dropped, there exists a counterexample family that violates $\mathsf{ByzSafe}$. The dropped classes are quorum or intersection obligations, authentication or evidence-validity obligations, adversarial-budget obligations, and primitive-consistency obligations.

*Proof sketch.* Define one constructor family per dropped assumption class in the Byzantine bundle. Each constructor forces failure of the corresponding profile obligation and induces a safety-visible violation trace. This yields class-indexed converse witnesses and therefore sharpness of Assumption Block 4 at the safety scope stated in this paper. ∎

**Proposition 2. Byzantine VM-Bridge Interface.** If theorem-pack capabilities include Byzantine characterization and VM envelope-adherence evidence, then runtime profile claims are constrained by $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$ under $\mathcal E_{\mathrm{byz}}$, and claims lacking required capability evidence are rejected by profile admission.

*Proof sketch.* The proof proceeds by capability-gated extraction. First, theorem-pack/profile APIs check the Byzantine premise bits required by the profile. Second, admitted profiles are interpreted through the VM Byzantine envelope layer, which gives the safety-visible relation `\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}`. Third, admission and conformance theorems ensure that claims without required evidence are rejected. Thus the interface is executable and proof-carrying. ∎

Core crash-tolerance lemmas include `crash_tolerance_iff` and `crashTolerantDec_sound`. Branching feasibility appears through `branching_iff_chromatic_capacity`.

Table 5 summarizes the decidability results.

| Predicate                         | Method                                                       | Result class           |
|-----------------------------------|--------------------------------------------------------------|------------------------|
| Async subtyping (regular)         | finite reachable triples                                     | decidable              |
| Regular type equivalence          | finite bisimulation checker                                  | decidable              |
| Crash-stop tolerance              | residual graph decider + characterization lemmas             | decidable + iff profile |
| Byzantine safety characterization | assumption-bundle characterization + counterexample families | exact iff profile      |
| Branching feasibility             | confusability and chromatic criterion                        | decidable criterion    |

Table 6 summarizes complexity envelopes for the decision layer.

| Predicate class          | State-space driver                      | Complexity envelope                  |
|--------------------------|-----------------------------------------|--------------------------------------|
| async subtyping          | reachable triples over regular fragment | polynomial in explored graph size    |
| regular type equivalence | finite bisimulation graph               | polynomial in explored graph size    |
| crash-stop tolerance     | residual graph connectivity             | linear or near-linear in graph size  |
| branching feasibility    | confusability graph coloring checks     | polynomial for fixed profile classes |

## 7. Quantitative Corollaries

**Corollary 1. Productive-Step Bound.** For any trace $\tau$ satisfying Assumption Block 1, $P(\tau) \le W_0$.

**Corollary 2. Scheduler-Lifted Total Bound.** For any trace $\tau$ satisfying Assumption Block 1 and scheduler profile $\sigma$ with lift constant $\kappa_\sigma$, $T(\tau) \le \kappa_\sigma \cdot W_0$.

**Corollary 3. Critical Capacity Boundary.** There exists a computable threshold $B_c$ such that the declared phase classifier over buffer capacity is exact at the theorem interface under the stated assumptions.

*Proof sketch.* Corollary 1 is the first clause of Theorem 1 with notation specialized to productive-step count. Instantiating Theorem 1 at the same trace and premises yields the stated inequality directly. ∎

*Proof sketch.* Corollary 2 is the scheduler-lift clause of Theorem 1 with the same premises and profile constant $\kappa_\sigma$. Substituting the selected scheduler profile into that clause yields the stated bound. ∎

*Proof sketch.* `critical_buffer_computable` provides existence of a computable boundary value `B_c`, and `phase_transition_sharp` proves exact classifier behavior on each side of that boundary. Composing these two lemmas yields the stated theorem-level threshold characterization. ∎

Table 7 separates exact and conservative consequences.

| Result                                     | Classification |
|--------------------------------------------|----------------|
| productive-step decrease                   | exact          |
| productive-step bound by $W_0$             | exact          |
| scheduler-lifted total-step bound          | conservative   |
| threshold estimate under scheduler profile | conservative   |

Table 8 gives worked values used in the worked example.

| Quantity                  |     Value |
|---------------------------|----------:|
| $W_0$                     |        25 |
| productive-step bound     | $\leq 25$ |
| 2-fair total-step bound   | $\leq 50$ |
| $B_c$                     |         2 |

Figure 5 locates the worked example on the phase boundary: with $B_c=2$ and $W_0=25$, the instance sits at the critical capacity line, so productive-step and scheduler-lift conclusions apply exactly as in Theorem 1 and Corollaries 1-2.

## 8. Proof Architecture

The architecture has one shared regularity kernel and two proof branches.

- quantitative branch: local-step algebra to strict descent to global bounds
- algorithmic branch: regularity to finite reachability to predicate decisions

This reuse reduces theorem fragmentation and proof duplication. It also gives a direct map from assumptions to output guarantees.

Dependency sketch:
1. Assumption Block 1 gives Theorem 1 and Corollaries 1-2.
2. Assumption Block 2 gives Theorem 2 and the subtyping/equivalence deciders.
3. Assumption Block 3 gives Theorem 3.
4. Assumption Block 4 gives Theorem 4, Corollary 4.1, and Proposition 2.

## 9. Mechanization Summary

Table 9 maps claim families to concrete modules and theorem anchors.

| Layer                                  | Primary modules | Representative anchors |
|----------------------------------------|-----------------|------------------------|
| Weighted dynamics                      | `lean/Runtime/Proofs/WeightedMeasure/Core.lean`, `lean/Runtime/Proofs/WeightedMeasure/TotalBound.lean`, `lean/Runtime/Proofs/Lyapunov.lean`, `lean/Runtime/Proofs/SchedulingBoundCore.lean` | `weightedMeasure`, `send_step_decreases`, `total_measure_decreasing`, `kfair_termination_bound`, `roundrobin_termination_bound` |
| Decision schemas                       | `lean/SessionCoTypes/AsyncSubtyping/Core.lean`, `lean/SessionCoTypes/AsyncSubtyping/Decidable.lean`, `lean/SessionCoTypes/Coinductive/BisimDecidable/Decidable.lean` | `reachable_triples_finite`, `async_subtype_decidable`, `regularTypeEqCheck_sound`, `regularTypeEqDecide_spec` |
| Protocol-level decision and thresholds | `lean/Protocol/CrashTolerance.lean`, `lean/Protocol/SpatialBranching.lean`, `lean/Protocol/BufferBoundedness/PhaseSharpness.lean`, `lean/Protocol/BufferBoundedness/OccupancyDelivery.lean` | `crash_tolerance_iff`, `crashTolerantDec_sound`, `branching_iff_chromatic_capacity`, `phase_transition_sharp`, `critical_buffer_computable` |
| Byzantine profile/VM bridge            | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean`, `lean/Runtime/Proofs/TheoremPack/API.lean`, `lean/Runtime/Proofs/TheoremPack/Profiles.lean` | `byzantineSafety_exact_of_profile`, `Distributed.ByzantineSafety.ExactByzantineSafetyCharacterization`, `vmByzantineEnvelopeAdherence_of_witness`, `byzantineCrossTargetConformance_of_witnesses`, `canOperateUnderByzantineEnvelope` |

**Proposition 1. Mechanization Coverage Soundness.** For any claim class $c$ in Table 9, if $c$ is marked covered and the corresponding Appendix F checks pass, then there exists a mechanized theorem object for $c$ within this paper's assumption scope.

*Proof sketch.* Coverage labels in Table 9 are defined by explicit module-and-theorem anchors. Appendix F rebuild checks certify that these declarations resolve and typecheck under the pinned toolchain. Therefore a passing check witnesses existence of a theorem object for each covered claim class. ∎

## 10. Related Work

Classical MPST work established session foundations and progress lines (Honda et al., 2008). Logical formulations connect sessions and propositions and motivate compositional proof interfaces (Caires and Pfenning, 2010, and Wadler, 2012). Program-logical and mechanized lines expanded the verification space (Hinrichsen et al., 2020, and Tirore, Bengtson, and Carbone, 2025). Event-structure and partial-order approaches give alternate macro views of concurrency (Castellan et al., 2023).

On the quantitative side, our use of descent functions follows the classical drift and stochastic-stability lineage (Lyapunov, 1892; Foster, 1953; Meyn and Tweedie, 2009). On the algorithmic side, the finite-reachability posture follows communicating-automata and model-checking lines (Brand and Zafiropulo, 1983; Baier and Katoen, 2008). Fault-side interfaces are compatible with standard crash and Byzantine theory baselines (Fischer, Lynch, and Paterson, 1985; Chandra and Toueg, 1996; Lamport, Shostak, and Pease, 1982; Castro and Liskov, 1999).

This paper differs in structure. It unifies quantitative bounds and algorithmic decidability through one regularity kernel. The result is a single reusable theorem program instead of isolated predicate proofs.

## 11. Limitations and Scope

Quantitative bounds require the Assumption Block 1 premises: well-typed asynchronous buffered transitions, active-edge Coherence preservation, non-negativity of $W$, and an explicit scheduler profile when total-step lifting is claimed. Scheduler-lifted totals remain conservative profile-dependent bounds rather than exact universal runtime counts.

Crash-stop characterization is exact only under Assumption Block 3, with crash-stop faults, finite role graph, and residual-graph side conditions. Byzantine results are exact safety characterizations only under Assumption Block 4, with $H_{\mathrm{byz}}$ fault-model, authentication and evidence-validity, conflict-exclusion primitive consistency, and adversarial-budget side conditions, and they do not imply Byzantine liveness.

Decidability and finite exploration require the Assumption Block 2 regular finite-reachability premises. Non-regular fragments and stronger adversarial models require different constructions.

Reconfiguration commutation and envelope maximality claims are out of scope for this paper and handled separately in the series.

## 12. Conclusion

This paper turns Coherence-preserving dynamics into computable dynamics. Quantitative bounds and decision procedures come from the same regularity source. That result provides the computational bridge between the Coherence paper and the reconfiguration and envelope claims in the Harmony paper.

Byzantine contribution in this paper is the exact safety-characterization interface and converse counterexample family packaging. Byzantine liveness beyond the stated assumptions remains open and is tracked as future work.

## 13. Works Cited

Baier, C., and Katoen, J.-P. (2008). Principles of Model Checking. MIT Press.

Brand, D., and Zafiropulo, P. (1983). On Communicating Finite-State Machines. Journal of the ACM, 30(2), 323-342.

Caires, L., and Pfenning, F. (2010). Session Types as Intuitionistic Linear Propositions. CONCUR 2010.

Castellan, S., et al. (2023). Event-structure and partial-order semantics for session-based concurrency. Journal of Logic and Algebraic Methods in Programming.

Castro, M., and Liskov, B. (1999). Practical Byzantine Fault Tolerance. OSDI 1999.

Chandra, T. D., and Toueg, S. (1996). Unreliable Failure Detectors for Reliable Distributed Systems. Journal of the ACM, 43(2), 225-267.

Cover, T. M., and Thomas, J. A. (2006). Elements of Information Theory (2nd ed.). Wiley.

Dwork, C., Lynch, N., and Stockmeyer, L. (1988). Consensus in the Presence of Partial Synchrony. Journal of the ACM, 35(2), 288-323.

Fischer, M. J., Lynch, N. A., and Paterson, M. S. (1985). Impossibility of Distributed Consensus with One Faulty Process. Journal of the ACM, 32(2), 374-382.

Foster, F. G. (1953). On the stochastic matrices associated with certain queueing processes. Annals of Mathematical Statistics, 24(3), 355-360.

Hinrichsen, J., et al. (2020). Actris: Session-type based reasoning in separation logic. POPL 2020.

Honda, K., Yoshida, N., and Carbone, M. (2008). Multiparty Asynchronous Session Types. POPL 2008.

Hopcroft, J. E., and Ullman, J. D. (1979). Introduction to Automata Theory, Languages, and Computation. Addison-Wesley.

Karp, R. M., and Miller, R. E. (1969). Parallel Program Schemata. Journal of Computer and System Sciences, 3(2), 147-195.

Lamport, L., Shostak, R., and Pease, M. (1982). The Byzantine Generals Problem. ACM Transactions on Programming Languages and Systems, 4(3), 382-401.

Lynch, N. A. (1996). Distributed Algorithms. Morgan Kaufmann.

Lyapunov, A. M. (1892). The General Problem of the Stability of Motion. Kharkov Mathematical Society.

Meyn, S. P., and Tweedie, R. L. (2009). Markov Chains and Stochastic Stability (2nd ed.). Cambridge University Press.

Shannon, C. E. (1948). A Mathematical Theory of Communication. Bell System Technical Journal, 27(3), 379-423 and 27(4), 623-656.

Tirore, L., Bengtson, J., and Carbone, M. (2025). Mechanized MPST metatheory with subject-reduction robustness analysis. ECOOP 2025.

Wadler, P. (2012). Propositions as Sessions. ICFP 2012.

## Appendices

## Appendix A. Deferred Quantitative Proofs

This appendix expands Theorem 1 and Corollaries 1-2.

### A.1 Weighted Potential and Productive Steps

For local state `s`, define:

```text
W(s) := 2 * sumDepths(s) + sumBuffers(s)
```

For global configuration `C`, write `W(C)` for the sum of local/session contributions. A step is productive iff it decreases `W` strictly.

### A.2 Rule-Level Decrease

**Lemma A.1. Send/Select Decrease.** For productive send/select steps, `Delta W <= -1`.

*Proof sketch.* Unfold the weighted measure into depth and buffer components. A productive send or select step consumes one protocol constructor, contributing `-2` to depth, and enqueues at most one message, contributing `+1` to buffers. Summing contributions gives `\Delta W \le -1`. ∎

**Lemma A.2. Recv/Branch Decrease.** For productive recv/branch steps, `Delta W <= -1`.

*Proof sketch.* For productive recv and branch steps, one buffered head is consumed and no new message is enqueued on that edge. Unfolding the weighted accounting shows a strict negative contribution from the consumed buffer and continuation progress. Therefore `\Delta W \le -1`. ∎

**Lemma A.3. Configuration Lift.** Rule-level decreases lift to the global step relation:

```text
productiveStep C C' -> W(C') <= W(C) - 1
```

*Proof sketch.* Decompose the global step into updated and untouched local components. Apply Lemma A.1 or Lemma A.2 on updated components and use zero change on untouched components. Summing all contributions yields `productiveStep C C' -> W(C') <= W(C) - 1`. ∎

### A.3 Trace Bounds

**Proposition A.4 (Productive-Step Bound).** For any finite trace from $C_0$, productive-step count $P$ satisfies $P \le W(C_0)$.

*Proof sketch.* Index productive positions in the trace and apply Lemma A.3 at each such index. Summing inequalities telescopes to `W(C_0) - W(C_n) \ge P`, where `P` is productive-step count. Since `W(C_n) \ge 0`, we conclude `P \le W(C_0)`. ∎

**Proposition A.5 (Scheduler-Lifted Total Bound).** If scheduler profile $\sigma$ admits lift constant $\kappa_\sigma$, then total steps $T$ satisfy:

$$
T \le \kappa_\sigma \cdot W(C_0).
$$

*Proof sketch.* Proposition A.4 bounds the number of productive steps by $W(C_0)$. The scheduler profile contributes a bound on how many non-productive steps can occur between productive ones. Multiplying these bounds gives $T \le \kappa_\sigma \cdot W(C_0)$. ∎

Theorem 1 and Corollaries 1-2 are exactly Propositions A.4-A.5 under Assumption Block 1.

## Appendix B. Deferred Proof of Algorithmic Decidability Schema

### B.1 Abstract Schema

Let `P` be a predicate over inputs `x`. Assume:

1. a finite reachable structure `Reach(x)`,
2. a terminating checker `check(x)` over `Reach(x)`,
3. soundness/completeness:

```text
check(x) = true  <->  P(x)
```

**Theorem B.1 (Generic Decider Transfer).** Under the three assumptions above, `P` is decidable.

*Proof sketch.* Finiteness of `Reach(x)` ensures that exploration terminates. The soundness and completeness hypotheses identify `check(x)` with truth of `P(x)`. Therefore the checker is a total decision procedure for `P`. ∎

### B.2 Complexity Envelope (Schema Level)

Let `N(x)` be size of the finite reachable object. If `check` runs in `poly(N(x))`, then decision complexity is `poly(N(x))`.

This explains why the paper reports complexity in explored-graph size, not in raw syntax size.

### B.3 Instantiations

1. Async subtyping: reachable triple graph (`reachable_triples_finite`, `async_subtype_decidable`).
2. Regular equivalence: reachable pair/bisim graph (`regularTypeEqCheck_sound`, `regularTypeEqDecide_spec`).

## Appendix C. Instantiated Decision Theorems

### C.1 Crash-Stop Tolerance Instantiation

Given role graph `R` and crash set `F`, let `Residual(R,F)` remove crashed roles and incident edges.

**Theorem C.1 (Crash-Stop Exactness).**

```text
CrashTolerant(R,F)  <->  ResidualReachable(R,F)
```

*Proof sketch.* For soundness, if the residual graph is disconnected then at least one required communication path is cut, so crash tolerance fails. For completeness, residual reachability gives continuation witnesses for all required communication obligations in the crash-stop model. Combining both directions yields the claimed equivalence. ∎

### C.2 Branching Feasibility Instantiation

Let `ConfGraph` be the confusability graph induced by branch-distinguishability constraints.

**Theorem C.2 (Branching Feasibility Criterion).** Feasibility holds iff the declared chromatic-capacity condition on `ConfGraph` holds.

*Proof sketch.* Encode branch distinguishability constraints as coloring constraints on `ConfGraph`. The profile fixes admissible class counts, so feasibility reduces to existence of a coloring within that bound. The equivalence follows by bidirectional translation between branch witnesses and valid colorings. ∎

### C.3 Capacity Threshold Instantiation

Define the phase classifier
$$
\mathsf{Phase}(B)=
\begin{cases}
\mathsf{Low}, & B < B_c,\\
\mathsf{Critical}, & B = B_c,\\
\mathsf{High}, & B > B_c.
\end{cases}
$$

**Theorem C.3 (Sharp Capacity Boundary).** There exists a computable threshold $B_c$ such that
$$
\forall B,\ \big(B < B_c \Rightarrow \mathsf{Phase}(B)=\mathsf{Low}\big)\ \land\ \big(B = B_c \Rightarrow \mathsf{Phase}(B)=\mathsf{Critical}\big)\ \land\ \big(B > B_c \Rightarrow \mathsf{Phase}(B)=\mathsf{High}\big),
$$
with exactness at the theorem interface.

*Proof sketch.* `critical_buffer_computable` yields a computable candidate threshold. `phase_transition_sharp` proves that the classifier is exact below, at, and above this threshold. Therefore the phase boundary is both computable and sharp. ∎

### C.4 Byzantine Safety Interface (Scope of This Paper)

Under Assumption Block 4, this paper provides the exact safety-side interface and converse counterexample packaging; full envelope maximality and transport are deferred to Paper 3.

## Appendix D. Mechanization Map

| Result family | Primary modules | Representative theorem anchors |
|---------------|------------------|--------------------------------|
| Quantitative dynamics and scheduler lift | `lean/Runtime/Proofs/WeightedMeasure/*.lean`, `lean/Runtime/Proofs/Lyapunov.lean`, `lean/Runtime/Proofs/SchedulingBoundCore.lean` | `weightedMeasure`, `total_measure_decreasing`, `kfair_termination_bound`, `roundrobin_termination_bound` |
| Decidability schema and instances | `lean/SessionCoTypes/AsyncSubtyping/*.lean`, `lean/SessionCoTypes/Coinductive/BisimDecidable/*.lean` | `reachable_triples_finite`, `async_subtype_decidable`, `regularTypeEqDecide_spec` |
| Crash/branching/threshold instantiations | `lean/Protocol/CrashTolerance.lean`, `lean/Protocol/SpatialBranching.lean`, `lean/Protocol/BufferBoundedness/PhaseSharpness.lean` | `crash_tolerance_iff`, `branching_iff_chromatic_capacity`, `phase_transition_sharp`, `critical_buffer_computable` |
| Byzantine profile and runtime bridge | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems*.lean`, `lean/Runtime/Proofs/TheoremPack/*.lean` | `byzantineSafety_exact_of_profile`, `vmByzantineEnvelopeAdherence_of_witness` |

## Appendix E. Exactness and Boundary Notes

### E.1 Exact Claims

1. Productive-step decrease and productive-step bounds (Assumption Block 1).
2. Crash-stop characterization (Assumption Block 3).
3. Byzantine safety characterization at paper interface scope (Assumption Block 4).

### E.2 Conservative or Profile-Indexed Claims

1. Scheduler-lifted total-step bounds ($\kappa_\sigma$-indexed).
2. Complexity bounds parameterized by explored finite-state size.
3. Capacity-boundary reporting when profile assumptions fix classifier semantics.

### E.3 Out-of-Scope Boundaries

1. Non-regular fragments for decision transfer.
2. Byzantine liveness under weaker timing/adversary assumptions.
3. Reconfiguration commutation and envelope maximality (Paper 3).

## Appendix F. Reproducibility

Reproduction uses the pinned Lean toolchain and manifest.

1. Build module families listed in Appendix D.
2. Run `just escape` and `just verify-protocols`.
3. Confirm Appendix-D theorem anchors resolve and typecheck.

Expected checks:

Finite-reachability and decision modules compile, weighted-measure descent and scheduler modules compile, crash and branching and threshold modules compile, and theorem-pack and profile-bridge modules compile.

## Appendix G. Index of Main Results

| Claim | Main section | Assumption scope | Formal location |
|-------|--------------|------------------|-----------------|
| Theorem 1. Quantitative Dynamics | Section 4 | Assumption Block 1 quantitative descent premises | `lean/Runtime/Proofs/WeightedMeasure/TotalBound.lean`, `lean/Runtime/Proofs/SchedulingBoundCore.lean`; Appendix A |
| Theorem 2. Algorithmic Dynamics Schema | Section 5 | Assumption Block 2 regular finite-reachability premises | `lean/SessionCoTypes/AsyncSubtyping/*.lean`, `lean/SessionCoTypes/Coinductive/BisimDecidable/*.lean`; Appendix B |
| Theorem 3. Crash-Stop Tolerance Characterization | Section 6 | Assumption Block 3 crash-stop premises | `lean/Protocol/CrashTolerance.lean`; Appendix C |
| Theorem 4. Exact Byzantine Safety Characterization | Section 6 | Assumption Block 4 Byzantine premises | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean` (`byzantineSafety_exact_of_profile`), `lean/Distributed/Families/ByzantineSafety/Core/Base.lean` (`ExactByzantineSafetyCharacterization`); Appendix C |
| Corollary 4.1. Converse Counterexample Families | Section 6 | Theorem 4 premises + dropped-assumption witness classes | Section 6 packaging + Appendix C |
| Corollary 1. Productive-Step Bound | Section 7 | Theorem 1 premises | derived in Section 7; Appendix A |
| Corollary 2. Scheduler-Lifted Total Bound | Section 7 | Theorem 1 premises + scheduler profile premises | derived in Section 7; Appendix A and E |
| Corollary 3. Critical Capacity Boundary | Section 7 | regular fragment + threshold side conditions | `lean/Protocol/BufferBoundedness/PhaseSharpness.lean`; Appendix C and E |
| Proposition 2. Byzantine VM-Bridge Interface | Section 6 | theorem-pack capability and adherence premises | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean`, `lean/Runtime/Proofs/TheoremPack/API.lean`, `lean/Runtime/Proofs/TheoremPack/Profiles.lean`; Appendix C and D |
| Proposition 1. Mechanization Coverage Soundness | Section 9 | reproducibility checks under Appendix F workflow | Section 9 argument + Appendix D and F |
