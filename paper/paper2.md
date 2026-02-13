# Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures

## Abstract

We prove that quotient dynamics for asynchronous MPST are computable in two coordinated senses. The first is quantitative and uses a weighted Lyapunov measure. The second is algorithmic and uses finite-reachability decision schemas over regular fragments.

The weighted measure is $W = 2 \cdot \Sigma\text{depth} + \Sigma\text{buffer}$. Productive steps strictly decrease $W$, which yields explicit productive-step bounds and scheduler-lifted total-step bounds under stated assumptions. Finite-reachability schemas then yield decidability for asynchronous subtyping, regular type equivalence, crash-stop tolerance, and branching feasibility.

All core claims are mechanized in Lean 4. This paper builds directly on *Coherence for Asynchronous Buffered MPST* and provides the quantitative and decision layer used by *Harmony from Coherence in Asynchronous MPST*.

## 1. Introduction

The preceding manuscript establishes Coherence as the local invariant kernel. This paper studies what can be computed from that kernel at runtime and analysis time.

The contribution has two parts. One part gives explicit quantitative bounds. The second part gives uniform decidability transfer through one finite-state schema.

The quantitative branch uses a classical Lyapunov template from stability theory (Lyapunov, 1892). The method chooses a nonnegative potential and proves strict decrease under productive transitions. In stochastic-process terms, this aligns with Foster-style drift arguments that lift local decrease to global stability-style conclusions (Foster, 1953). The weighted measure $W$ in this paper is the protocol-level potential for that template.

Here the Lyapunov potential is an energy-like ranking function on states, not physical energy. The core proof pattern is nonnegative potential plus strict decrease on productive steps, which yields bounded productive progress.

The scheduler assumptions play the role of a drift condition. Under a declared fairness profile, productive decrease has an expected directional effect along traces, which is what justifies lifting local decrease to conservative total-step bounds.

The algorithmic branch follows a standard regularity-to-decidability strategy from finite-state analysis. Regularity assumptions are used to bound reachable structure, then one terminating exploration yields decision procedures by soundness and completeness transfer. What is new here is a single reusable schema that instantiates to asynchronous subtyping, regular equivalence, crash tolerance, and branching feasibility without changing the core proof pattern.

Capacity thresholds follow a standard phase-boundary intuition in buffered and queue-like systems, where behavior classes change when load or backlog crosses a boundary. The standard point is qualitative phase separation between safe and unstable regions. What is new here is a theorem-level threshold boundary $B_c$ with an exact interface-level characterization under explicit MPST assumptions.

Operationally, $B_c$ is a regime split. Below $B_c$ one behavior class is admitted by the theorem profile. Above $B_c$ a different class appears and may require stronger conditions. The boundary statement is exact under the paper's assumptions.

An information-theoretic view helps interpret the decision layer. Regularity hypotheses induce finite summaries that preserve exactly the predicates this paper decides, which is a sufficiency claim rather than heuristic compression (Cover and Thomas, 2006). In that sense the finite exploration graph is an analysis channel with no decision loss for the targeted properties.

The paper presents a single regularity-driven method that generates both numeric and algorithmic claims.

Dependency across the three papers is explicit. *Coherence for Asynchronous Buffered MPST* supplies the invariant kernel, this paper supplies computable dynamics and decision procedures, and *Harmony from Coherence in Asynchronous MPST* lifts these components to reconfiguration and envelope theorems.

Scope is restricted to regular finite-reachability fragments for decision claims and explicit scheduler profiles for total-step bounds. Fault claims in this paper include crash-stop exactness and an explicit Byzantine safety characterization under a separate assumption bundle $H_{\mathrm{byz}}$. Reconfiguration commutation and determinism-envelope maximality are deferred to *Harmony from Coherence in Asynchronous MPST*.

Our contributions are as follows:

1. A quantitative descent theorem with explicit productive-step and scheduler-lifted total-step bounds from one weighted measure.
2. A uniform algorithmic schema that turns regular finite reachability into reusable decidability procedures.
3. A crash-stop tolerance characterization with decision and residual-graph exactness under stated side conditions.
4. A Byzantine safety characterization interface with exact iff form, converse counterexample families, and VM-bridge handoff obligations.
5. A mechanized architecture that shares one regularity kernel across quantitative and algorithmic branches.

Related liveness lines often emphasize qualitative progress in session-typed settings (Honda et al., 2008, and Caires and Pfenning, 2010). Related mechanized lines expose proof brittleness and motivate reusable proof architecture (Tirore, Bengtson, and Carbone, 2025). Figure 1 summarizes the two-branch architecture.

Figure 1. Two-branch theorem architecture. A shared regularity kernel generates quantitative and algorithmic results.

```text
                Shared regularity kernel
      (finite-reachability + Coherence-preserving semantics)
                           |
          +----------------+----------------+
          |                                 |
Quantitative branch                   Algorithmic branch
  weighted measure W                    finite exploration
  per-step decrease                     sound/complete deciders
  productive-step bound                 predicate instantiations
  scheduler lift                        (subtyping/equivalence/crash/branching)
```

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

**Definition 1. Productive Step.** A productive step is a step that strictly decreases the progress state under the weighted measure used in this paper.

**Definition 2. Weighted Measure.** For a session state, $W = 2 \cdot \Sigma\text{depth} + \Sigma\text{buffer}$. The implementation artifact is `weightedMeasure`.

The factor two is required for strict decrease on send and select steps where one enqueue occurs. The same definition is used for global lifts and scheduler bounds.

Table 3 lists scheduler profiles used by the bound statements.

| Scheduler profile | Assumption form                                              | Bound class                      |
|-------------------|--------------------------------------------------------------|----------------------------------|
| round-robin       | bounded delay between enabled steps                          | total-step conservative bound    |
| $k$-fair          | each continuously enabled action scheduled within $k$ slots  | total-step conservative bound    |
| adversarial fair  | fairness only                                                | productive-step exact bound only |

## 3. Worked Example

The worked example is the single-pool capacity protocol from *Coherence for Asynchronous Buffered MPST*.

```text
C -> P : Request(n)
P -> C : Grant(k)
C -> M : Report(k)
M -> P : Confirm
P -> C : Token(t)
```

The initial worked state has depths `5`, `5`, and `2` for roles `P`, `C`, and `M`. One pending request appears on edge `(C,P)`. This gives $W_0 = 2 \cdot (5 + 5 + 2) + 1 = 25$.

The example is reused in all theorem sections. It gives concrete values for bounds, scheduler lifts, and threshold interpretation.

Table 4 gives the per-rule $\Delta W$ profile used in Theorem 1.

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

*Proof sketch.* The proof has two levels. Level one proves per-rule decrease lemmas for send, recv, select, and branch. Level two lifts local decrease to configuration-level decrease and then to trace bounds using non-negativity. ∎

Expanded derivation structure:

1. Define `weightedMeasure = 2*sumDepths + sumBuffers`.
2. Prove rule-local inequalities:
   - `send_step_decreases`,
   - `recv_step_decreases`,
   - `select_step_decreases`,
   - `branch_step_decreases`.
3. Lift rule-local decreases to system-level decrease:
   - `total_measure_decreasing`.
4. Use non-negativity to bound productive steps:
   - each productive step decreases `W` by at least 1,
   - therefore productive-step count is at most `W0`.
5. Apply scheduler-lift theorem for declared fairness profile:
   - obtain `T(τ) ≤ κσ * W0`,
   - classify this bound as conservative (profile-dependent).

The local decrease artifacts are `send_step_decreases`, `recv_step_decreases`, `select_step_decreases`, and `branch_step_decreases`. The configuration-level lift is `total_measure_decreasing`.

Figure 2 shows the weighted decomposition. Figure 3 shows per-rule $\Delta W$ profiles.

Figure 2. Weighted measure decomposition. The figure separates depth and buffer contributions.

```text
W(state) = 2 * sumDepths(state) + sumBuffers(state)

Depth term:
  decreases when local type head is consumed/advanced

Buffer term:
  +1 on enqueue-like steps, -1 on dequeue-like steps

Why coefficient 2:
  send/select may do {depth -1, buffer +1}
  so net change stays <= -1 after weighting
```

Figure 3. Per-rule decrease profile. The figure reports signed contributions for send, recv, select, and branch.

```text
Rule class      Depth delta   Buffer delta   Net delta in W
send            -2            +1             -1
recv             0            -1             -1
select          -2            +1             -1
branch           0            -1             -1

All productive rules satisfy ΔW <= -1.
```

## 5. Theorem 2: Algorithmic Dynamics Schema

**Assumption Block 2. Regular Finite-Reachability Premises.** The decision schema assumes regularity hypotheses that produce finite reachable-state spaces and predicate reductions expressed by total decision procedures on those spaces.

**Theorem 2. Algorithmic Dynamics Schema.** For any predicate family $\mathcal P$ that satisfies Assumption Block 2, there exists a total decider $\mathsf{dec}_{\mathcal P}$ such that
$$
\forall x,\ \mathsf{dec}_{\mathcal P}(x)=\mathsf{true} \iff \mathcal P(x).
$$
In particular, asynchronous subtyping and regular type equivalence are decidable on the regular fragment.

Coinductive boundary note (artifact-level): effect-level transport is restricted to the witness-carrying rational subclass via `rationalEffect_transport_bridge`; witness-check soundness/completeness is provided by `checkRationalEffectWitness_sound` and `checkRationalEffectWitness_complete`; strict outside non-transportability is witnessed by `strict_boundary_witness_effect`. These do not alter Theorem 2 assumptions and are consumed by the Paper 3 boundary layer.

*Proof sketch.* The argument is uniform. First construct a finite reachable-state space from regularity. Next run terminating exploration on this space. Last prove soundness and completeness for each predicate-specific reduction. ∎

Expanded derivation structure:

1. Reachability finiteness:
   - build reachable triple/pair sets from regularity hypotheses,
   - prove finite bounds (`reachable_triples_finite`, `reachablePairs_finite`).
2. Executable exploration:
   - construct exploration state and fuel discipline (`explore`, `checkAsync`, checker APIs).
3. Predicate reduction:
   - map each target predicate to a reachability or bisimulation checker.
4. Correctness transfer:
   - prove soundness and completeness of each checker,
   - package resulting decider theorem.
5. Instantiation:
   - async subtyping and regular equivalence follow as direct corollaries.

Async subtyping instantiation appears through `reachable_triples_finite` and `async_subtype_decidable`. Regular type-equivalence instantiation appears through `regularTypeEqCheck_sound` and `regularTypeEqDecide_spec`.

Figure 4 presents the decision workflow used by all instantiations.

Figure 4. Uniform decision workflow. The figure maps regularity assumptions to finite exploration and final decision output.

```text
Regularity assumptions
    |
finite reachable state construction
    |
terminating exploration/checker
    |
soundness + completeness
    |
Decider:
  dec_P(x) = true  <->  P(x)
```

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

*Proof sketch.* Decision is provided by a graph-level decider and a soundness theorem. Characterization follows from residual reachability lemmas and completeness assumptions in the model profile. ∎

Expanded derivation structure:

1. Build communication graph and residual graph after crash set removal.
2. Define Boolean decider `crashTolerantDec`.
3. Prove decider soundness (`crashTolerantDec_sound`).
4. Prove exact characterization (`crash_tolerance_iff`):
   - crash tolerance iff residual connectivity.
5. Export witness families showing topology-sensitive flips in tolerance outcomes under admissible changes.

**Assumption Block 4. Byzantine Characterization Premises.** Byzantine characterization assumes explicit bundle $H_{\mathrm{byz}}$ with fault-model, authentication and evidence-validity, conflict-exclusion primitive consistency, and adversarial-budget side conditions.

**Theorem 4. Exact Byzantine Safety Characterization.** Under Assumption Block 4, there exists a characterization predicate $\mathsf{ByzChar}$ such that
$$
\mathsf{ByzSafe} \iff \mathsf{ByzChar}.
$$
The statement is exact in the model scope of this paper.

*Proof sketch.* This theorem is an interface-level exactness package at Paper 2 scope.

1. Pin the Byzantine assumption bundle as a typed profile (`H_byz` components).
2. Use profile extraction theorems to obtain safety-side implications from passed assumptions.
3. Package both directions at the interface boundary:
   - soundness: assumptions imply safety characterization conditions,
   - completeness: characterization obligations reconstitute safety-visible guarantees in the model scope.
4. Record explicit assumption classes for converse sharpness (Corollary 4.1).

The full cross-layer envelope maximality program is outside Paper 2 and consumed by the later reconfiguration/envelope paper. ∎

**Corollary 4.1. Converse Counterexample Families.** If any required class in $H_{\mathrm{byz}}$ is dropped, there exists a counterexample family that violates $\mathsf{ByzSafe}$. The dropped classes are quorum or intersection obligations, authentication or evidence-validity obligations, adversarial-budget obligations, and primitive-consistency obligations.

*Proof sketch.* Counterexample constructors are indexed by dropped assumption class. For each class, the corresponding profile bit fails and a violating family is produced at the safety-visible interface. This establishes sharpness of the assumption bundle at the paper’s safety scope. ∎

**Proposition 2. Byzantine VM-Bridge Interface.** If theorem-pack capabilities include Byzantine characterization and VM envelope-adherence artifacts, then runtime profile claims are constrained by $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$ under $\mathcal E_{\mathrm{byz}}$, and claims lacking required capability evidence are rejected by profile admission.

*Proof sketch.* The bridge follows capability-gated extraction:

1. Byzantine profile assumptions are checked in theorem-pack/profile APIs.
2. Safety-visible equalities are interpreted via the VM Byzantine envelope layer.
3. Admission and conformance theorems enforce that only capability-backed claims pass profile checks.

Thus the bridge is executable and checkable at the profile interface in this paper. ∎

Core crash-tolerance artifacts include `crash_tolerance_iff` and `crashTolerantDec_sound`. Branching feasibility appears through `branching_iff_chromatic_capacity`.

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

The threshold line is implemented in the buffer-boundedness layer. Representative artifacts include `phase_transition_sharp` and `critical_buffer_computable`.

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

Figure 5 locates the worked example on the phase boundary view.

Figure 5. Capacity threshold view. The figure places the worked example relative to the bounded and bounded-stuck regions.

```text
                buffer-capacity axis B
   unbounded / unstable        |         bounded regime
                               |
-------------------------------+---------------------------->
                              Bc = 2

Worked point:
  protocol instance at B = 2 sits on the critical boundary
  with W0 = 25 and profile-dependent total-step lift.
```

## 8. Proof Architecture

The architecture has one shared regularity kernel and two proof branches.

- quantitative branch: local-step algebra to strict descent to global bounds
- algorithmic branch: regularity to finite reachability to predicate decisions

This reuse reduces theorem fragmentation and proof duplication. It also gives a direct map from assumptions to output guarantees.

Dependency sketch:

```text
Assumption Block 0
   +-- Block 1 -> Theorem 1 -> Corollaries 1,2
   +-- Block 2 -> Theorem 2 -> subtyping/equivalence decisions
   +-- Block 3 -> Theorem 3 -> crash-stop exact characterization
   +-- Block 4 -> Theorem 4 + Corollary 4.1 + Proposition 2
```

## 9. Mechanization and Artifacts

Table 9 maps claim families to concrete modules and theorem anchors.

| Layer                                  | Primary modules | Representative anchors |
|----------------------------------------|-----------------|------------------------|
| Weighted dynamics                      | `lean/Runtime/Proofs/WeightedMeasure/Core.lean`, `lean/Runtime/Proofs/WeightedMeasure/TotalBound.lean`, `lean/Runtime/Proofs/Lyapunov.lean`, `lean/Runtime/Proofs/SchedulingBoundCore.lean` | `weightedMeasure`, `send_step_decreases`, `total_measure_decreasing`, `kfair_termination_bound`, `roundrobin_termination_bound` |
| Decision schemas                       | `lean/SessionCoTypes/AsyncSubtyping/Core.lean`, `lean/SessionCoTypes/AsyncSubtyping/Decidable.lean`, `lean/SessionCoTypes/Coinductive/BisimDecidable/Decidable.lean` | `reachable_triples_finite`, `async_subtype_decidable`, `regularTypeEqCheck_sound`, `regularTypeEqDecide_spec` |
| Protocol-level decision and thresholds | `lean/Protocol/CrashTolerance.lean`, `lean/Protocol/SpatialBranching.lean`, `lean/Protocol/BufferBoundedness/PhaseSharpness.lean`, `lean/Protocol/BufferBoundedness/OccupancyDelivery.lean` | `crash_tolerance_iff`, `crashTolerantDec_sound`, `branching_iff_chromatic_capacity`, `phase_transition_sharp`, `critical_buffer_computable` |
| Byzantine profile/VM bridge            | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems.lean`, `lean/Runtime/Proofs/TheoremPack/API.lean`, `lean/Runtime/Proofs/TheoremPack/Profiles.lean` | `byzantineSafety_exact_of_profile`, `vmByzantineEnvelopeAdherence_of_witness`, `byzantineCrossTargetConformance_of_witnesses`, `canOperateUnderByzantineEnvelope` |

**Proposition 1. Artifact Soundness Boundary.** For any claim class $c$ in Table 9, if $c$ is marked covered and artifact checks for $c$ pass under Appendix F workflow, then there exists a mechanized theorem artifact for $c$ within this paper's stated assumption scope.

## 10. Related Work

Classical MPST work established session foundations and progress lines (Honda et al., 2008). Logical formulations connect sessions and propositions and motivate compositional proof interfaces (Caires and Pfenning, 2010, and Wadler, 2012). Program-logical and mechanized lines expanded the verification space (Hinrichsen et al., 2020, and Tirore, Bengtson, and Carbone, 2025). Event-structure and partial-order approaches give alternate macro views of concurrency (Castellan et al., 2023).

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

Caires, L., and Pfenning, F. (2010). Session Types as Intuitionistic Linear Propositions. CONCUR 2010.

Castellan, S., et al. (2023). Event-structure and partial-order semantics for session-based concurrency. Journal of Logic and Algebraic Methods in Programming.

Cover, T. M., and Thomas, J. A. (2006). Elements of Information Theory (2nd ed.). Wiley.

Foster, F. G. (1953). On the stochastic matrices associated with certain queueing processes. Annals of Mathematical Statistics, 24(3), 355-360.

Hinrichsen, J., et al. (2020). Actris: Session-type based reasoning in separation logic. POPL 2020.

Honda, K., Yoshida, N., and Carbone, M. (2008). Multiparty Asynchronous Session Types. POPL 2008.

Lyapunov, A. M. (1892). The General Problem of the Stability of Motion. Kharkov Mathematical Society.

Shannon, C. E. (1948). A Mathematical Theory of Communication. Bell System Technical Journal, 27(3), 379-423 and 27(4), 623-656.

Tirore, L., Bengtson, J., and Carbone, M. (2025). Mechanized MPST metatheory with subject-reduction robustness analysis. ECOOP 2025.

Wadler, P. (2012). Propositions as Sessions. ICFP 2012.

## Appendices

## Appendix A. Deferred Quantitative Proofs

### A.1 Weighted Potential

The quantitative layer is based on:

```text
W(s) = 2 * sumDepths(s) + sumBuffers(s)
```

and its lifted form over global configurations.

### A.2 Rule-Level Decrease and Configuration Lift

**Lemma A.1 (Rule-Level Decrease).** Each productive transition class (send, recv, select, branch) strictly decreases `W` by at least one.

**Lemma A.2 (Configuration Lift).** Rule-level decrease lifts to the configuration step relation (`total_measure_decreasing`).

### A.3 Global Bounds

**Proposition A.3 (Productive-Step Bound).** Under Assumption Block 1, productive-step count is bounded by `W0`.

**Proposition A.4 (Scheduler-Lifted Total Bound).** Under scheduler profile `sigma`, total-step count is bounded by `kappa_sigma * W0`.

Theorem 1 and Corollaries 1-2 follow from A.1-A.4.

## Appendix B. Deferred Proof of Algorithmic Decidability Schema

### B.1 Generic Decider Transfer

The schema requires:

1. a finite reachable-state presentation,
2. a terminating exploration/checker,
3. soundness and completeness of that checker.

**Theorem B.1 (Generic Decider Transfer).** If predicate `P` admits the three obligations above, then `P` is decidable.

*Proof sketch.* Finite exploration terminates by construction; soundness/completeness identify checker output with `P`; hence membership in `P` is decidable.

### B.2 Instantiations Used in the Main Text

Async subtyping is instantiated by the reachable triple graph; regular equivalence by the reachable pair/bisim graph over regular representatives.

## Appendix C. Instantiated Decision Theorems

### C.1 Crash-Stop Tolerance

Exact criterion: crash tolerance holds iff residual communication connectivity holds in the declared crash-stop model.

### C.2 Branching Feasibility

Feasibility is characterized by the confusability/chromatic-capacity condition in the stated fragment.

### C.3 Capacity Threshold

The phase classifier has a sharp boundary with computable critical threshold `Bc`.

### C.4 Byzantine Safety Interface (Scope of This Paper)

This paper proves exact safety-side characterization under the declared Byzantine profile bundle, plus converse counterexample packaging when assumption classes are dropped.

## Appendix D. Mechanization Map

| Result family | Primary modules |
|---------------|-----------------|
| Quantitative dynamics and scheduler lift | `lean/Runtime/Proofs/WeightedMeasure/*.lean`, `lean/Runtime/Proofs/Lyapunov.lean`, `lean/Runtime/Proofs/SchedulingBoundCore.lean` |
| Decidability schema and instances | `lean/SessionCoTypes/AsyncSubtyping/*.lean`, `lean/SessionCoTypes/Coinductive/BisimDecidable/*.lean` |
| Crash/branching/threshold instantiations | `lean/Protocol/CrashTolerance.lean`, `lean/Protocol/SpatialBranching.lean`, `lean/Protocol/BufferBoundedness/PhaseSharpness.lean` |
| Byzantine profile and runtime bridge | `lean/Runtime/Proofs/Adapters/Distributed/EnvelopeTheorems*.lean`, `lean/Runtime/Proofs/TheoremPack/*.lean` |

## Appendix E. Exactness and Boundary Notes

1. Productive-step decrease and productive-step bounds are exact under Assumption Block 1.
2. Scheduler-lifted total bounds are profile-indexed upper bounds.
3. Crash-stop exactness is scoped to Assumption Block 3.
4. Byzantine exactness in this paper is safety-side and assumption-bundle scoped.
5. Decidability transfer depends on regular finite-reachability assumptions.

## Appendix F. Reproducibility

Reproduction uses the pinned Lean toolchain and manifest. Build the module families in Appendix D; run `just escape` and `just verify-protocols` for project-level consistency checks.

## Appendix G. Index of Main Results

| Claim | Main section | Assumption scope | Formal location |
|-------|--------------|------------------|-----------------|
| Theorem 1. Quantitative Dynamics | Section 4 | Assumption Block 1 quantitative descent premises | `WeightedMeasure/TotalBound.lean`, `SchedulingBoundCore.lean`; Appendix A |
| Theorem 2. Algorithmic Dynamics Schema | Section 5 | Assumption Block 2 regular finite-reachability premises | `AsyncSubtyping/*.lean`, `BisimDecidable/*.lean`; Appendix B |
| Theorem 3. Crash-Stop Tolerance Characterization | Section 6 | Assumption Block 3 crash-stop premises | `Protocol/CrashTolerance.lean`; Appendix C |
| Theorem 4. Exact Byzantine Safety Characterization | Section 6 | Assumption Block 4 Byzantine premises | Byzantine profile extraction modules; Appendix C |
| Corollary 4.1. Converse Counterexample Families | Section 6 | Theorem 4 premises + dropped-assumption witness classes | Section 6 packaging + Appendix C |
| Corollary 1. Productive-Step Bound | Section 7 | Theorem 1 premises | derived in Section 7; Appendix A |
| Corollary 2. Scheduler-Lifted Total Bound | Section 7 | Theorem 1 premises + scheduler profile premises | derived in Section 7; Appendix A and E |
| Corollary 3. Critical Capacity Boundary | Section 7 | regular fragment + threshold side conditions | `PhaseSharpness.lean`; Appendix C and E |
| Proposition 2. Byzantine VM-Bridge Interface | Section 6 | theorem-pack capability and adherence premises | theorem-pack/profile modules; Appendix C and D |
| Proposition 1. Artifact Soundness Boundary | Section 9 | artifact checks under reproducibility workflow | Section 9 argument + Appendix D and F |
