# Harmony from Coherence in Asynchronous MPST: A Minimal Erasure Invariant for Classical Dynamics

[Paper](paper3.md)

## One-Paragraph Thesis
For well-formed reconfiguration (`link` or delegation) and subsequent enabled protocol steps, projection commutes with evolution (`project ∘ step_reconfig = local_step_reconfig ∘ project`). Coherence is the minimal erasure-stable invariant that makes this Harmony law hold. Safe delegation is a corollary, and composed systems inherit quantitative conservation.

## Core Claims (Main Body)
1. Reconfiguration Harmony theorem (commutation under `link` + delegation).
2. Erasure characterization of Coherence.
3. Safe delegation exactness corollary under `DelegationWF` (sufficiency + footprint-scope converse packaging).
4. Relative minimality over explicit `Admissible(I)`.
5. Composed-system conservation.
6. Exact characterization of execution determinism envelope (soundness + realizability + maximality).
7. Exchange-normalized determinism with spatial-subtyping monotonicity.
8. Observational adequacy + abstract-to-VM adherence modulo envelope.

## Byzantine Integration Mapping
1. Extend Section 2 notation with $H_{\mathrm{byz}}$, $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, and $\mathcal E_{\mathrm{byz}}$.
2. Add explicit formal statement blocks in Section 11:
   - exact Byzantine characterization theorem,
   - converse counterexample-family corollary,
   - capability-gated VM adherence and admission proposition.
3. Integrate theorem-pack interpretation so profile bits correspond to proved Byzantine artifacts.
4. Keep Byzantine liveness beyond stated timing and fairness assumptions as explicit open work.

## Paper Spine (Formal-First)

## 1. Introduction
1. Gap: delegation/topology change is often omitted because invariants break.
2. Main claim: Harmony under reconfiguration is the top-level theorem.
3. **Trilogy completion:** To our knowledge, the field has improved mechanization (Paper 1's concern), fairness-sensitive liveness (Paper 2's concern), and fault tolerance separately, but rarely combines: (i) quotient state space as semantic object, (ii) macroscopic observables on equivalence classes, (iii) commutation theorems for reconfiguration that enlarge the symmetry group. This paper completes that combination with Harmony + minimality.
4. Theorem roadmap (`B -> A -> C -> D -> E -> F -> G -> H`).
5. Paper map and reviewer-facing formal-first framing.
6. Figure placement (essential F1): commuting square for reconfiguration Harmony.
7. Main-body figure budget: 5 essential figures; extras moved to appendices.

## 2. Setup, Definitions, and Side Conditions (Self-Contained)
1. Compact recap of required primitives from Papers 1 and 2: Coherence, arbitrary fair scheduling, parametric delivery models (FIFO/causal/lossy), crash-stop fault tolerance.
2. `link` and delegation reconfiguration operators.
3. `DelegationWF` side conditions and footprint definitions.
4. **Dynamic participant sets.** Role sets are not fixed at protocol start:
   - *Joining*: Delegation allows a role to transfer its endpoint to a new participant who wasn't previously in the session. The delegatee joins mid-protocol.
   - *Leaving*: Crash-stop allows participants to fail (edges become inactive). Delegation can also model voluntary departure (delegate then crash).
   - *Composition*: `link` composes disjoint sessions, potentially introducing new edges between previously unconnected participants.

   The model supports protocols where participants join and leave dynamically, with Coherence preserved across these topology changes.
5. **Definition (Harmony):** projection commutes with (reconfigured) evolution.
6. **Definition (Joint realizability on active edges):** projected locals admit a compatible active-edge witness assignment.
7. **Definition (`Admissible(I)`):** locality + erasure-stability (`ConfigEquiv`) + frame-stability + delegation adequacy.
8. Figure placement (essential F2): delegation footprint before/after highlighting affected edges.

## 3. Running Example (Shared Across Trilogy)

**Protocol:** Distributed Capacity Pool (continued from Papers 1-2)

Papers 1-2 established Coherence and quantitative dynamics for the single-pool protocol. Paper 3 extends to the full distributed version with adaptive coordination, typed guards, and delegation.

**Single-pool baseline (Paper 1-2):**

Roles: **P** (Pool), **C** (Client), **M** (Monitor)

```
C -> P : Request(n)
P -> C : Grant(k)
C -> M : Report(k)
M -> P : Confirm
P -> C : Token(t)        // t is a delegable capacity capability
```

**Distributed version (Paper 3 scope):**

Roles: **Pools[K]** (K distributed pools), **C** (Client), **M** (Monitor), **Coord** (Coordinator, dormant in optimistic mode)

```
// Optimistic mode (CRDT-style, no coordination)
optimistic_mode:
  C -> Pools[i] : Request(n)
  Pools[i] -> C : LocalGrant(k)         // local capacity, may conflict
  C -> M : Report(k)

// Transition guard (typed precondition)
guard transition_to_coordinated:
  requires: conflict_detected ∧ reachable(Coord) ∧ W ≤ transition_budget
  crash_tolerance: CrashTolerant(Pools ∪ {Coord}, F) for |F| ≤ f

// Coordinated mode (consensus-style)
coordinated_mode:
  C -> Coord : Request(n)
  Coord -> Pools[*] : Prepare(n)
  Pools[*] -> Coord : Vote(available)
  Coord -> C : GlobalGrant(k)           // globally consistent
  C -> M : Report(k)
  M -> Coord : Confirm
  Coord -> C : Token(t)
```

**Reconfiguration scenarios:**

1. *Static link (pool federation):*
   - Two pool clusters (Pools[1..K], Pools[K+1..2K]) are linked into a federated system.
   - `link` operator composes the cluster components with a shared coordinator.
   - Pre-link: Each cluster operates independently with local monitors.
   - Post-link: Unified capacity space; cross-cluster requests possible.
   - **Harmony checkpoint:** projection of linked federation equals composition of projected locals.

2. *Adaptive mode transition:*
   - Protocol transitions from optimistic_mode to coordinated_mode.
   - Transition is itself a choreography: quiesce local operations, synchronize state, establish coordinator.
   - **Typed guard:** Transition fires only when guard preconditions are satisfied:
     - `conflict_detected`: semantic trigger from application layer
     - `reachable(Coord)`: crash tolerance check (decidable per Paper 2)
     - `W ≤ transition_budget`: Lyapunov bound ensures transition completes within budget
   - **Harmony checkpoint:** mode transition preserves Coherence; projection commutes with mode switch.

3. *Dynamic delegation (capability transfer):*
   - C delegates its `Token(t)` to a new client C'.
   - C' inherits C's remaining capacity rights without re-requesting from pools.
   - Pre-delegation edges: (Pools[*],C), (C,M), (C,C') for handoff.
   - Post-delegation edges: (Pools[*],C') replaces (Pools[*],C) for subsequent Token-based operations.
   - **Harmony checkpoint:** `project ∘ delegate = local_delegate ∘ project`.

4. *Zero-downtime protocol upgrade (P₁ → P₂):*
   - Capacity Pool v2 adds a new `RateLimit` message in the grant flow.
   - New pools (Pools_v2) join via delegation from old pools.
   - Dual-write phase: old clients see v1 messages, new clients see v2.
   - **Typed guard:** "if all Pools_v2 reachable and W ≤ drain_budget, proceed to cutover."
   - Old pools delegate remaining capacity to new pools and exit.
   - **Harmony checkpoint:** Each upgrade phase preserves Coherence; version boundary typed by async subtyping.

**Paper 3 theorem instantiations:**

| Theorem             | Instantiation on running example                                                         |
|---------------------|------------------------------------------------------------------------------------------|
| B (Harmony)         | Link: federation composition commutes. Mode transition: optimistic→coordinated commutes. Delegation: C→C' handoff commutes. Protocol upgrade: v1→v2 migration commutes. |
| A (Erasure)         | Coherence on pool edges iff Grant/Token alignment is jointly realizable across all pools.|
| C (Safe delegation) | `Coherent(Config) ∧ DelegationWF(C, delegate_to_C')` implies safe handoff; converse is packaged at delegation-footprint scope under explicit side conditions, with per-clause `DelegationWF` strictness witnesses. |
| D (Minimality)      | Any invariant I satisfying Admissible(I) and delegation safety implies I ⊆ Coherent.    |
| E (Conservation)    | For pure reconfiguration (`link`/delegation), W is preserved; transition/upgrade choreography is handled via descent/budget bounds. |

**Typed guards and decidability:**

The mode transition guard demonstrates the connection between Paper 2's decidability results and runtime decisions:

| Guard clause              | Source                    | Compile-time guarantee                              |
|---------------------------|---------------------------|-----------------------------------------------------|
| `conflict_detected`       | Application layer         | N/A (runtime semantic trigger)                      |
| `reachable(Coord)`        | Crash tolerance decidability | If guard passes, coordinated_mode can complete    |
| `W ≤ transition_budget`   | Lyapunov bound            | Transition completes in ≤ budget productive steps   |
| `|F| ≤ f`                 | Crash tolerance param     | Tolerate up to f pool crashes during transition     |

**Cross-paper continuity:**
- Paper 1: Coherence/Consume checks on single-pool `Grant` step.
- Paper 2: W₀ = 25, Bc = 2, crash tolerance for single pool.
- Paper 3: Distributed pools with adaptive coordination, typed guards, delegation.

**Concrete delegation trace:**

```
State 0: C holds Token(t) from coordinated_mode grant
         C' exists but has no capacity rights
         Edges: (Pools[*],C) active, (C,C') active for handoff, (Pools[*],C') inactive

State 1: C sends Delegate(t) to C'
         delegate(C, C', t) applied
         Graph delta: edges (Pools[*],C') activated, edges (Pools[*],C) restricted

State 2: C' now holds capacity rights via Token(t)
         Edges: (Pools[*],C') active for Token-based ops, (C,C') closed
         Coherence preserved: higher-order Consume updated graph
         W conserved: delegation doesn't change depth or buffer counts
```

**Adaptive transition trace:**

```
State 0: optimistic_mode active
         W = 15 (some pending local grants)
         Pools operating independently

State 1: conflict_detected = true (concurrent grants exceed capacity)
         Guard check: reachable(Coord)? → CrashTolerant({Pools, Coord}, ∅) = true
         Guard check: W ≤ 20? → true
         Transition fires

State 2: Quiesce choreography executes
         All pending LocalGrants drain (W decreases)
         Coordinator activated

State 3: coordinated_mode active
         W = 0 at mode boundary (clean handoff)
         Subsequent requests use consensus path
```

**Protocol upgrade trace (v1 → v2):**

```
State 0: All pools running v1 protocol
         Clients C[*] connected to Pools_v1[*]
         W = 12 (some in-flight grants)

State 1: Pools_v2[*] join via delegation from Pools_v1[*]
         Dual-write: v1 clients see Grant(k), v2 clients see Grant(k) + RateLimit(r)
         Message translation typed by AsyncSubtype(LocalType_v2, LocalType_v1)
         Coherence preserved: both versions satisfy EdgeCoherent

State 2: Guard check: all Pools_v2 reachable? → true
         Guard check: W ≤ drain_budget (= 20)? → true (W = 8)
         Cutover proceeds

State 3: Pools_v1[*] delegate remaining capacity to Pools_v2[*]
         Pools_v1[*] exit (edges become inactive)
         All clients now connected to v2 pools

State 4: Legacy edges drained (W = 0)
         Upgrade complete, zero downtime
         All subsequent operations use v2 protocol
```

Figure placement: four-panel timeline showing (1) optimistic→coordinated transition with guard checks, (2) pool federation via link, (3) C→C' delegation with edge activations, (4) v1→v2 protocol upgrade with version boundary. Panels are annotated with W behavior (conservation for pure reconfiguration; descent/budget for transition choreography) and Coherence checkpoints.

## 4. Theorem B: Reconfiguration Harmony (Static + Dynamic)
1. Statement: for well-typed `C`, well-formed `rho ∈ {link, delegate}`, and enabled post-`rho` steps, projection commutes with reconfigured evolution.
2. Static component: compositional Harmony through `link`.

Coinductive boundary note: at the effect-observation layer, linking and composition contexts are discharged via `effectBisim_congr_link`, and quotient compatibility is bridged by `configEquiv_iff_effectBisim_silent`.
3. Dynamic component: delegation Harmony with higher-order consume updates.
4. Side-condition necessity decomposition: each indexed Harmony side condition has a dropped-condition strictness witness interface.
5. Figure placement (essential F3): two-panel Harmony diagram (static + dynamic).

## 5. Theorem A: Erasure Characterization of Coherence
1. Statement: Coherence iff projected locals are jointly realizable on active edges.
2. Proof sketch: realizability -> Coherence and Coherence -> realizability.
3. Clarifies semantic content of the invariant used in Theorem B.
4. **Quotient-first remark:** This theorem is the formal content of "erasure is semantics." Defining a quotient state space as the semantic object is the architectural stance of this trilogy (with novelty scope tied to the survey claim in `papers.md`). Coherence is precisely the invariant that survives the quotient.
5. Optional figure placement: realizability witness map (appendix candidate if page-tight).

## 6. Theorem C: Safe Delegation Corollary
1. Sufficiency: `Coherent C ∧ DelegationWF(C, op) -> SafeDelegation(C, op)`.
2. Footprint exactness packaging: `SafeDelegation(C, op) ↔ SafeDelegationFootprint(C, op)` (under explicit step/WF side conditions), with dropped-side-condition counterexample witnesses and per-clause `DelegationWF` independence packaging.
3. Derivation dependency: A + B + `DelegationWF`.
4. Figure placement: implication chain A+B+WF -> C.

## 7. Theorem D: Relative Minimality
1. Minimality theorem: `forall I, Admissible(I) -> (forall C, I C -> Coherent C)`.
2. Admissibility closure: `Coherent` itself satisfies `Admissible(I)` under the stated model/assumption bundle's locality/frame obligations, completing weakest-admissible packaging.
3. Consequence: Coherence is the weakest admissible invariant guaranteeing delegation safety.
4. Figure placement (essential F4): invariant lattice with Coherence as minimal admissible node.

## 8. Theorem E: Composed-System Conservation
1. Under composition via `link`, delegation preserves Coherence and Harmony.
2. Quantitative lift: Paper 2 measure `W = 2*sum(depth) + sum(buffer)` is preserved for pure reconfiguration and provides descent/budget certificates for transition choreography under the stated model/assumption bundle.
3. Flagship systems theorem.
4. Figure placement (essential F5): composed-system diagram with `W` before/after reconfiguration.
5. Table placement: theorem decomposition table (B/A/C/D/E/F/G/H and support lemmas).

## 9. Theorem F: Exact Characterization of Determinism Envelope
1. Statement: under the stated model/assumption bundle, the envelope is exact: soundness, realizability/completeness, and maximality.
2. Positioning: dual to Theorem D (minimality), giving weakest admissible invariant + exactly characterized admissible behavioral quotient.
3. D/F duality package: theorem-level exact-boundary pairing of D-minimality with F-maximality.
4. Proof shape: (i) envelope soundness, (ii) constructive realizability witness, (iii) strict-superset counterexample.
5. Boundary corollary F.1: finite-erasure transportability holds iff the behavior lies in the rational (finite-state) coinductive fragment.
6. Boundary corollary F.2: strict boundary witness exists (a non-rational coinductive behavior that is not finite-erasure transportable).
7. Boundary corollary F.3: syntax-bridge exactness on the inductive embedding (`toCoind` image exactness).
8. Appendix-only corollary F.4: principal finite witness + adequacy replay for rational behaviors.
9. Appendix-only corollary F.5: relative maximality of the rational fragment among finite-erasure-transportable fragments.
10. Figure placement: minimality/maximality dual-lattice diagram (appendix candidate if page-tight).

## 10. Theorem G: Exchange-Normalized Determinism and Spatial Monotonicity
1. Exchange-normalized determinism: admissible reorderings collapse to equivalent safety-visible outcomes.
2. Spatial-subtyping monotonicity: safety/envelope obligations are preserved under admissible spatial refinement.
3. Dependency structure: exchange/coherence lemmas + spatial typing/subtyping lemmas + reconfiguration Harmony.
4. Figure placement: normalization-by-exchange commutation figure with spatial refinement overlay.

## 11. Theorem H: Observational Adequacy and VM Adherence Modulo Envelope
1. Statement: abstract/protocol envelope results transport to VM theorem-pack capabilities, and VM/reference executions are observationally adequate modulo the declared envelope relation.
2. Runtime consequence: proof-carrying conformance between claimed runtime profile and available proof artifacts.
3. Local↔sharded collapse exactness: under explicit collapse assumptions, local and sharded exact-envelope characterizations coincide.
4. Cross-layer dependency: protocol theorem bundle -> adapter lemmas -> runtime theorem-pack extraction -> adequacy theorem.
5. Secondary corollary S1: principal capability + admission completeness (not only one-way admission safety).
6. Secondary corollary S2: compositional exactness under explicit non-interference assumptions, plus converse strictness boundary packaging when non-interference is dropped.
7. Deferred program P1: full failure/recovery envelope (commit certainty + restart/reconcile policy) post-trilogy.

## 12. Supporting Formal Layer
1. Higher-order extension (`ValType.chan`, graph delta, higher-order consume).
2. Conservative extension (HO collapses to FO without channel payloads).
3. Dependency structure across support lemmas.

## 13. Worked Transport in Main Body (Concrete)
1. **Worked transport 1 (fully spelled):** Large deviation tail bound for completion-time SLA.
2. **Worked transport 2 (fully spelled):** Mixing-time bound for convergence-to-baseline guarantees.
3. For each: structural assumptions from typing/Harmony vs analytic assumptions discharged.
4. Table placement: compact 2-example assumption-to-conclusion table.

## 14. Discussion: The Classical Boundary

**Structural properties that session types with Coherence exhibit:**

| Property                  | Session types                                | Classical physics analogue     |
|---------------------------|----------------------------------------------|--------------------------------|
| **Exchangeability**       | Roles interchangeable via delegation         | Particle indistinguishability  |
| **Local interaction**     | Per-edge Coherence (no action at distance)   | Local Hamiltonians             |
| **Well-posed dynamics**   | Preservation (steps preserve Coherence)      | Deterministic evolution        |
| **Classical correlations**| Buffers hold classical data, no superposition| Classically representable correlations (no entanglement in this model) |
| **Classical state spaces**| Finite sets, simplices, measure spaces       | ODEs, SDEs, kinetic theory     |

These properties place session-typeable systems in a classical regime where classical reasoning tools apply.

**Why session types land in the classical regime:**

1. *Identity becomes gauge, not structure.* With safe delegation, role identity is eliminable. State lives on a quotient by permutations—only multisets and empirical distributions matter. This is the move from labeled mechanics to statistical mechanics.

2. *Correlations remain classically representable.* Session semantics assume separable local state and classical message passing. Even after delegation, the strongest invariant is a classical joint distribution evolving under a Markov kernel. Irreducibly quantum correlations violate these assumptions structurally.

3. *Dynamics live on classical state spaces.* Everything admissible evolves on finite sets, simplices, or measure spaces with Lipschitz drift and Markov kernels—the scope of classical ODEs, SDEs, and mean-field limits, not unitary evolution on Hilbert space.

4. *Ergodicity becomes meaningful (under the stated model/assumption bundle).* The question "do time averages equal ensemble averages?" is a marker of classical statistical mechanics. In quantum theory, ergodicity is subtle and often false. Here it is provable for transport profiles that discharge Lyapunov/mixing side conditions.

5. *Critical phenomena are outside the current transport envelope.* KAM theory, chaotic mixing, critical phenomena, and turbulence do not lift automatically under the stated model/assumption bundle. But this is where classical mechanics itself stops being uniform.

**Where classical erasure stops:**

| Failed erasure           | Why it fails                                         |
|--------------------------|------------------------------------------------------|
| **Phase erasure**        | Relative phase is observable (quantum interference)  |
| **Entanglement erasure** | Local marginals do not determine the global quantum state |
| **Measurement erasure**  | Observer affects state (quantum back-action)         |
| **Topological erasure**  | Global topological degrees can be stateful/observable |

These are non-classical moves. Within this framework, under the stated model/assumption bundle, the safe erasures are exactly the twelve canonical classical erasures. Systems requiring quantum correlations, non-local measurements, or topological protection are not captured without extending the semantics.

**Beyond the boundary (concrete anchor):**
Recent work explicitly explores **Quantum MPST** (SEFM 2024; arXiv:2409.11133), pushing session types into quantum regimes where our classical erasures fail. This supports the boundary claim: standard erasure-safe MPST semantics do not model entanglement/measurement back-action without extension. Our contribution is carving the classical regime cleanly—showing exactly what holds and why.

**The quotient-by-symmetry worldview:**
The physics framing is not hand-wavy metaphor but structural alignment. Quotient-by-symmetry + coarse-graining + Lyapunov monotone is exactly how classical statistical mechanics works (Marsden-Weinstein reduction, entropy production, ergodic theory). Session types with Coherence instantiate this pattern in a typed distributed-systems context. The formal kernel is: safe delegation enlarges the symmetry group, making role identity gauge.

**Framing for reviewers:**
1. Classical-boundary interpretation is a *consequence* of the formal results, not a premise.
2. Formal claims (Theorems A-H) stand independently of physics interpretation.
3. The interpretation explains *why* the formal structure has the shape it does.

## 15. Related Work, Limitations, Conclusion

### 15.1 Related Work
1. **Prior delegation/topology-change lines:** Higher-order sessions (HO π-calculus variants), session-based Java, internal delegation in global-type frameworks.
2. **Ozone (ECOOP 2024):** Both Ozone and this paper address "order erasure"—correctness under message reordering. Ozone permits out-of-order execution via futures/reactive-style programming with integrity preservation. We achieve similar goals via quotients and Coherence-preserving symmetries. Different mechanisms, related insights about trajectory details becoming gauge.
3. **MPST for runtime adaptation (ECOOP 2021):** Harvey et al. give language-design safety for component replacement in actor settings. Our Harmony is a *semantic commutation theorem* about reconfiguration operators—a different layer (metatheory vs language design) with different guarantees (projection commutes vs runtime safety).
4. **Commutation + minimality rarity:** MPST literature often provides sufficient conditions for delegation safety without showing minimality in an invariant lattice. Theorem D (relative minimality) is comparatively rare—we prove Coherence is the *weakest* admissible invariant, not just a sufficient one.
5. **Mechanization (ECOOP 2025):** Tirore-Bengtson-Carbone's mechanization validates that MPST meta-theory is brittle under reconfiguration. Our Harmony theorem is designed to be mechanization-friendly via the same Coherence kernel as Papers 1-2.
6. **Unified positioning:** The field has improved mechanization, fairness-sensitive liveness, and fault tolerance separately (2021-2025), but rarely combines: (i) quotient state space as semantic object, (ii) macroscopic observables on equivalence classes, (iii) commutation theorems for reconfiguration that enlarge the symmetry group. This paper completes that combination.

### 15.2 Limitations
1. Assumptions likely to matter for reviewers.
2. Side conditions (`DelegationWF`, footprint definitions) are explicit but non-trivial.
3. Higher-order extension requires `ValType.chan`; systems without channel passing collapse to first-order.

### 15.3 Target Application: Unified Distributed Systems Protocols

The trilogy's capabilities converge on a compelling application: unified protocol stacks for distributed systems.

Traditional distributed systems fragment across layers (P2P networking, consensus, state machine) with informal interfaces. Most bugs occur at layer boundaries. The unified VM + session types approach offers:

- **Single formalism**: Networking handshakes, consensus rounds, and state transitions are all choreographies in one VM
- **Cross-layer type checking**: Session types span layers; interface mismatches become type errors
- **Crash tolerance**: Paper 2's decidability applies directly to "can this protocol complete if F nodes crash?"
- **Delegation**: Node handoff (failover, rotation) is delegation with Coherence preservation
- **Composition**: Protocol layering via `link` with typed guarantees at interfaces

This addresses the reliability gap where most distributed systems bugs occur—at layer boundaries rather than within layers.

**Adaptive protocols with typed transitions.** A further design space: protocols that transition between coordination modes (e.g., CRDT ↔ consensus) with formal guarantees through the transition. The transition itself is a choreography—quiesce, synchronize, establish leader—with crash tolerance decidability answering "can this transition complete if nodes F crash?"

**Typed guards with decidable preconditions.** The decision to transition can be a guard checked at runtime but verified at compile time: "if reachable nodes ≥ 2f+1, transition to consensus" guarantees consensus can complete. Guards can reference crash tolerance decidability, Lyapunov bounds (W ≤ budget), and buffer thresholds—connecting Paper 2's quantitative results to runtime decisions with machine-checked guarantees.

**Zero-downtime typesafe protocol upgrades.** Protocol version migration becomes a typed choreography rather than an operational hazard. The upgrade from protocol P₁ to P₂ is itself a choreography:

1. *Coordination phase*: New nodes running P₂ join via delegation; old nodes continue P₁
2. *Dual-write phase*: Messages are translated at boundaries (typed by subtyping)
3. *Cutover phase*: Old nodes delegate to new nodes and exit
4. *Cleanup phase*: Legacy edges drain (Lyapunov-bounded)

Each phase preserves Coherence. Typed guards ensure phases complete: "if all P₂ nodes reachable and W ≤ drain_budget, proceed to cutover." The result is live migration with machine-checked safety and no required downtime window. This addresses a major operational pain point in distributed systems where protocol upgrades are often the riskiest operations.

### 15.4 Conclusion
Harmony-first theorem story with delegation corollary and minimality.

## Main Theorem Slots
1. Theorem B: Reconfiguration Harmony.
2. Theorem A: Erasure characterization.
3. Theorem C: Safe delegation exactness corollary.
4. Theorem D: Relative minimality over `Admissible(I)`.
5. Theorem E: Composed-system conservation.
6. Theorem F: Exact characterization of determinism envelope.
7. Corollary F.1: Rational-fragment exactness (finite erasure iff rational).
8. Corollary F.2: Strict boundary witness (non-rational non-transportable behavior).
9. Corollary F.3: `toCoind` image exactness.
10. Theorem G: Exchange-normalized determinism + spatial-subtyping monotonicity.
11. Theorem H: Observational adequacy + VM adherence modulo envelope.
12. Secondary corollary S1: Principal capability + admission completeness.
13. Secondary corollary S2: Compositional exactness under non-interference + converse strictness boundary packaging.
14. Deferred program P1: Failure/recovery envelope extension.

## Appendices

## Appendix A. Full Regime Analysis
1. Scheduling/failure hierarchies.
2. **Crash-stop as capability:** Paper 2 establishes exact decidable crash-stop tolerance. This appendix extends the analysis to composed/delegated systems—crash sets in linked systems, crash tolerance preservation under delegation.
3. 3x3 regime matrix.
4. Structural vs sensitive result families.
5. Practical regime-selection playbook.
6. Heavy-tail/non-normal analysis.

## Appendix B. Expanded Practical Payoff Tables
1. Transported result payoff table (10-theorem set).
2. 3x3 interpretation table.
3. Regime selection guide.
4. Practical interpretation notes.

## Appendix C. Full Theorem-Transport Catalog

### C.1 Scope Note
Transport-only ten-theorem set beyond Papers 1 and 2 core theorems.

### C.2 Transport Matrix + Fully Discharged Exemplars

Assumption sets are necessity-tagged (`proven-necessary` vs `sufficient-only`) per transported theorem profile, with dropped-assumption failure witnesses used to certify profile-level minimal-basis closure where claimed.

| Classical result                              | Sched | Fail | Hypothesis typing provides                            | What still needs checking                          | Conclusion                                  |
|-----------------------------------------------|:-----:|:----:|-------------------------------------------------------|----------------------------------------------------|---------------------------------------------|
| Foster-Lyapunov + Harris ergodicity           |   R   |  R   | finite-state Markov abstraction + irreducibility      | drift + minorization (petite set)                  | unique invariant law + geometric convergence|
| Mixing-time bounds                            |   R   |  R   | ergodic finite-state transition system                | spectral gap or coupling                           | explicit burn-in and rate certificates      |
| MaxWeight/backpressure throughput optimality  |   D   |  R   | queue conservation constraints from typing            | arrivals interior to capacity region + policy      | stability for admissible loads              |
| Little's Law (stable regime)                  |   A   |  A   | flow conservation and arrival/completion accounting   | steady-state existence and finite first moments    | `L = lambda W` identities                   |
| Fluid-limit stability theorems                |   A   |  A   | scaled process and Lipschitz drift templates          | global fluid ODE stability + tightness             | positive recurrence and drain guarantees    |
| Large deviation principle                     |   A   |  R   | finite-state Markov dynamics                          | non-degenerate rate function + exponential tight   | exponential completion/SLA tail bounds      |
| Concentration inequalities                    |   A   |  R   | bounded increments or weak dependence                 | bounded differences/sub-Gaussian mgf               | high-probability aggregate guarantees       |
| Heavy-traffic diffusion limits                |   R   |  R   | critical-load scaling and centered increments         | functional tightness + reflection-map regularity   | reflected-diffusion approximation           |
| Propagation of chaos / mean-field limits      |   R   |  R   | exchangeability from delegation + mean-field form     | Lipschitz kernel + uniform moments                 | deterministic mean-field limit as n → ∞     |
| Functional CLT / invariance principles        |   R   |  R   | martingale decomposition for cumulative observables   | Lindeberg + quadratic-variation convergence        | Gaussian weak limits for excursion paths    |

### C.3 Limitation Statement
Transport conclusions require theorem-specific analytic side conditions.

## Appendix D. Formal Mechanization and Runtime Realization (Supporting)

### D.1 Supporting Theorem Decomposition
1. Compositional Harmony through `link`.
2. Higher-order Coherence preservation under delegation.
3. Conservative extension (HO to FO collapse).
4. Choreographic delegation Harmony.
5. Liveness conservation under composition/delegation.
6. Delegation in composed systems.
7. Rational-fragment supporting pack: principal witness + adequacy replay + relative maximality.
8. Transport assumption minimal-basis closure (profile-level dropped-assumption witnesses).
9. Canonical VM basis uniqueness up to erasure isomorphism.
10. Quotient universality of observables (`observationalErasure` factorization iff `ConfigEquiv`-invariance).
11. Productive-step bound tightness witness packaging + conservative-extension converse (FO→HO on channel-free traces).

### D.2 Cross-Layer Impact Map (VM included here, not main body)
1. SessionTypes: `ValType.chan` semantics.
2. Choreography: `delegate` projection rules.
3. Protocol/Coherence: HO consume and preservation.
4. Protocol/Deployment: link/merge/Harmony theorems.
5. Protocol/Typing: linear capability transfer.
6. Runtime/Iris: ownership transfer via ghost-map updates.
7. Runtime/VM: `transfer`/`acquire` realization.
8. Runtime/Proofs: theorem-pack capabilities for envelope/profile gating.

### D.3 Reproducibility Notes
1. Proof dependency DAG for B/A/C/D/E/F/G/H.
2. File-to-theorem index.
3. Build/check commands.
