# Computable Dynamics for Asynchronous MPST: Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures

[Paper](paper2.md)

## One-Paragraph Thesis
Dynamics on the Coherence quotient are computable in two linked senses: evolution bounds are computable via a Lyapunov state function, and protocol predicates are computable via finite-reachability decision schemas. Both theorems share one mechanism: regular finite-state structure.

## Core Claims (Main Body)
1. Quantitative dynamics theorem via weighted Lyapunov function `W = 2*sum(depth) + sum(buffer)`.
2. Uniform algorithmic dynamics theorem via finite reachability on regular local types.
3. Corollaries spanning decidability and quantitative bounds.

## Byzantine Integration Mapping
1. Extend Section 2 notation with $H_{\mathrm{byz}}$, $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, and $\mathcal E_{\mathrm{byz}}$.
2. Add formal statement blocks in Section 6:
   - exact Byzantine safety characterization theorem,
   - converse counterexample-family corollary,
   - VM-bridge interface proposition.
3. Keep crash-stop exactness as an explicit theorem and scope Byzantine claims to safety characterization assumptions.
4. Move all implementation detail to appendices and theorem index tables.

## Paper Spine (Main Sections)

## 1. Introduction
1. Gap: liveness often qualitative; decision results fragmented.
2. Unifying insight (upfront): both Theorem 1 and Theorem 2 derive from the same finite-state regularity of quotient dynamics.
3. **Novel combination:** To our knowledge, the field has quotient-level Lyapunov bounds (rare) and unified decidability schemas (rare) separately, but not together. DS usually has per-protocol bounds; PL usually has qualitative liveness. We give both quantitative bounds and algorithmic decidability from one regularity kernel.
4. Contributions and scope.
5. Paper map.
6. Figure placement (essential F1): two-branch spine showing both branches rooted in shared regularity.
7. Main-body figure budget: 5 essential figures; extras deferred.

## 2. Self-Contained Model Summary
1. Compact recap of configurations, steps, Coherence, and regularity assumptions.
2. **Model scope:** Asynchronous buffered communication under arbitrary fair scheduling, parametric delivery models (FIFO/causal/lossy via `DeliveryModel` typeclass), active-edge invariants.
3. Productive-step vs total-step semantics.
4. Scheduler assumptions preview (explicit): round-robin, `k`-fair, and adversarial baseline.
5. Finite-state reachability setup for regular local types.
6. Goal: fully readable without Paper 1.

## 3. Running Example (Shared Across Trilogy)

**Protocol:** Distributed Capacity Pool (continued from Paper 1)

Paper 1 established Coherence for the single-pool protocol. Paper 2 adds quantitative dynamics and foreshadows the distributed version.

**Single-pool configuration (Paper 1 baseline):**

Roles: **P** (Pool), **C** (Client), **M** (Monitor)

```
C -> P : Request(n)
P -> C : Grant(k)
C -> M : Report(k)
M -> P : Confirm
P -> C : Token(t)
```

| Component           | Value                                                              |
|---------------------|--------------------------------------------------------------------|
| Local type depth(P) | 5 (send Grant, recv Confirm, send Token, plus recursion unfolding) |
| Local type depth(C) | 5 (send Request, recv Grant, send Report, recv Token)              |
| Local type depth(M) | 2 (recv Report, send Confirm)                                      |
| Buffer (C,P)        | `[Request(10)]` — one pending request                              |
| Buffer (P,C)        | `[]` — empty                                                       |
| Buffer (C,M)        | `[]` — empty                                                       |
| Buffer (M,P)        | `[]` — empty                                                       |

**Paper 2 computations:**

1. *Lyapunov measure W₀:*
   ```
   W = 2·Σdepth + Σbuffer = 2·(5 + 5 + 2) + 1 = 25
   ```

2. *Productive-step bound:* At most 25 productive steps to quiescence (W = 0).

3. *Scheduler lift:* Under 2-fair scheduling, total-step bound is ≤ 50 steps.

4. *Critical capacity threshold Bc:*
   - Bc = 2 for this protocol structure.
   - Phase boundary (under the stated model/assumption bundle): B < 2 admits unbounded executions; B ≥ 2 gives bounded buffers.

5. *Per-step descent profile:*
   | Step               | ΔW                          |
   |--------------------|-----------------------------|
   | C sends Request    | −2 (depth) +1 (buffer) = −1 |
   | P receives Request | −1 (buffer)                 |
   | P sends Grant      | −2 (depth) +1 (buffer) = −1 |
   | C receives Grant   | −1 (buffer)                 |

   Every productive step yields ΔW ≤ −1.

**Crash tolerance (foreshadowing Paper 3 distributed version):**

Even in the single-pool setting, crash tolerance applies (policy-dependent for monitoring):
- Under strict confirm-before-token semantics, `CrashTolerant({P,C,M}, {M})` = false.
- Under a degraded-mode policy where missing monitor confirmation can be handled locally, `CrashTolerant({P,C,M}, {M})` can be true.
- `CrashTolerant({P,C,M}, {P})` = false: if P crashes, no grants are possible.
- Non-monotonicity preview: adding a backup pool P' can make some crash sets tolerable that weren't before.

**Quantitative dynamics for distributed version (preview):**

Paper 3 extends to K distributed pools. The same W measure applies compositionally:
- W_distributed = Σᵢ W(Poolᵢ) + W(coordination)
- Transition from optimistic to coordinated mode has cost W_transition ≤ budget (typed guard)
- Crash tolerance: "can allocation complete if pools F crash?" remains decidable

**Cross-paper continuity:**
- Paper 1: Coherence/Consume checks on single-pool `Grant` step.
- Paper 3: Distributed pools with adaptive coordination, typed guards, delegation.

Figure placement: protocol graph with W-contribution annotations on each edge, plus initial-state table showing depth and buffer values.

## 4. Theorem 1: Quantitative Dynamics (Lyapunov Descent)
1. Definition of `W` and interpretation.
2. Nonnegativity and quiescence (`W = 0`).
3. Strict productive-step descent by rule.
4. Productive-step termination bound.
5. Lift to total-step bounds under scheduler assumptions.
6. Figure placement (essential F2): weighted decomposition of `W`.
7. Figure placement (essential F3): per-rule `Delta W` profile.

## 5. Theorem 2: Algorithmic Dynamics Schema
1. Reachable-graph finiteness for regular local types.
2. Generic exploration skeleton.
3. Generic decidability transfer theorem.
4. Complexity envelope.
5. Figure placement (essential F4): decision workflow flowchart.

## 6. Decidability Results

### 6.1 Async Subtyping Decidability
Async subtyping for regular types is decidable via finite reachability on (S, T, buffer) triples.

### 6.2 Regular Type-Equivalence Decidability
Coinductive type equivalence for regular types is decidable via the same finite-reachability schema.

### 6.3 Exact Crash-Stop Tolerance (Theorem)
**Theorem (Crash-Tolerance Decidability + Characterization):** For any finite protocol G and crash set F:
1. `CrashTolerant G F` is decidable via residual communication graph connectivity.
2. Under the stated model/assumption bundle (crash-stop faults, finite role graph, fair scheduling, and a delivery model satisfying the residual-reachability criterion), crash set F is tolerable iff the residual graph (after removing crashed participants) remains connected.
3. **Non-monotonicity:** The crash-tolerance relation is non-monotone—adding an intermediary can break tolerance that held without it. This is proved constructively.

This is stronger than "decidable"—under explicit assumptions, we have a tight iff-characterization with explicit counterexamples for non-monotonicity.

### 6.4 Branching Feasibility
Branching feasibility via confusability/chromatic-number criterion.

### 6.5 Table Placement
Decision-result summary (predicate, method, exactness class, assumptions).

## 7. Quantitative Corollaries and Worked Numbers
1. Additive compositionality for disjoint sessions.
2. Critical capacity threshold `Bc`.
3. Worked running-example numbers:
   - `W0 = 25`.
   - productive-step bound `<= 25`.
   - 2-fair lift `<= 50` total steps.
   - `Bc = 2`.
4. Exact vs conservative distinction (main-body explicit):
   - exact: productive-step descent, finite reachability decidability,
   - conservative: scheduler-lifted total-step bounds, some practical threshold estimates.
5. Figure placement (essential F5): `Bc` phase boundary with running-example point.
6. Table placement: worked-numbers table (`W0`, scheduler, bound, `Bc`, exact/conservative tag).

## 8. Proof Architecture
1. Quantitative branch.
2. Algorithmic branch.
3. Shared finite-state kernel and reuse map.
4. Optional figure placement: corollary dependency DAG (appendix candidate if page budget tight).

## 9. Mechanization and Artifact
1. Theorem-to-file mapping.
2. Automation and proof combinators.
3. Executable decision extraction points.
4. Table placement: mechanization coverage table.

## 10. Related Work and Delta
1. **Qualitative-liveness lines:** Prior MPST work provides qualitative progress/liveness guarantees.
2. **Fair termination (JLAMP 2024, CONCUR 2022):** Recent type systems guarantee termination under fairness assumptions. Our Lyapunov approach is complementary: they give type-theoretic liveness *guarantees*; we give *quantitative bounds* (exact productive-step counts, scheduler-lifted total-step bounds) on a quotient. Both are valuable; ours adds the numbers.
3. **Mechanization pressure (ECOOP 2025):** Tirore-Bengtson-Carbone's mechanization work validates that MPST meta-theory is brittle—our unified decidability schema addresses this by deriving multiple results from one regularity kernel.
4. **Fragmented decidability lines:** Prior decidability results (async subtyping, type equivalence, implementability) are typically proved separately. We unify them under one finite-reachability schema.
5. **DS-facing positioning:** We're not proving a protocol correct; we're giving a *canonical reduction principle* (quotient + invariant) that explains when a class of typed distributed systems admits stable macroscopic reasoning, and when it doesn't. DS has many tight thresholds per-problem (consensus, replication); we give structure-sensitive bounds across a semantic class.
6. Delta: one regularity kernel for both quantitative and algorithmic branches.
7. Table placement: prior-work delta table.

## 11. Limitations and Scope
1. Conditions for tightness.
2. Cases requiring scheduler assumptions.
3. **Fault model boundary:** Results hold for crash-stop faults with exact characterization. Beyond crash-stop (Byzantine behavior, delivery failures outside the chosen `DeliveryModel` assumptions, non-Markovian failures), erasure safety requires additional machinery—this is the boundary of the classical regime.

Rational-effect boundary note: for effect-level coinductive transport we restrict to the witness-carrying rational fragment (`RationalEffectFragment`), where finite transport witnesses are explicit and checker-backed; a strict outside witness (`strict_boundary_witness_effect`) marks non-transportability beyond that subclass.
4. Transport-level claims are Paper 3 scope.

## 12. Conclusion
1. Computability of quotient dynamics in two senses.
2. Bridge from Paper 1 structure to Paper 3 reconfiguration/transport.

## Main Theorem and Corollary Slots
1. Quantitative Dynamics Theorem (Lyapunov descent).
2. Algorithmic Dynamics Schema Theorem (finite reachability).
3. **Crash-Tolerance Theorem** (exact decidability + iff-characterization + non-monotonicity).
4. Async Subtyping Decidability Corollary.
5. Type Equivalence Decidability Corollary.
6. Branching Feasibility Corollary.
7. Additive Composition Corollary.
8. Critical Capacity Corollary.

## Appendices

## Appendix A. Full Quantitative Proofs
1. Per-step descent lemmas.
2. Tight productive-step bounds.
3. Scheduler-lift theorems.
4. Total-step corollaries.

## Appendix B. Full Algorithmic Schema Proofs
1. Reachable-state finiteness construction.
2. Exploration termination proof.
3. Decision-reduction correctness theorem.
4. Instantiation template.

## Appendix C. Expanded Decision Instantiations
1. Crash tolerance details.
2. Branching feasibility details.

## Appendix D. Expanded Mechanization Inventory
1. File-level inventory and line counts.
2. Theorem-to-file mapping.

## Appendix E. Boundary Cases and Tightness Notes
1. Tightness examples.
2. Scheduler-sensitive cases.
3. Finite-state assumption failure cases.

## Appendix F. Reproducibility Notes
1. Build/check commands.
2. Theorem index by section.
3. Artifact checklist.
