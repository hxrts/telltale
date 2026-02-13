# Coherence for Asynchronous Buffered MPST: A Mechanized Metatheory

[Paper](paper1.md)

## One-Paragraph Thesis
This paper has two spine claims: active-edge Coherence gives a reusable preservation architecture for asynchronous buffered MPST, and Coherence remains stable under asynchronous subtype replacement via `Consume_mono`. (The effect-typed bridge is treated as supporting artifact material, not a central theorem claim.)

## Core Claims (Main Body)
1. Coherence preservation via a reusable three-way edge proof skeleton.
2. Session evolution via `Consume_mono` and subtype replacement.

## Extended Artifact Claim (Non-Spine)
1. Effect-typed execution bridge (`EffectModel.handlerType`) from choreography obligations to VM obligations.

## Byzantine Integration Mapping
1. Add shared Byzantine notation in Section 2: $H_{\mathrm{byz}}$, $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$, $\mathcal E_{\mathrm{byz}}$.
2. Add cross-paper formal interface statements in Section 8:
   - exact characterization interface,
   - converse counterexample interface,
   - VM adherence bridge interface.
3. Keep implementation-level details and artifact paths out of main-body Byzantine claims.
4. Keep full mechanization linkage in appendices and theorem index only.

## Paper Spine (Main Sections)

## 1. Introduction
1. Problem: asynchronous buffered MPST proofs are hard with per-step global re-derivation.
2. Main idea: per-edge active-edge Coherence replaces global re-derivation in preservation proofs.
3. Contributions and positioning.
4. **Quotient-first framing:** The architecture is designed so that Coherence defines a quotient state space—configurations identified up to Coherence-preserving symmetries. Novelty scope is tied to the trilogy-level literature-positioning claim (surveyed 2021-2025 corpus), rather than repeated here.
5. Scope (early): asynchronous buffered semantics under arbitrary fair scheduling, parametric delivery models (FIFO/causal/lossy), active-edge quantification, classical payloads, regularity where needed.
6. Paper map.
7. Figure placement (essential F1): visual thesis figure comparing legacy proof loop vs Coherence-local proof loop.
8. Main-body figure budget: 4 essential figures; non-essential visuals move to appendices.

## 2. Self-Contained Model and Semantics
1. Configurations, environments, buffers, and step relation.
2. `ActiveEdge`, `EdgeCoherent`, `Coherent`, and `Consume` definitions.
3. Well-typedness assumptions and update operators.
4. **Parametric delivery semantics:** Model admits FIFO/causal/lossy via the same `DeliveryModel` typeclass interface—a differentiator vs FIFO-only prior work. Most MPST literature assumes FIFO; we parameterize over delivery model from the start. Details deferred to Appendix D.
5. Figure placement (essential F2): active-edge snapshot showing exactly which edges are checked.

**Why "Coherence"**

Coherence is the operational analogue of Girard's *coherence spaces* (1987), the standard denotational model for linear logic. A coherence space is a set of tokens with a reflexive symmetric relation (coherence). Points are cliques—maximal subsets where all pairs are coherent. Two tokens are *incoherent* if they represent mutually exclusive resource uses.

| Coherence spaces                | Telltale Coherence                                        |
|---------------------------------|-----------------------------------------------------------|
| Token                           | Directed edge (A, B, s) with buffer and local type        |
| Coherence relation              | `EdgeCoherent`: buffer compatible with receiver's type    |
| Incoherence                     | Incompatible demand: receiver can't handle buffer         |
| Clique (point)                  | `Coherent` configuration: all active edges coherent       |
| Linear map preserves cliques    | Preservation theorem: steps preserve Coherence            |
| Tensor decomposes componentwise | Per-edge independence (frame rule)                        |

Both are instances of the same pattern: **coherence = the invariant characterizing erasure-safe combinations**. Girard's insight was that linear logic's resource sensitivity is captured by the coherence relation. Telltale's insight is the operational version: session type safety is captured by `EdgeCoherent`. This connection is structural, not metaphorical—coherence spaces are the denotational semantics for linear logic, and linear logic is the logical foundation for session types (Caires-Pfenning 2010, Wadler 2012).

## 3. Running Example (Shared Across Trilogy)

**Protocol:** Distributed Capacity Pool

A capacity allocation service that scales from a single pool (Paper 1) to a distributed, adaptive system (Papers 2-3). Capacity is a conserved resource: allocations are bounded, audited, and transferable.

**Paper 1 scope:** Single pool, establishing Coherence fundamentals.

Roles:
- **P** (Pool) — holds and allocates capacity
- **C** (Client) — requests and consumes capacity
- **M** (Monitor) — tracks allocations, enforces accounting

Base flow:
```
C -> P : Request(n)      // request n units of capacity
P -> C : Grant(k)        // grant k ≤ n units
C -> M : Report(k)       // report allocation to monitor
M -> P : Confirm         // monitor confirms booking
P -> C : Token(t)        // capability token for allocated capacity
```

The `Token(t)` payload is a transferable capability—ordinary payload in Paper 1, delegation vehicle in Paper 3.

**Paper 1 checkpoints (explicit):**

1. *Coherence check on send step* (`P -> C : Grant(k)`):
   - Three-way edge split applied: updated edge (P,C), shared-endpoint edges ((P,M), (C,M)), unrelated edges (none in this 3-party protocol).
   - Updated edge: local type at P advances past send, buffer (P,C) gains `Grant(k)`.
   - Shared-endpoint edges: irrelevance lemmas discharge—types and buffers unchanged.
   - `EdgeCoherent` re-established on all active edges.

2. *Consume check on receive step* (`C` receives `Grant(k)` from buffer):
   - Buffer (P,C) contains `[Grant(k)]`.
   - C's local type expects `?P.Grant`.
   - `Consume([Grant(k)], ?P.Grant.T')` returns `T'` with empty residual.
   - `Consume_cons` lemma discharges the alignment obligation.

3. *Session evolution* (type refinement):
   - Suppose P's `Grant` type is refined to a subtype (e.g., `Grant(k)` where `k ≤ n` is made explicit in the type).
   - `Consume_mono` ensures Coherence is preserved under this async subtype replacement.

**Cross-paper evolution:**
- Paper 2 adds quantitative dynamics: W₀ = 25, phase threshold Bc = 2, crash tolerance.
- Paper 3 scales to distributed pools with adaptive coordination and typed guards.

Figure placement: protocol timeline with buffer snapshots at the Grant-in-transit and Token-in-transit states, annotated with Coherence/Consume check points.

## 4. Coherence Preservation Architecture
1. Main preservation theorem statement.

**The Quotient Structure**

Session-typeable systems have dynamics on a quotient:

> **Evolution happens on S/G, where S is the state space, G is the symmetry group, and Coherence is the invariant that survives the quotient.**

A configuration is not a point but an equivalence class. Two configurations are equivalent if they differ only by Coherence-preserving symmetries (role renaming, carrier reassignment, resource re-identification). The preservation theorem says this commuting square holds:

```
     C  ─────step─────▶  C'
     │                   │
  quotient            quotient
     │                   │
     ▼                   ▼
    [C] ────step────▶  [C']
```

Stepping a concrete configuration then quotienting gives the same result as quotienting first then stepping on the quotient. The top row is concrete execution (specific roles, carriers, resources). The bottom row is dynamics on equivalence classes. The vertical maps forget inessential details.

This explains why the frame rule works: operations on disjoint sessions are symmetries from each other's perspective, mapping to the identity on the quotient. Paper 3 extends this by showing delegation is also a Coherence-preserving symmetry, enlarging G to include carrier permutations.

2. Three-way edge split:
   - updated edge
   - shared-endpoint edges
   - unrelated edges
3. Reusable irrelevance/frame lemmas.
4. Worked instantiation on the running example send step.
5. Figure placement (essential F3): three-way partition of edges for one transition.

## 5. Message-Type Alignment via `Consume` Lemmas
1. Recursive alignment function `Consume`.
2. Key lemmas:
   - `Consume_append`
   - `Consume_cons`
3. How send/recv preservation obligations reduce to these lemmas.
4. Worked instantiation on the running example receive step.

## 6. Session Evolution via Subtyping
1. Asynchronous subtyping assumptions.
2. Monotonicity theorem `Consume_mono`.
3. `Coherent_type_replacement` and `Coherent_session_evolution`.
4. Running-example local-type refinement and preserved Coherence.
5. Figure placement (essential F4): commuting square (replace type then check vs check then monotonicity).

## 7. Mechanization and Artifact Summary
1. Theorem-to-file mapping for core claims.
2. Reusable proof kernels (`Consume`, edge-split infrastructure).
3. Artifact reproducibility summary.
4. Table placement: mechanization footprint table.

## 8. Extended Artifact: Effect-Typed Bridge (Brief)
1. `choreography -> effects -> VM` bridge summary.
2. `EffectModel.handlerType` obligations.
3. Why this is presented as supporting artifact scope here.

Claim-scope note: coinduction at this layer is used only for extensional effect equivalence bridges (observer equality, congruence, quotient compatibility). Finite-step preservation internals remain in the inductive Coherence/Consume stack.
4. Table placement: bridge-obligation checklist (core obligations only).

## 9. Related Work and Delta
1. Binary duality and global re-derivation strategies.
2. **Mechanization pressure (ECOOP 2025):** Tirore-Bengtson-Carbone found issues in classical MPST subject reduction, reinforcing why local-invariant architectures matter. Our three-way edge split is a cleaner, more reusable skeleton than per-step global re-derivation.
3. **Actris distinction:** Actris (POPL 2020, LMCS 2022) is a *program logic* for verifying code against session-like protocols inside Iris. Coherence is a *semantic invariant kernel* for the MPST operational semantics itself—designed to support quotienting, preservation, and (in Papers 2-3) macroscopic dynamics and reconfiguration. Different layers, complementary goals.
4. **Event-structure semantics (JLAMP 2023):** Another "macro over micro" approach using partial orders to capture concurrency. We use quotients by Coherence-preserving symmetries—a different but related move away from over-committing to microstructure.
5. **Quotient-first novelty:** Recent literature (2021-2025) has improved mechanization and fault tolerance separately; we treat quotient-state semantics as a central architectural framing, with novelty scope aligned to the trilogy-level survey claim.
6. Delta of this paper's architecture.
7. Table placement: prior-work delta table.

## 10. Limitations and Scope Boundaries
1. What is proved here (preservation + evolution).
2. What is deferred to Paper 2 (computable dynamics, crash-stop fault tolerance with exact decidability) and Paper 3 (reconfiguration Harmony, minimality).
3. **Fault model note:** The Coherence architecture supports crash-stop faults (participants may crash, leaving edges inactive). Paper 2 proves exact decidable characterization; this paper establishes the invariant that makes that possible.
4. Table placement: in-scope vs deferred map.

## 11. Conclusion
1. Coherence as the reusable invariant kernel.
2. Session evolution robustness via `Consume_mono`.

## Main Theorem Slots
1. Coherence Preservation Theorem.
2. Session Evolution Theorem via `Consume_mono`.

## Appendices

## Appendix A. Formal Preliminaries and Notation
1. Full syntax and environment definitions (`GEnv`, `DEnv`, `Edge`, `ActiveEdge`).
2. Step rules and typing judgments.
3. Auxiliary lookup/update lemmas.

## Appendix B. Full Preservation Proof Details
1. Full proof script structure for the three-way split.
2. Updated-edge lemmas (send/recv/select/branch).
3. Shared-endpoint irrelevance lemmas.
4. Unrelated-edge transport lemmas.

## Appendix C. Consume and Session Evolution Library
1. Recursive `Consume` definition and fuel/termination setup.
2. `Consume_append` and `Consume_cons` proofs.
3. `RecvSubtype_refl`, `consumeOne_mono`, `Consume_mono`.
4. `Coherent_type_replacement` and `Coherent_session_evolution`.
5. Running-example proof excerpts.

## Appendix D. Delivery + Effect Bridge Details
1. `DeliveryModel` law set and instance obligations.
2. FIFO/causal/lossy details.
3. Effect signature and `EffectModel.handlerType` obligations.
4. Bridge lemmas to VM instruction typing.

## Appendix E. Mechanization Inventory
1. File-level inventory and line counts.
2. Mapping from theorem statements to files.

## Appendix F. Reproducibility Notes
1. Build commands.
2. Theorem index by file.
3. Artifact checklist.

---

# Paper 1 Supplementary Artifact Outline

## Scope
Non-spine artifact contributions supporting the Paper 1 ecosystem.

## Extended Artifact Contributions
1. Coherence invariant replacing binary duality.
2. Consume function with append/cons decomposition.
3. Three-way edge-case infrastructure.
4. Model-parametric delivery (FIFO, causal, lossy).
5. Effect-typed execution model with `EffectModel.handlerType`.
6. Session evolution via `Consume_mono`.
7. Coinductive-inductive roundtrip (`toCoind_toInductive_eq2ce`).
8. Three-algorithm Harmony (`trans`, `projectb`, `projectR?`).
9. Erasure/Blindness/Embedding decomposition.
10. Noninterference exactness pack: blind-step observational invariance with an explicit non-blind counterexample witness interface.
11. Information-cost exactness pack: under the stated model/assumption bundle, blindness implies zero CMI; reverse direction (`mutualInfo = 0 ↔ erasure-kernel`) comes with assumption-indexed sharpness witnesses and degenerate-model boundary interfaces.
12. Conservation from symmetry: `automorphism_equivariant`.
13. Five-domain compositional VM model.
14. Iris-style program logic with WP rules.
15. Verified executable simulation (`stepDecide_sound`).

## Suggested Use In Submission Package
1. Keep main-paper artifact pointer concise.
2. Link this supplement from artifact README.
3. Map each contribution to file paths and theorem names.
