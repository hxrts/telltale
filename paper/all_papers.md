# Three Papers on Coherence

**Last updated:** 2026-02-10 (revised per literature review + envelope integration)

## Documents

**Papers**
- [Paper 1: Coherence for Asynchronous Buffered MPST](paper1.md)
- [Paper 2: Computable Dynamics for Asynchronous MPST](paper2.md)
- [Paper 3: Harmony from Coherence in Asynchronous MPST](paper3.md)

**Outlines**
- [Outline 1](outline1.md)
- [Outline 2](outline2.md)
- [Outline 3](outline3.md)

---

## The Arc

Three papers that trace the classical boundary in distributed systems.

## Byzantine Safety Track Status

The current paper set includes a scoped Byzantine safety extension with three aligned statement classes.

1. Exact characterization under explicit assumptions: $\mathsf{ByzSafe} \iff \mathsf{ByzChar}$ with bundle $H_{\mathrm{byz}}$.
2. Converse sharpness: dropped-assumption counterexample families for quorum or intersection, authentication or evidence validity, adversarial budget, and primitive consistency.
3. VM bridge and capability gating: runtime claims must be backed by theorem-pack Byzantine artifacts and envelope-adherence artifacts.

Shared notation for this track is fixed across papers as:
- $H_{\mathrm{byz}}$ for the Byzantine assumption bundle.
- $\mathsf{Obs}_{\mathrm{safe}}^{\mathrm{byz}}$ for Byzantine safety-visible observation projection.
- $\mathsf{Eq}_{\mathrm{safe}}^{\mathrm{byz}}$ for Byzantine safety-visible observational equality.
- $\mathcal E_{\mathrm{byz}}$ for Byzantine determinism-envelope relation.

**Novel combination (per literature review).** In our surveyed 2021-2025 corpus, work improves mechanization (ECOOP 2025), fairness-sensitive liveness (JLAMP 2024, CONCUR 2022), and fault tolerance largely in separate threads; the specific combination of (i) quotient state space as semantic object, (ii) macroscopic observables on equivalence classes, and (iii) commutation theorems for reconfiguration that enlarge the symmetry group appears uncommon. This trilogy develops that combined line.

### Trilogy-Strengthening Priorities (Current Recommendation)

The following additions are prioritized by "strengthens the trilogy spine" rather than novelty alone:

1. **[Formal, spine] Exact characterization of the execution determinism envelope.**
   - Strengthen to **exact envelope characterization** (under the stated model/assumption bundle): soundness + realizability + maximality.
   - Pairs directly with Paper 3's existing relative minimality theorem (`Coherence` as weakest admissible invariant).
   - Narrative symmetry: weakest admissible invariant + exactly characterized admissible diff relation.
2. **[Formal, spine] Exchange-normalized determinism with spatial-subtyping monotonicity.**
   - Tightens the symmetry/quotient story by making admissible reorderings and refinement monotonicity theorem-level.
3. **[Formal, bridge] Observational adequacy plus abstract-to-VM adherence.**
   - Connects abstract/protocol proofs to executable runtime conformance as first-class theorem artifacts.
4. **[Consequence, secondary] Admission theorem (`D_user ⊆ D_prog ⊆ Envelope`).**
   - Strengthen to **principal capability + admission completeness** (not only one-way safety).
   - Keep as corollary/application layer rather than spine theorem.
5. **[Program, deferred] Full failure/recovery envelope program.**
   - Valuable but scope-heavy; defer beyond the trilogy submission spine to avoid dilution.

### Scope and Claim Types

This document is intentionally speculative and written against the **intended end-state** (all target proofs completed). To avoid ambiguity, claims should be read with the following tags:

- **[Formal]**: statement intended as a theorem/mechanized result in the Lean model.
- **[Consequence]**: direct model-level implication of formal results.
- **[Interpretation]**: conceptual framing (physics/semantics perspective).
- **[Program]**: roadmap or research direction, not yet a theorem statement.

### Model Assumptions (for all absolute claims)

All "exact", "unique", and boundary claims are scoped to the formal model used in these papers:

- asynchronous buffered MPST semantics under **arbitrary fair scheduling** with per-edge `Consume` and `Coherent`
- **parametric delivery models** (FIFO, causal, lossy) via `DeliveryModel` typeclass—not restricted to FIFO
- active-edge coherence (`ActiveEdge`: both sender and receiver endpoints exist)
- **crash-stop fault tolerance** with exact decidable characterization via residual communication graph connectivity
- **dynamic participant sets**: roles can join mid-protocol via delegation, leave via crash or delegate-then-crash; `link` composes sessions
- classical payloads (including channel capabilities as classical names)
- regularity/finite-state assumptions where required for decidability/bounds
- fairness/scheduling assumptions stated per theorem (productive-step vs total-step bounds distinguished)

**The core insight [Formal+Consequence]:** Erasure is the semantics. In this model, session-typeable systems evolve on a quotient space: two configurations are equivalent if they differ only by Coherence-preserving symmetries. The three papers identify safe erasures (the model's classical boundary) and characterize Coherence as the canonical invariant supporting that quotient dynamics.

- **Paper 1: Define the quotient.** Introduces Coherence, the invariant that characterizes when projection (the micro→macro map) is well-defined. Proves the quotient is preserved under steps. The invariant is per-edge (local), role-agnostic (identity carries no information), and buffer-aware (classical data only). These properties place us in the classical regime.

- **Paper 2: Dynamics on the quotient.** The Lyapunov function W = 2·Σdepth + Σbuffer is a macroscopic observable, defined on equivalence classes rather than configurations. Its strict decrease is the second law: evidence that the quotient is well-posed. Also: decidable predicates, phase transitions, relaxation bounds.

- **Paper 3: Complete the quotient.** Proves reconfiguration Harmony for `link` + delegation, so projection commutes with topology change. Safe delegation then follows as an operational corollary, making role identity erasable. This enlarges the symmetry group to include all role permutations. The quotient becomes the intended classical statistical-mechanical state space: exchangeable particles, classically representable correlations, and classical dynamics.

**Erasure as semantics.** Each paper addresses a class of erasures:

| Paper | Erasures addressed                                   | What becomes gauge                           |
|-------|------------------------------------------------------|----------------------------------------------|
| 1     | Projection, history, coordinate, **gauge**, observer | Role‑invisible structure of the global state |
| 2     | Time-parameter, fluctuation, initial-condition       | Microscopic trajectory details               |
| 3     | Carrier, resource, permutation, identity             | Role and endpoint identity                   |

Within this model, the classical boundary is where these erasures are safe. Beyond it (entanglement, measurement effects, non-Markovian memory), the assumptions no longer apply.

### Why "Coherence"

**The inevitability argument [Formal].** Coherence is the invariant used to characterize safe coarse-graining in this model. Consider what must hold for projection (the micro→macro map) to be well-defined:

1. Each role's local view must be consistent with the global state
2. This consistency must be preserved when the system steps
3. The check must be local (otherwise projection wouldn't decompose per-role)
4. The check must be role-agnostic (otherwise identity would carry information that projection erases)

These requirements select Coherence in the current formulation. `EdgeCoherent` checks whether a receiver can handle its incoming buffer, the minimal information needed to ensure the local view is consistent. Any weaker invariant would allow configurations where projection loses essential information (safety failure). Stronger invariants may fail preservation under coarse-graining.

**Coherence = compatible marginals.** In classical probability, marginals do not in general uniquely determine a joint distribution; they provide compatibility constraints. A set of marginals is *consistent* if they could have arisen from some joint distribution. Coherence is the operational version: a configuration is Coherent if every **active edge** (an edge where both sender and receiver endpoints exist) has a local view that could have arisen from a well-typed global protocol. In Lean: `Coherent G D := ∀ e, ActiveEdge G e → EdgeCoherent G D e`. This is a hallmark of classical probabilistic modeling in this setting, and why Coherence characterizes the boundary studied here.

**Coherence = erasure-safe compatibility.** There's a deeper way to see this. Two local views are *coherent* if they can coexist, if you don't need to distinguish between them because they're mutually compatible. Two local views are *incoherent* if one excludes the other, requiring you to track which one you have. The coherence relation *is* the structure of what survives erasure. A Coherent configuration is a maximal set of mutually compatible local views, exactly what remains after erasing the incompatible alternatives.

This is the same insight that underlies **Girard's coherence spaces** (1987), the standard denotational model for linear logic. A coherence space is a set of tokens with a reflexive symmetric binary relation (the coherence relation). The *points* are cliques, subsets where all pairs are coherent. Two tokens are *incoherent* if they represent mutually exclusive resource uses: you can have one or the other, not both. A clique is a maximal consistent subset, what survives when you erase the incompatible possibilities.

| Coherence spaces                      | Telltale Coherence                                          |
|---------------------------------------|-------------------------------------------------------------|
| Token                                 | Directed edge (A, B, s) with buffer and local type          |
| Coherence relation                    | `EdgeCoherent`: buffer compatible with receiver's type      |
| Incoherence                           | Incompatible demand: receiver can't handle what's in buffer |
| Clique (point)                        | `Coherent` configuration: all **active** edges coherent     |
| Linear map preserves cliques          | Preservation theorem: steps preserve Coherence              |
| Tensor decomposes componentwise       | Per-edge independence (extensivity / frame rule)            |
| Dual swaps coherence for incoherence  | Sender/receiver asymmetry in `Consume`                      |

The connection runs deeper than terminology. Girard's insight was that linear logic's resource sensitivity is captured denotationally by the coherence relation: "these tokens can coexist, those cannot." The coherence relation *is* the structure of resource compatibility. Points are the denotational content after erasing inconsistent possibilities. Telltale's insight is the operational version: session type safety is captured by `EdgeCoherent`, which checks "these local views are mutually consistent." Coherent configurations are the operational content after erasing what roles can't observe.

Both are instances of the same meta-pattern:

> **Coherence = the invariant characterizing erasure-safe combinations. Cliques/configurations = what survives projection to the observable level.**

This supports a **structural correspondence** with a classical regime. The coherence relation is reflexive and symmetric, a classical binary relation rather than a quantum amplitude or non-commutative structure.

Coherence spaces are the denotational semantics for linear logic, and linear logic is the logical foundation for session types (Caires-Pfenning 2010, Wadler 2012). Telltale's Coherence is an *operational correspondence* to what coherence spaces provide *denotationally*: same compatibility pattern at different abstraction levels, not a claim of full model identity.

The three-paper progression mirrors a known trajectory in coherence space semantics:
- **Paper 1** (first-order Coherence) corresponds to first-order coherence spaces, where tokens are atomic and cliques are sets of compatible values.
- **Paper 2** (dynamics on Coherence) corresponds to linear maps between coherence spaces. Linear maps preserve cliques, just as well-typed steps preserve Coherent configurations. The Lyapunov function W is a morphism to the ordered monoid (ℕ, ≥, +), decreasing under every step.
- **Paper 3** (higher-order Coherence) corresponds to second-order coherence spaces, where tokens are themselves coherence spaces. This is exactly what `ValType.chan` in a buffer represents: a message payload that carries its own session capability.

### The Quotient Structure

At the deepest level, session-typeable systems have dynamics on a quotient:

> **Evolution happens on S/G, where S is the state space, G is the symmetry group, and Coherence is the invariant that survives the quotient.**

A configuration is not a point but an equivalence class. Two configurations are equivalent if they differ only by:
- Role renaming (identity/permutation erasure)
- Carrier reassignment (delegation erasure)
- Resource re-identification (nullification erasure)

All three are Coherence-preserving symmetries. The unified correctness criterion:

> **A transition is valid iff it preserves Coherence on the quotient.**

The commuting square:

```
     C  ─────step─────▶  C'
     │                   │
  quotient            quotient
     │                   │
     ▼                   ▼
    [C] ────step────▶  [C']
```

The square commutes: stepping a concrete configuration then quotienting gives the same result as quotienting first then stepping on the quotient. This is the content of the preservation theorem. The top row is concrete execution (specific roles, carriers, resources). The bottom row is dynamics on equivalence classes (what theorems are about). The vertical maps forget the inessential details.

All proofs happen in the bottom layer. The top layer exists only to implement the quotient. This is why the frame rule works: operations on disjoint sessions are symmetries from each other's perspective, so they map to the identity on the quotient. This is why delegation preserves Coherence: it's a symmetry that permutes carriers while preserving the equivalence class.

### Physics connection [Interpretation]

"Coherence" in physics means consistent local descriptions, the defining property of classical systems.

1. **Erasure as coarse-graining.** The micro/macro distinction in statistical mechanics is characterized by erasure: you coarse-grain away particle identities to get thermodynamic quantities. In session types, projection is exactly this operation, erasing interactions you're not party to. The information-theoretic exactness result under the stated model/assumption bundle is: blindness implies zero CMI unconditionally, while the reverse direction is proved through an explicit erasure-kernel condition (`mutualInfo = 0 ↔ erasure-kernel`) with boundary witnesses when assumptions are dropped. The classical boundary is precisely where coarse-graining is safe, where microscopic and macroscopic descriptions are related by pure information loss rather than physical disturbance.

2. **Phase transitions.** Paper 2's buffer phase transition at critical capacity B_c is the boundary between a coherent regime (progress guaranteed) and an incoherent regime (deadlock possible). This is classical statistical mechanics: a sharp transition in macroscopic behavior at a critical parameter value.

3. **Orders of coherence.** First-order Coherence checks edge-level compatibility (two-point: sender type, receiver buffer). Higher-order Coherence checks edges carrying capabilities, where the message itself has internal structure. The Paper 1 → Paper 3 progression mirrors the standard hierarchy in physics: first-order correlations, then correlations of correlations.

4. **The classical regime.** Session-typeable systems in this model exhibit structural properties of classical statistical mechanics: identity becomes gauge (exchangeability), correlations are classically representable (no entanglement in the model semantics), dynamics live on classical state spaces (simplices, manifolds, measure spaces), and ergodicity becomes meaningful. Systems requiring entanglement, non-local quantum correlations, or unitary Hilbert-space evolution fall outside this erasure-safe MPST setting and need richer semantics (e.g., quantum MPST extensions). Within the classical regime, classical reasoning tools apply. Typing provides structural hypotheses, and classical theorems' conclusions follow when the remaining analytic conditions hold.

5. **Noether's theorem.** Symmetries imply conservation laws. Protocol automorphisms (role permutations that preserve the communication structure) are the symmetries of session types. The theorem `automorphism_equivariant` proves that dynamics commute with symmetries: if φ is an automorphism, then stepping and then applying φ equals applying φ and then stepping. What's conserved? The balanced communication structure itself. Every send has a matching receive, and messages are created and destroyed in pairs. This is a continuity equation: communication flow is conserved. The Noether perspective also illuminates delegation: when roles become interchangeable (Paper 3), the symmetry group enlarges, and more quantities become "conserved" in the sense of being invariant under the larger group. Identity becoming gauge is the statement that the symmetry group includes all role permutations.

### Separation logic as operational witness

Coherence's per-edge structure is not just a mathematical convenience but what enables *modular concurrent proofs*. The separation logic machinery (Iris, ghost state, WP rules) is the **operational witness** that Coherence actually delivers on its promise.

**The connection:**

1. **Coherence = compatible marginals.** Each edge's local view is compatible with at least one global state.
2. **Consistent marginals = separable resources.** If edges are independent, they can be reasoned about independently.
3. **Separable resources = separation logic applies.** The frame rule (∀P Q R, {P} c {Q} → {P ∗ R} c {Q ∗ R}) requires that R (the "frame") is unaffected by c. Coherence's per-edge locality is exactly this: stepping edge e doesn't affect edge e'.
4. **Separation logic = concurrent preservation.** The cross-session diamond (R.1 in implementation) proves that steps on disjoint sessions commute. This is the concurrent analogue of preservation: not just "steps preserve Coherence" but "concurrent steps preserve Coherence without interference."

**Why the machinery is necessary:**

- **Type unfolding tracking.** `Consume` walks the receiver's type against the buffer. Each step unfolds one layer of the type. The ghost state tracks this unfolding: `session_progress_supply` records which type state each endpoint is in. Without this, we couldn't prove that concurrent steps unfold types consistently.

- **Step length tracking.** The Lyapunov measure W = 2·depth + buffer decreases by a known amount per step type. The WP rules (`wp_lift_step_with_cost`) charge this cost against a budget. This connects the abstract measure to concrete execution: each coroutine step consumes from its budget, and the budgets are separable resources.

- **Concurrent branch tracking.** When two coroutines step concurrently, we need to prove they don't interfere. The three-way edge analysis (updated/shared-endpoint/unrelated) from preservation becomes the frame rule: the updated edge is the footprint, shared-endpoint edges are in the frame, and unrelated edges are trivially framed.

**The payoff:** Without separation logic, "concurrent execution preserves Coherence" would be a single monolithic proof. With separation logic, it factors into:
- Per-instruction commutativity lemmas (the cross-session diamond)
- Per-resource ownership transfer lemmas (ghost state updates)
- A generic frame rule that composes them

This factorization is not just proof engineering but the computational content of Coherence's claim that "edges are independent." If we couldn't factor the proof, Coherence wouldn't really be per-edge.

**The three-paper progression.** Paper 1 enforces classical structure and defines the coarse-graining (projection). Paper 2 shows the tools of classical analysis apply (Lyapunov functions, phase transitions), evidence that we're in the classical regime. Paper 3 completes the picture by proving Harmony under topology change, with delegation-safety as the key consequence, enabling theorem transport from classical dynamics. The progression: **enforce → apply → extend**.

---

## Paper 1: Coherence for Asynchronous Buffered MPST

*Subtitle:* A Mechanized Metatheory with Effect-Typed Execution Bridge

**Target venue:** POPL / ICFP

**Thesis.** Mechanized metatheory for asynchronous buffered multiparty session types, with a verified execution model via algebraic effects. Built on a single per-edge invariant that is preserved by protocol steps, robust under subtype replacement, and parametric over delivery semantics.

### Primary Claims (Submission Focus)

1. **[Formal] Coherence Preservation Theorem**: per-edge active-edge Coherence replaces global re-derivation in asynchronous buffered MPST proofs and is preserved by protocol steps.
2. **[Formal] Session Evolution Theorem via `Consume_mono`**: asynchronous subtype replacement preserves Coherence.

### Secondary Claims (Artifact Scope)

Additional mechanization results (delivery/effects bridge, projection variants, information-theoretic projection, simulation, Iris integration) remain part of the full artifact but are secondary to the paper's central theorem story.

### Prior Work Delta

| Prior limitation | This paper's delta |
|------------------|--------------------|
| Binary-duality-centered preservation in asynchronous settings | Per-edge `EdgeCoherent` + reusable 3-way proof skeleton |
| Delegating from global re-derivation after each step | Local edge reasoning with stable preservation interface |
| Weak connection from metatheory to execution model | Explicit effect-typed bridge (`EffectModel.handlerType`) |
| FIFO-only delivery assumptions | Parametric delivery models (FIFO, causal, lossy) via typeclass |
| Mechanization brittleness (ECOOP 2025 found issues in classical MPST proofs) | Local-invariant architecture with single discharge point (`Consume_mono`) |

### Recent Literature Positioning

- **ECOOP 2025 mechanization (Tirore-Bengtson-Carbone):** Found issues in classical MPST subject reduction—our three-way edge split is a cleaner, more reusable skeleton.
- **Actris (POPL 2020, LMCS 2022):** Program logic for verifying code; Coherence is a semantic invariant kernel for operational semantics—different layers, complementary goals.
- **Event-structure semantics (JLAMP 2023):** Another "macro over micro" approach using partial orders; we use quotients by Coherence-preserving symmetries.

### Six Novel Techniques

**1. Coherence invariant.** A per-edge, buffer-aware safety invariant that replaces binary duality. Each directed edge is checked independently: can the receiver handle what's in the pipe? No global type re-derivation during preservation.

```lean
def EdgeCoherent (G : GEnv) (D : DEnv) (e : Edge) : Prop :=
  let trace := lookupD D e
  forall Lrecv, lookupG G receiverEp = some Lrecv ->
    exists Lsender, lookupG G senderEp = some Lsender /\
      (Consume e.sender Lrecv trace).isSome
```

**Why it's novel.** The standard MPST approach inherits binary duality, checking that two endpoint types are "dual." For multiparty, the literature (Coppo et al. 2016, Scalas & Yoshida 2019) either encodes multiparty as nested binary sessions (losing the global structure), or uses a global type as reference (requiring re-establishment after every step). Coherence is local (no global type re-derivation), compositional (edges don't interfere), and buffer-native.

**Three structural properties** that become significant in Paper 3:
- *Per-edge locality*: no action at distance, the invariant decomposes into independent per-edge checks.
- *Role-agnostic*: `EdgeCoherent` checks whether *the receiver* can handle the buffer, not *which* role is the receiver. Role identity carries no information the invariant depends on.
- *Classical data*: buffers contain values, not superpositions. The receiver's state after consuming a message is determined by the message content alone.

**2. Consume function.** A recursive buffer-compatibility check that walks buffered messages against the receiver's local type. Two key lemmas drive every preservation proof:
- `Consume_append`: licenses send preservation. Appending a message to the buffer is coherent iff the post-consumption type can handle one more receive.
- `Consume_cons`: licenses receive preservation. Dequeueing decomposes as consuming the head then the tail.

**Borrows from:** Actris (Hinrichsen et al. 2020) for the buffer-compatibility-via-message-walk pattern. Novel contribution: multiparty per-edge instantiation with append/cons decomposition driving a uniform preservation skeleton.

**3. Three-way edge case analysis.** Every preservation proof follows the same structure:
1. **Updated edge**: the edge whose buffer was modified. Use `Consume_append` or `Consume_cons`.
2. **Shared-endpoint edge**: involves the modified role but different edge. Frame-like irrelevance.
3. **Unrelated edge**: old coherence carries through unchanged.

**4. Model-parametric delivery.** The metatheory is parametric over the delivery model. FIFO, causal, and lossy delivery are all instances of a `DeliveryModel` structure with algebraic laws. A new delivery model needs only four axioms, and all metatheory follows automatically.

**5. Effect-typed execution model.** A three-layer architecture (choreography → effect algebra → VM bytecode) where `EffectModel.handlerType` maps every effect action to the session type it must satisfy.

**6. Session evolution via Consume monotonicity.** Coherence is robust under asynchronous subtype replacement: if `AsyncSubtype L L'`, then replacing role r's local type from L to L' preserves Coherence. The key lemma `Consume_mono` shows buffer compatibility is monotone under subtyping. This demonstrates that Coherence is the right invariant: preserved not only by protocol steps but also by protocol evolution. (Paper 3 extends this: evolution and delegation unify through `Consume_mono`, where the delegatee's existing type merges with the delegated type via the same lemma.)

**Mechanization.** `RecvSubtype_refl`, `consumeOne_mono`, `Consume_mono`, `Coherent_type_replacement`, and `Coherent_session_evolution` are all proved, establishing session evolution via Coherence preservation.

### Extended Artifact Contributions

The full artifact includes the following additional contributions:

1. Coherence invariant replacing binary duality
2. Consume function with append/cons decomposition
3. Three-way edge case analysis
4. Model-parametric delivery (FIFO, causal, lossy)
5. Effect-typed execution model with `EffectModel.handlerType` bridge
6. Session evolution via `Consume_mono`
7. Coinductive-inductive roundtrip (~2,500 lines): `toCoind_toInductive_eq2ce`
8. Three-algorithm Harmony: `trans`, `projectb` (sound + complete), `projectR?` (proof-carrying)
9. Erasure/Blindness/Embedding decomposition: `projectable_of_wellFormedBlind` (the micro/macro interface)
10. Noninterference exactness pack: blind-step observational invariance with explicit non-blind counterexample witness interface
11. Information-cost exactness pack (under the stated model/assumption bundle): blindness -> zero CMI, plus reverse (`mutualInfo = 0 ↔ erasure-kernel`) with assumption-indexed sharpness witnesses and degenerate-model boundary witnesses
12. Conservation from symmetry: `automorphism_equivariant` for all 4 step types
13. Five-domain compositional VM model
14. Iris-style program logic with weakest-precondition rules
15. Verified executable simulation with `stepDecide_sound`

### Narrative [Interpretation]

This addresses three gaps simultaneously. First, the 20-year community goal of mechanized MPST for the real asynchronous buffered setting. Coherence is a genuinely new proof architecture, not mechanization of known strategies. The mechanization (~290 files, ~80K lines) is an order of magnitude beyond prior MPST formalizations. Second, the gap between session type theory and executable programs: the algebraic effect model provides a formally connected execution pipeline. Third, the deployment gap: session evolution via `Consume_mono` shows that Coherence handles not just protocol execution but also protocol upgrade.

The "quotient-first" approach—defining Coherence to characterize a quotient state space—is the architectural stance used throughout this trilogy (with novelty scope stated in the opening literature-positioning claim above).

### Provenance

| Technique               | Borrows from                                                 | Novel contribution                                                          |
|-------------------------|--------------------------------------------------------------|-----------------------------------------------------------------------------|
| Coherence invariant     | Coppo et al. compatibility, separation logic frame rule      | Per-edge buffer-aware invariant eliminating global type from preservation   |
| Consume function        | Actris (Hinrichsen et al. 2020) buffer walk pattern          | Multiparty per-edge instantiation with append/cons driving uniform preservation |
| Three-way edge analysis | Binary session type case splits (Gay & Hole), separation logic framing | Systematic multiparty generalization with reusable irrelevance lemmas       |

### Mechanization

~27,188 lines in Protocol layer. `Preservation.lean` (1,933 lines). `Typing/Preservation.lean` (2,137 lines, largest single proof). `InformationCost.lean` (976 lines). ~12,914 lines SessionCoTypes (coinductive EQ2, bisimulation, async subtyping). ~16,251 lines Choreography/projection (three algorithms, Harmony). ~13,736 lines Runtime (EffectModel, ProgramLogic, Iris backend, VM with instruction specs).

---

## Paper 2: Computable Dynamics for Asynchronous MPST

*Subtitle:* Lyapunov Descent, Capacity Thresholds, and Uniform Decision Procedures

**Target venue:** POPL

**Thesis.** A unified computable-dynamics metatheory for asynchronous MPST: one quantitative theorem for termination dynamics and one algorithmic theorem schema for decidability.

### Prior Work Delta

| Prior limitation | This paper's delta |
|------------------|--------------------|
| Mostly qualitative liveness ("terminates under fairness") | Quantitative productive-step bounds via weighted Lyapunov function |
| Decidability fragments treated separately | Unified finite-reachability proof pattern across decision problems |
| Capacity/branch feasibility often heuristic | Exact single-shot combinatorial characterization (confusability graph) |
| Crash tolerance as separate concern | Exact decidable crash-stop tolerance with iff-characterization + non-monotonicity proof |

### Recent Literature Positioning

- **Fair termination (JLAMP 2024, CONCUR 2022):** Type systems guarantee termination under fairness. Our Lyapunov approach is complementary: they give type-theoretic liveness *guarantees*; we give *quantitative bounds* on a quotient. Both valuable; ours adds the numbers.
- **ECOOP 2025 mechanization:** Validates that MPST meta-theory is brittle—our unified decidability schema derives multiple results from one regularity kernel.
- **DS positioning:** We're not proving a protocol correct; we're giving a *canonical reduction principle* (quotient + invariant) that explains when a class of typed distributed systems admits stable macroscopic reasoning.

### Two Central Theorems (Submission Spine)

**Theorem 1 [Formal]: Quantitative Dynamics.**  
Let W(C) = 2·Σdepth(C) + Σbuffer(C). For any well-typed configuration C:
- W is nonnegative and reaches 0 exactly at quiescence.
- Every productive step strictly decreases W by a known amount.
- Any fair execution terminates in at most W₀ productive steps (tight in productive-step semantics).
- Under explicit scheduler assumptions (round-robin / k-fair), this lifts to explicit total-step bounds.

This is the paper's primary quantitative claim: protocol liveness becomes a computable numeric bound, not only a qualitative fairness statement.

**Theorem 2 [Formal]: Algorithmic Dynamics Schema.**  
For regular local types, reachable protocol-state spaces are finite and effectively enumerable. Therefore any property reducible to graph reachability/fixpoint checks on that finite graph is decidable.

This is the paper's primary algorithmic claim: multiple decision procedures are instances of one finite-reachability proof pattern rather than isolated constructions.

### Main Corollaries (Core Paper)

**1. Additive compositionality [Formal+Consequence].**  
For disjoint sessions with measures W₁, ..., Wₖ, productive work composes additively (W₁ + ... + Wₖ). Scheduler assumptions then lift this to composed total-step bounds.

**2. Critical capacity threshold B_c [Formal+Consequence].**  
The buffer threshold B_c is computable from type structure and marks a sharp qualitative boundary (progress guaranteed vs deadlock-permitting regimes under bounded-buffer semantics).

**3. Asynchronous subtyping decidability [Formal].**  
`AsyncSubtype S T` is decidable for regular types.

**4. Type equivalence decidability [Formal].**  
Bisimulation for regular coinductive session types is decidable via finite reachable-pairs construction.

**5. Branching feasibility [Formal].**  
Branching feasibility is decidable via the confusability/chromatic-number criterion.

### Core Decidability Results

**Theorem 3 [Formal]: Exact Crash-Stop Tolerance.**
For any finite protocol G and crash set F:
1. `CrashTolerant G F` is decidable via residual communication graph connectivity.
2. Exact iff-characterization: crash set F is tolerable iff the residual graph remains connected.
3. **Non-monotonicity:** The crash-tolerance relation is non-monotone—adding an intermediary can break tolerance. Proved constructively.

This is stronger than "decidable"—we have tight characterization with explicit counterexamples.

### Additional Instantiations (Appendix/Artifact Scope)

- Expanded mechanization inventory and per-file accounting.

### Proof Architecture

**Quantitative side.** The Lyapunov argument proves strict descent of W under productive well-typed steps. Together with fairness and scheduler models, this yields computable time-to-termination bounds.

**Algorithmic side.** A single finite-state exploration skeleton (reachable-set enumeration with visited-set termination) is instantiated across subtyping/equivalence and other decision predicates.

**Interpretive note [Consequence].** The W argument has the same monotone-state-function form as classical relaxation analysis. In this document's arc, Paper 2 uses that structure for computable dynamics; full cross-domain theorem transport is intentionally deferred to Paper 3 after the boundary characterization.

### Narrative [Interpretation]

Paper 2 turns "well-typed programs make progress" into a computable dynamics theory with two explicit outputs: numeric termination bounds and executable decision procedures.

The first main theorem gives a state-function descent law (W) and therefore quantitative liveness. The second gives a reusable finite-reachability algorithmic schema and therefore decidability families. The third gives exact crash-stop tolerance with iff-characterization and non-monotonicity proof. Together they make protocol analysis predictive and automatable.

This is what makes Paper 2 co-equal with Papers 1 and 3 in the arc: Paper 1 defines the invariant structure, Paper 2 makes that structure computationally analyzable, and Paper 3 characterizes where this style of analysis is valid and transportable.

**Fault model boundary:** Results hold for crash-stop faults with exact characterization. Beyond crash-stop (Byzantine behavior, delivery failures outside the chosen `DeliveryModel` assumptions, non-Markovian failures), erasure safety requires additional machinery—this is the boundary of the classical regime.

**Novel combination:** To our knowledge, the field has quotient-level Lyapunov bounds (rare) and unified decidability schemas (rare) separately, but not together with exact crash tolerance. DS usually has per-protocol bounds; PL usually has qualitative liveness. We give quantitative bounds, algorithmic decidability, and crash tolerance from one regularity kernel.

### Mechanization

Core mechanization for the submission spine:
- Lyapunov descent and weighted bounds (`Lyapunov.lean`, Files 09/09b/10b)
- Finite-reachability decidability pattern (`reachablePairs_finite`, Files 05/05b, bisimulation development)
- Compositional dynamics support (cross-session diamond)

**Appendix reference [Program].** Expanded instantiations and full Paper 2 file inventory are listed in **Appendix C** below.

---

## Paper 3: Harmony from Coherence in Asynchronous MPST

*Subtitle:* A Minimal Erasure Invariant for Classical Dynamics

**Target venue:** POPL

**Thesis.** The primary claim is Harmony under topology change: for well-formed `link`/delegation reconfiguration and subsequent protocol steps, projection commutes with evolution (`project ∘ step_reconfig = local_step_reconfig ∘ project`). Coherence is the minimal erasure-stable local invariant that makes this commutation law hold, and safe delegation is the key operational corollary. This makes roles structurally interchangeable in composed systems and yields quantitative lift: W is preserved for pure reconfiguration (composition + delegation), while transition choreographies are controlled by descent/budget bounds. Session-typeable systems therefore satisfy the structural hypotheses needed for classical-style theorem transport.

### Prior Work Delta

| Prior limitation | This paper's delta |
|------------------|--------------------|
| Delegation/topology change often dropped in mechanized MPST due to invariant breakage | Reconfiguration-Harmony theorem covering `link` + delegation with active-edge semantics |
| Static composition and dynamic delegation proved separately | Unified Harmony treatment via `Consume_mono` and composed/delegated setting |
| Physics analogy without applicability contract | Explicit theorem-transport workflow with assumptions and checks |
| Sufficient conditions without minimality | Relative minimality: Coherence is the *weakest* admissible invariant, not just sufficient |

### Recent Literature Positioning

- **Ozone (ECOOP 2024):** Both address "order erasure"—correctness under reordering. Ozone uses futures/reactive-style; we use quotients and Coherence-preserving symmetries. Different mechanisms, related insights.
- **MPST for runtime adaptation (ECOOP 2021):** Language-design safety for component replacement. Our Harmony is a *semantic commutation theorem*—different layer (metatheory vs language design).
- **Commutation + minimality rarity:** MPST literature often provides sufficient conditions without showing minimality in an invariant lattice. Theorem D is comparatively rare.
- **Quantum MPST (SEFM 2024; arXiv:2409.11133):** Explicit exploration of quantum regimes supports the boundary claim: standard erasure-safe MPST semantics do not model entanglement or measurement back-action, so quantum MPST extensions add the required semantics.
- **ECOOP 2025 mechanization:** Validates that MPST is brittle under reconfiguration—our Harmony theorem is designed to be mechanization-friendly via the same Coherence kernel.

### Core Theorem Program (Submission Spine)

Paper 3 is organized as one theorem program with eight mutually reinforcing results:

**Theorem A [Formal]: Erasure Characterization of Coherence.**  
`Coherent` is exactly the realizability condition for global→local erasure: a configuration is Coherent iff its projected local views are jointly compatible (jointly realizable) on active edges.

**Theorem B [Formal]: Reconfiguration Harmony (Static + Dynamic).**  
For any well-typed `C`, any well-formed reconfiguration `rho` (`link` or `delegate`), and any enabled protocol step after `rho`, projection commutes with reconfigured evolution (global-step then project = project then local-step in the reconfigured topology).
Indexed side-condition necessity is packaged with dropped-condition witnesses: when a required Harmony side condition is removed, a strict non-Harmony counterexample can be produced.

**Theorem C [Formal]: Safe Delegation Corollary (Sufficiency + Footprint Exactness Packaging).**  
Under delegation side conditions (`DelegationWF`: active-edge discipline, ownership constraints, mergeability when delegatee already participates):
- `Coherent C ∧ DelegationWF(C, op) → SafeDelegation(C, op)` (sufficiency)
- `SafeDelegation(C, op) ↔ SafeDelegationFootprint(C, op)` (delegation-footprint exactness under explicit step/WF side conditions)
- dropped-side-condition boundary witnesses (strictness when those side conditions are weakened)
- per-clause `DelegationWF` independence packaging (each side condition has an indexed strictness witness interface)

**Theorem D [Formal]: Relative Minimality of Coherence.**  
Define `Admissible(I)` as the conjunction of: locality on active-edge delegation footprints; erasure-stability (`ConfigEquiv` invariance); frame-stability under disjoint-session steps; and delegation adequacy (`I C ∧ DelegationWF(C, op) → SafeDelegation(C, op)`). Then `∀ I, Admissible(I) → (∀ C, I C → Coherent C)`. This makes Coherence the weakest admissible invariant guaranteeing delegation safety.
Closure is packaged explicitly: `Coherent` itself is admissible under the stated model/assumption bundle's locality/frame obligations.

**Theorem E [Formal+Consequence]: Composed-System Delegation Conservation.**  
For systems assembled via `link`, delegation preserves Coherence and Harmony and conserves the Paper 2 weighted measure W = 2·Σdepth + Σbuffer. This is the flagship systems theorem: static composition + dynamic delegation + quantitative conservation in one statement.

**Theorem F [Formal]: Exact Characterization of the Determinism Envelope.**  
For the stated model/assumption bundle, define the admissible behavior-difference relation `Envelope` and prove:
1. soundness: all admitted target runs stay within `Envelope`,
2. realizability/completeness: every diff in `Envelope` is realizable by an admissible execution,
3. maximality: any strict superset violates safety-visible equivalence or hypothesis constraints.
A duality package theorem links D and F as one exact admissibility-boundary pair: minimal admissible invariant core + maximal admissible behavior envelope.

**Corollary F.1 [Formal]: Rational-Fragment Exactness for Erasure Transport.**  
Within the same stated model/assumption bundle, finite-erasure transportability holds iff behavior lies in the rational (finite-state) coinductive fragment.

**Corollary F.2 [Formal]: Strict Boundary Witness.**  
There exists a coinductive behavior outside the rational fragment and therefore outside finite-erasure transportability.

**Corollary F.3 [Formal]: Syntax-Bridge Exactness on the Inductive Embedding.**  
On the `toCoind` image of inductive local types, rationality and finite-erasure transportability coincide exactly.

**Appendix Corollary F.4 [Formal]: Principal Finite Witness + Adequacy Replay.**  
Every rational behavior admits a canonical principal finite witness, and replay from that witness is extensionally adequate.

**Appendix Corollary F.5 [Formal]: Relative Maximality of the Rational Fragment.**  
Any fragment whose behaviors are all finite-erasure transportable is included in the rational fragment.

**Theorem G [Formal]: Exchange-Normalized Determinism + Spatial Monotonicity.**  
1. Exchange-equivalent executions preserve safety-visible outcomes and remain within the certified envelope class.  
2. Envelope/safety obligations are monotone under admissible spatial subtype refinement.

**Theorem H [Formal+Artifact]: Observational Adequacy and VM Adherence Modulo Envelope.**  
Abstract/protocol envelope theorems transport to VM theorem-pack capabilities, and VM/reference semantics are observationally adequate modulo the declared envelope relation.
A local↔sharded collapse theorem is included: under explicit collapse assumptions, local and sharded exact-envelope characterizations coincide.

Together these results provide erasure meaning (A), semantic commutation under reconfiguration (B), operational delegation safety (C), invariant minimality (D), systems payoff (E), maximality duality for admissible divergence (F), normalization/refinement control (G), and executable conformance transport (H).

**Secondary Corollary S1 [Consequence]: Principal Capability and Admission Completeness.**  
`D_prog` is principal for the chosen profile/inference system, and admission is both sound and complete relative to that principal capability (`D_user ⊆ D_prog` iff admissible under the stated model/assumption bundle).

**Secondary Corollary S2 [Consequence]: Compositional Exactness under Non-Interference.**  
Where explicit independence conditions hold, global envelope composition is exact (not only upper bounded). A converse strictness package is included: when non-interference is dropped, an indexed counterexample witness can certify failure of the exactness conclusion.

**Deferred Program P1 [Program]: Failure/Recovery Envelope.**  
Commit-certainty/restart/reconcile envelope theory is tracked as post-spine work to avoid overload in trilogy submissions.

### The Structural Properties

Session types with Coherence and delegation exhibit the defining properties of classical systems:

| Property                   | Session types                               | Physics                                              |
|----------------------------|---------------------------------------------|------------------------------------------------------|
| **Exchangeability**        | Roles interchangeable via delegation        | Particle indistinguishability in classical stat mech |
| **Local interaction**      | Per-edge Coherence (no action at distance)  | Local Hamiltonians, nearest-neighbor interactions    |
| **Well-posed dynamics**    | Preservation (steps preserve Coherence)     | Deterministic evolution, Liouville's theorem         |
| **Classical correlations** | Buffers hold classical data, no superposition | Classically representable correlations (no entanglement in this model) |
| **Classical state spaces** | Finite sets, simplices, measure spaces      | ODEs, SDEs, kinetic theory, mean-field limits        |

These properties place session-typeable systems in a classical-style regime under the stated model/assumption bundle, where classical reasoning tools apply.

### Why Session Types Land in the Classical Regime

**1. Identity becomes gauge, not structure.** With safe delegation, role identity is eliminable. State lives on a quotient by permutations, and only multisets, measures, and empirical distributions matter. This is exactly the move from labeled classical mechanics to classical statistical mechanics. In classical physics, particles are distinguishable in principle but physical laws are permutation-invariant, so labels carry no observable meaning. Delegation + permutation-blind observables enforce precisely this.

**2. Correlations remain classically representable.** Session semantics assume separable local state, classical message passing, and erasure/locality. Even after delegation, the strongest invariant representable is a classical joint distribution evolving under a Markov kernel, a defining feature of classical probabilistic descriptions in this setting. Irreducibly quantum correlations (entanglement) violate these assumptions: erasure fails and delegation does not preserve quantum resources without extra semantics. The boundary aligns with "admits a classical probabilistic description in an erasure-safe MPST model."

**3. Dynamics live on classical state spaces.** Everything admissible evolves on finite sets, simplices, manifolds, or spaces of measures, with Lipschitz drift, conservation laws, Lyapunov functions, and Markov kernels. This is the textbook scope of classical ODEs, SDEs, kinetic theory, mean-field limits, diffusion, and classical thermodynamics, not unitary evolution on Hilbert space, operator algebras, or noncommutative probability.

**4. Ergodicity becomes meaningful and conditionally provable.** The question "do time averages equal ensemble averages?" is itself a marker of classical statistical mechanics. In quantum theory, ergodicity is subtle, representation-dependent, and often false. In classical stochastic systems, it is a standard structural question, and here it is provable for theorem-transport profiles where Lyapunov/mixing side conditions are discharged.

**5. Critical phenomena and chaos are outside the current transported theorem envelope.** KAM theory (requires near-integrability), chaotic mixing (needs hyperbolicity), critical phenomena (infinite correlation length), and turbulence (loss of regularity) do not lift automatically under the stated model/assumption bundle. But this is where classical mechanics itself stops being uniform. The boundary aligns with the real classical boundary.

### Theorem Transport: When Classical Results Apply [Program+Consequence]

Because session-typeable systems satisfy classical structural properties, results from classical dynamics become applicable not by analogy but because the systems satisfy the theorems' hypotheses.

A classical dynamics theorem typically has the form: *If a system satisfies X (structure) and Y (regularity), then Z (behavior) follows.* Session types + Coherence provide structural guarantees (X). You check the remaining hypotheses (Y), often smoothness, convexity, or noise conditions, and the conclusion (Z) applies.

**Structural properties that typing provides:**
- Locality (per-edge Coherence, no action at distance)
- Well-posedness (preservation, dynamics are defined everywhere)
- Classical state space (finite configurations, no superposition)
- Markovian dynamics (step relation is memoryless)
- Exchangeability (delegation, roles interchangeable)
- Time-stationarity (step probabilities don't depend on absolute time)
- Microscopic reversibility (detailed balance at equilibrium)
- Finite degrees of freedom (bounded role count, finite type depth)

### Applicability Contract (Required for Transport)

| Layer | What is provided | What must still be checked | Typical status tag |
|-------|------------------|----------------------------|--------------------|
| **Typing/Coherence [Formal]** | Locality, well-posedness, active-edge compatibility, classical state representation | N/A | Mechanized |
| **Dynamics [Formal]** | Step relation, preservation, progress framework, fairness model | Match theorem's dynamical assumptions (e.g., reversibility, stationarity) | Mechanized + assumptions |
| **Analysis [Program/Formal]** | Candidate imported theorem (Foster-Lyapunov/Harris, mixing-time, MaxWeight, Little's Law, fluid/diffusion limits, LDP, concentration, mean-field, functional CLT) | Theorem-specific regularity/analytic side conditions (drift/minorization, spectral gap, policy assumptions, moment bounds, diffusion scaling, tails) | Assumption discharge |
| **Conclusion [Consequence]** | Engineering interpretation once assumptions discharge | State regime sensitivity (A/R/D) and scope limits | Model-level consequence |

### Concrete Examples of Theorem Transport

Main text keeps one fully discharged exemplar and defers the complete transport catalog to appendix form.

**Exemplar (fully discharged): Large deviations for SLA tails.**  
Given Markov dynamics on a finite state space and a non-degenerate rate function, large-deviation bounds yield:
`P[CompletionTime > W₀ + ε] ≤ exp(-n·I(ε))`.
In this framework, the structural hypotheses come from typing + Coherence + delegation (classical state representation, well-posed dynamics, exchangeability regime when required), and the remaining analytic side conditions are discharged in the transport appendix.

**Appendix reference [Program].** Full transported-theorem matrix and additional fully discharged exemplars are collected in **Appendix D** below.

### Beyond Thermal Equilibrium: Scheduling and Failure Regimes

This section is intentionally concise in the main draft.

**[Consequence] Regime summary:**
- Structural results (Coherence preservation, productive-step liveness, decidability, phase-transition thresholds) are regime-robust.
- Equilibrium-derived results are baseline predictors and require explicit scheduling/failure assumptions.
- Designed/mitigated systems typically outperform equilibrium baselines; adversarial regimes can underperform them.

**Compact matrix (main-text version):**

| Result family | Scheduler sensitivity | Failure sensitivity |
|---------------|-----------------------|---------------------|
| Structural guarantees | Low | Low |
| Equilibrium predictions | Medium/High | Medium/High |
| Large-n / statistical limits | High | High |

**Appendix reference [Program].** Full regime matrices, heavy-tail discussion, and deployment playbooks are preserved in **Appendix A** below.

### Where Classical Erasure Stops

The classical boundary is precisely where erasure stops being safe. Any additional erasure would have to erase one of:

| Failed erasure            | Why it fails                                         |
|---------------------------|------------------------------------------------------|
| **Phase erasure**         | Relative phase is observable (quantum interference)  |
| **Entanglement erasure**  | Local marginals do not determine the global quantum state |
| **Measurement erasure**   | Observer affects state (quantum back-action)         |
| **Topological erasure**   | Global topological degrees can be stateful/observable |

These are non-classical moves. In this framework, under the stated model/assumption bundle, the safe erasures are exactly the twelve canonical classical erasures (via Coherence-preserving generation exactness). Systems requiring quantum correlations, non-local measurements, or topological protection are not captured without extending the semantics.

This is not a limitation to apologize for but a *characterization*. Within the model scope, session types characterize systems where this classical reasoning toolkit applies.

### The VM as Classical Dynamics

The VM instruction set is not designed ad hoc — its minimal-complete claim is now exposed in theorem form (completeness/minimality interfaces plus missing-class witness hooks), concretized by a canonical-basis exactness theorem, and tightened to an iff-style VM↔erasure generation statement (`safe erasure ↔ generated by canonical VM/ConfigEquiv morphisms`) plus coverage/irredundancy against the 12-erasure interface for classical dynamics on Coherent configurations. Eight instructions arise from three determining structures:

1. **Local type grammar** — 4 action constructors (`send`, `recv`, `select`, `branch`) require 4 communication primitives
2. **Consume function** — buffer operations must match type recursion (append/dequeue aligned with Consume)
3. **Active edge quantification** — topology must be managed (`open`, `close`, `transfer`, `acquire`)

Together with ConfigEquiv, the projection function, and the effect handler abstraction, the VM is proven (under the stated model/assumption bundle) to realize exactly the twelve canonical classical erasures:

| Encoding | Erasures | Mechanism |
|----------|----------|-----------|
| Resource morphisms (send/recv) | #3 | Nullifiers |
| Control morphisms (select/branch) | #5 | Type narrowing |
| Topology morphisms (open/close) | #5 | Domain restriction |
| Delegation morphisms (transfer/acquire) | #2 | Ownership transfer |
| Quotient structure | #1, #7, #10 | ConfigEquiv + content addressing |
| Observer structure | #11 | Projection function |
| Effect abstraction | #9 | Handler independence |
| Semantic properties | #4, #6, #8, #12 | Proved invariants |

This is the computational manifestation of Paper 3's thesis. The VM isn't "an interpreter that happens to be correct" — it is a canonical dynamics on S/G under the stated constraints, with basis exactness obligations stated as theorem-form interfaces, concrete canonical-basis instantiation, iff-style VM↔erasure generation exactness, and witness obligations. The instruction set is derived from the requirement that every operation be a Coherence-preserving morphism on the quotient.

The value/choice split in communication primitives reflects different erasure mechanisms: send/recv operate on resources with linearity (nullifier-based erasure), while select/branch operate on labels with type narrowing (projection-based erasure). This isn't just "send with different payload" — the erasure semantics differ fundamentally, justifying the 4-way split of communication into two dual pairs.

### Harmony ⇒ Safe Delegation (Key Corollary)

The key operational corollary is: **if a configuration is Coherent, then any *well‑formed* delegation operation preserves Coherence.** In this framing, safe delegation is derived from the stronger semantic claim that Harmony survives topology change (`link` + delegation). It says Coherence is *sufficient* for safe delegation given the standard side conditions for delegation (e.g., the delegatee is not already in the session, or is mergeable via `Consume_mono`). No additional global invariants are required. If Coherence holds, endpoints can move.

**Dynamic participant sets.** This means role sets are not fixed at protocol definition time:
- A delegatee who wasn't in the session can join mid-protocol by receiving a delegated endpoint
- Combined with crash-stop, participants can also leave (edges become inactive)
- `link` can compose previously disjoint sessions, introducing new communication paths

The model supports genuinely dynamic topologies, not just static role assignments.

Why this works: Coherence is per-edge and role-agnostic. `EdgeCoherent G D e` checks whether the receiver can handle the buffer contents. It doesn't care *who* the receiver is, only that the receiver's type matches. When delegation transfers an endpoint from A to B, the edge structure changes but each new edge inherits a well-typed configuration from the old edges. The per-edge locality that makes Coherence compositional also makes it delegation-invariant.

```
First-order:  Consume processes values, advances one local type
Higher-order: Consume processes capabilities, advances one local type AND restructures the session graph
```

**Mechanization.** Key lemmas proved: `delegate_redirected_edge_coherent`, `Consume_rename_sender_implication`, `delegateGEnv_*`, `delegateDEnv_*`. The main theorem `delegate_preserves_coherent` is proved **non‑vacuously** under the refined Coherence definition that quantifies only over **active** edges (both endpoints exist). The Aristotle artifact `work/aristotle/14_delegation_coherence_nonvacuous.lean` captures why the older receiver‑only quantification is vacuous for infinite role universes, motivating the ActiveEdge refinement.

### Two Mechanisms, One Invariant

**Static composition.** Real systems run multiple protocols that share participants. Composing two protocols via `link` (connecting matching endpoints across protocol boundaries) must preserve Coherence and Harmony. The proof requires showing that `mergeBufs` preserves typing, that linked monitors remain well-typed, and that compositional deadlock freedom follows from per-protocol deadlock freedom. The key insight: Coherence's per-edge structure makes composition tractable because edges from different protocols are independent.

**Dynamic delegation.** Delegation has been in the MPST theory since Honda, Yoshida, and Carbone (2008), but many mechanizations defer or drop it because it breaks structural invariants. The reason is precise: first-order invariants cannot handle messages that carry session capabilities. When the buffer on session t contains an endpoint for session s, consuming that message restructures the session graph. `Consume` must become higher-order, but this extension stays within the classical boundary because the transferred capability is a classical name, not a quantum state.

### Supporting Theorems (Mechanization Decomposition)

The core theorem program is proved through the following supporting theorems:

**1. Compositional Harmony.** Composing two protocols via `link` preserves the Harmony property: projecting the composed global type then stepping locally equals stepping globally then projecting.

**2. Higher-order Coherence preservation.** After delegation of session s from A to B (including composed settings), higher-order Coherence is preserved; the edge analysis includes created edges induced by delegation.

**3. Conservative extension.** If no `ValType.chan` values are used and no `link` is applied, higher-order Coherence collapses to first-order Coherence, preserving all Paper 1 results.

**4. Choreographic delegation Harmony.** The `delegate` constructor in `GlobalType` and its projection rules extend Harmony from static topology to dynamic topology changes.

**5. Liveness lift.** The weighted measure W = 2·Σdepth + Σbuffer is preserved under pure reconfiguration (composition and delegation), enabling quantitative lift from Paper 2 into the delegation setting; transition choreography is handled via descent/budget bounds.

**6. Delegation in composed systems.** General delegation to already-present participants is handled via `Consume_mono` merge conditions, unifying evolution and delegation through one proof device.

### Cross-Layer Nature

The topology-change extensions touch every layer of the formalization:

- **SessionTypes.** `ValType.chan` becomes load-bearing, the type-level hook for capability-carrying messages.
- **Choreography.** New `delegate` constructor with projection rules. Harmony extended for both `delegate` and `link`.
- **Protocol/Coherence.** Higher-order `Consume` and `EdgeCoherent`. The flagship definitions and preservation theorem.
- **Protocol/Deployment.** Compositional Harmony through `Interface`, `Merge`, and `Linking`. The 8 linking axioms become proved theorems. They find their theoretical home as the static-composition counterpart to dynamic delegation.
- **Protocol/Typing.** Linear capability transfer in `HasTypeProcN`. `LinCtx` with `produceToken`/`consumeToken`.
- **Runtime/Iris.** Delegation corresponds to `ghost_map_update` on the session ownership map. **This gives the Iris separation logic layer its theoretical raison d'etre.** Without delegation, endpoints have fixed owners and the full power of Iris-style ownership transfer is unnecessary. With delegation, the ~108 shim axioms become the formal framework for linear capability transfer.
- **Runtime/VM.** `stepTransfer` and `ExecOwnership.lean` implement VM-level delegation.

### Structure

```
1. First-order Coherence recap
2. Higher-order Coherence definitions (GraphDelta, HO Consume, HO EdgeCoherent)
3. Conservative extension (HO collapses to FO when no ValType.chan)
4. Static topology change: Compositional Harmony through link
5. Dynamic topology change: Delegation Coherence preservation (four-way edge analysis)
6. Unification: Delegation in composed systems (general case)
7. Cross-layer connections (Iris ownership transfer, Lyapunov preservation/lift)
```

The unification in section 6 is where the two results become more than the sum of their parts. Delegation to an existing participant in a composed system is the operation that requires the full machinery. Compositional Harmony provides the well-typed composed context, higher-order Consume handles the capability transfer, and `Consume_mono` mediates the type merge at the delegatee.

### Narrative [Interpretation]

"Harmony survives reconfiguration; safe delegation follows." This is the Paper 3 completion of the arc:

- **Paper 1** defined Coherence as safe coarse-graining, the invariant that makes projection well-defined.
- **Paper 2** derived the second law, proving that systems satisfying Coherence obey classical thermodynamics.
- **Paper 3** proves Harmony under topology change, yielding safe delegation as a corollary and making role identity erasable.

Once identity is erasable, you obtain the intended classical-statistical-mechanics-style structure: exchangeability, classically representable correlations, and classical state spaces. The three papers trace the model boundary where this style of reasoning applies. Within this boundary, theorem transport applies: typing proves structural hypotheses; analysis discharges remaining side conditions.

---

## Synthesis: One Semantic Core [Consequence+Interpretation]

The three papers converge on a single insight: **within this formal model, session-typeable systems are the systems where erasure is semantically safe**.

This yields one notion of each fundamental concept:

| Concept         | Unified meaning                                                              |
|-----------------|------------------------------------------------------------------------------|
| **Correctness** | Transition preserves Coherence on the quotient S/G                           |
| **Identity**    | None: roles, carriers, resources are presentations, not objects              |
| **Time step**   | Any Coherence-preserving transformation (protocol, delegation, nullification) |
| **Equivalence** | ConfigEquiv: differ only by Coherence-preserving symmetries                  |

The litmus test: if removing something doesn't change any conserved quantity or observable prediction, it's already quotiented out. If removing it does change predictions, it's not erasable and therefore not classical.

This is a deliberate structural alignment. The twelve erasures in `work/erasure.md` are used as the organizing symmetry set for this framework: session types enforce them, Coherence proves their safety conditions, and delegation completes the intended symmetry picture.

**Stop thinking of erasure as a feature. It is the semantics.**

---

## Paper Comparison

| Paper | Core thesis | Role in arc | Novel techniques | Target venue |
|---|---|---|---|---|
| 1. Coherence for Asynchronous Buffered MPST | Safety + evolution via safe coarse-graining | Enforce classical structure | Coherence invariant, Consume, three-way analysis, model-parametric delivery, effects bridge, `Consume_mono` | POPL / ICFP |
| 2. Computable Dynamics for Asynchronous MPST | Quantitative liveness + unified decidability | Make classical structure computable | Lyapunov descent theorem, finite-reachability schema, phase thresholds, compositional bounds | POPL |
| 3. Harmony from Coherence in Asynchronous MPST | Characterize erasure-safe reconfiguration boundary | Complete classical characterization | Erasure realizability, reconfiguration Harmony, delegation corollary, relative minimality, composed-system conservation, theorem transport | POPL |

## Comprehensive Theorem Inventory (Main + Appendices)

This section is the authoritative theorem list for the trilogy and is synchronized with `work/paper/outline1.md`, `work/paper/outline2.md`, and `work/paper/outline3.md`.

### Paper 1: Coherence for Asynchronous Buffered MPST

**Main body theorem slots**
1. Coherence Preservation Theorem.
2. Session Evolution Theorem via `Consume_mono`.

**Appendix theorem/lemma sets**
1. Updated-edge preservation lemmas (`send`/`recv`/`select`/`branch`).
2. Shared-endpoint irrelevance lemmas.
3. Unrelated-edge transport lemmas.
4. `Consume` library core: `Consume_append`, `Consume_cons`.
5. Session-evolution core: `RecvSubtype_refl`, `consumeOne_mono`, `Consume_mono`, `Coherent_type_replacement`, `Coherent_session_evolution`.
6. Delivery/effect bridge obligations: `DeliveryModel` law obligations + effect-to-VM bridge lemmas.

### Paper 2: Computable Dynamics for Asynchronous MPST

**Main body theorem/corollary slots**
1. Quantitative Dynamics Theorem (Lyapunov descent).
2. Algorithmic Dynamics Schema Theorem (finite reachability).
3. Crash-Tolerance Theorem (decidability + iff characterization + non-monotonicity).
4. Async Subtyping Decidability Corollary.
5. Type Equivalence Decidability Corollary.
6. Branching Feasibility Corollary.
7. Additive Composition Corollary.
8. Critical Capacity Corollary.

**Appendix theorem/lemma sets**
1. Quantitative appendix set: per-step descent lemmas, tight productive-step bounds, scheduler-lift theorems, total-step corollaries.
2. Algorithmic appendix set: reachable-state finiteness construction, exploration termination, decision-reduction correctness theorem.
3. Expanded instantiation details: crash tolerance details + branching feasibility details.

### Paper 3: Harmony from Coherence in Asynchronous MPST

**Main body theorem/corollary slots**
1. Theorem B: Reconfiguration Harmony.
2. Theorem A: Erasure Characterization of Coherence.
3. Theorem C: Safe Delegation Corollary (footprint exactness packaging).
4. Theorem D: Relative Minimality over `Admissible(I)`.
5. Theorem E: Composed-System Conservation.
6. Theorem F: Exact Determinism-Envelope Characterization.
7. Corollary F.1: Rational-Fragment Exactness (`finite erasure ↔ rational`).
8. Corollary F.2: Strict Boundary Witness.
9. Corollary F.3: `toCoind` Image Exactness.
10. Theorem G: Exchange-Normalized Determinism + Spatial Monotonicity.
11. Theorem H: Observational Adequacy + VM Adherence Modulo Envelope.
12. Secondary Corollary S1: Principal Capability + Admission Completeness.
13. Secondary Corollary S2: Compositional Exactness under Non-Interference + converse strictness boundary packaging.

**Appendix theorem/lemma sets**
1. Appendix Corollary F.4: Principal Finite Witness + Adequacy Replay.
2. Appendix Corollary F.5: Relative Maximality of the Rational Fragment.
3. Supporting theorem decomposition set: compositional Harmony; higher-order Coherence preservation under delegation; conservative extension (HO→FO collapse); choreographic delegation Harmony; liveness conservation under composition/delegation; delegation in composed systems; rational-fragment support pack.
4. Coinductive effect-bridge pack (implemented): `effectBisim_implies_observationalEquivalence`, `effectBisim_congr_seq`, `effectBisim_congr_par`, `effectBisim_congr_link`, `effectBisim_congr_handler_subst`, `configEquiv_iff_effectBisim_silent`, `protocolOutcome_effectBisim_of_observationalEq`, `compile_refines_observationalEq_of_effectBisim`, `vmView_effectBisim_of_VMCEquiv`, `vmCEquiv_of_vmView_effectBisim`, `topology_change_preserves_VMCEquiv_via_effectBisim`, `rationalEffect_transport_bridge`, `strict_boundary_witness_effect`.
5. Transport theorem catalog (10-result set): Foster-Lyapunov + Harris ergodicity, mixing-time bounds, MaxWeight/backpressure throughput optimality, Little's Law, fluid-limit stability, large deviations, concentration inequalities, heavy-traffic diffusion limits, propagation of chaos/mean-field limits, functional CLT/invariance principles.
6. Appendix closure theorem: transport profile minimal-basis (`provenNecessary` assumptions are jointly minimal via dropped-assumption failure witnesses).
7. Appendix closure theorem: canonical VM basis uniqueness up to erasure isomorphism.
8. Appendix closure theorem: quotient universality (`factor through observationalErasure ↔ ConfigEquiv-invariant observable`).
9. Appendix closure theorem: witness-based productive-step bound tightness (saturating trace implies exact bound at that initial state).
10. Appendix closure theorem: conservative-extension converse (FO success on channel-free traces lifts to HO with empty delta and identical observable residual).

**Mechanization scale.** ~425 files, ~115,000 lines, 0 axioms, 0 sorry. The largest prior MPST mechanization (Scalas & Yoshida, JFP 2019) is ~5,000 lines—this is over an order of magnitude beyond.

**Effects integration.** The algebraic effect system is cross-cutting: Paper 1 introduces the architecture and `EffectModel.handlerType` bridge, Paper 2 connects termination bounds to effect execution, and Paper 3 frames delegation as linear capability transfer and composition as per-protocol effect isolation through the effect layer.

## Recommended Order

1 → 2 → 3. The quotient progression:

| Paper | Quotient operation                           | What becomes gauge              |
|-------|----------------------------------------------|---------------------------------|
| 1     | Define S/G (Coherence = invariant)           | Non-participating interactions  |
| 2     | Dynamics on S/G (Lyapunov = state function)  | Microscopic trajectory details  |
| 3     | Complete S/G (reconfiguration Harmony)       | Role and endpoint identity      |

Each paper enlarges the symmetry group G while proving the invariant survives. Paper 2's tools work *because* Paper 1 placed us on the quotient. Paper 3's characterization is meaningful *because* Papers 1 and 2 established the invariant and its dynamics.

**If you could only do one:** Paper 1. It defines the quotient, Coherence as the invariant that survives coarse-graining. Addresses the 20-year community goal (mechanized asynchronous buffered MPST) and is publishable with what mostly already exists.

**If you could do two:** Papers 1 + 2. Define + derive. The quotient + dynamics on it. Safety + the second law + decidability = a complete, algorithmically tractable metatheory for classical distributed systems.

## Target Application: Unified Distributed Systems Protocols

The typical distributed systems stack is fragmented across layers with informal interfaces:

| Layer | Typical approach | Problem |
|-------|------------------|---------|
| P2P networking | libp2p, custom gossip protocols | Untyped message passing, tested not verified |
| Consensus | Raft, Paxos, HotStuff implementations | Separate codebase, interface assumptions unverified |
| State machine | Application-specific logic | No connection to consensus/network correctness |

The interfaces between layers are where bugs live. Consensus implementations assume the network delivers messages correctly. State machines assume consensus provides the guarantees it claims. These assumptions are rarely checked formally.

**What the unified VM + session types approach offers:**

1. **Single formalism.** P2P peer handshakes, consensus rounds, and state machine transitions are all choreographies projected to local types, executed in one VM. No layer boundaries to get wrong.

2. **Cross-layer type checking.** The session type for a consensus round includes the state machine transitions it triggers. Type errors surface at compile time if the state machine expects something consensus doesn't provide.

3. **Crash tolerance is native.** The crash-stop decidability (Paper 2) directly applies: "Can this protocol complete if participants F crash?" is decidable via residual graph connectivity.

4. **Delegation = participant handoff.** A node delegating its role to a new node (validator rotation, load balancing, failover) is literally delegation in the session type sense, with Coherence preservation proved.

5. **Composition = protocol layering.** `link` for composing sessions models cross-protocol communication (e.g., consensus protocol composed with state replication protocol) with typed guarantees at the interface.

**The pitch for practitioners:**

> Instead of three codebases with informal interfaces, write one choreography that spans networking, consensus, and application logic. The session type is your specification. The VM is your execution. Coherence is your safety invariant. Crash tolerance is decidable. Delegation handles node rotation. Composition handles protocol layering.

This directly addresses the reliability gap in distributed systems infrastructure, where most bugs occur at layer boundaries rather than within layers.

### Adaptive Protocols with Typed Transitions

A further design space opens up: **environment-aware protocols that transition between coordination modes with formal guarantees through the transition**.

Traditional systems pick a consistency model (CRDT, consensus, etc.) and stick with it. Some systems offer per-operation tuning, but without formal transition semantics. With session types, the transition itself becomes a choreography:

| Phase | Coordination mode | Properties |
|-------|-------------------|------------|
| Normal operation | CRDT / eventual consistency | High availability, partition tolerance |
| **Transition** | Quiesce, synchronize, establish leader | **Typed protocol with crash tolerance decidability** |
| Strong consistency needed | Consensus (Raft, Paxos, etc.) | Linearizability, lower availability |

The session type describes all three phases as one protocol. The transition phase is not informal "implementation detail" but a first-class choreography with:
- Typed message sequences (quiesce → collect state → merge → start consensus)
- Crash tolerance: "can this transition complete if nodes F crash?" is decidable
- Coherence preserved across the mode change

This enables protocols that fluidly adapt to environmental conditions (network stability, load, consistency requirements) while maintaining sharp guarantees through every transition. The boundaries between modes become typed interfaces rather than informal assumptions.

### Zero-Downtime Typesafe Protocol Upgrades

Protocol version migration—typically the most dangerous operation in distributed systems—becomes a typed choreography:

| Phase | Description | Typed guarantee |
|-------|-------------|-----------------|
| 1. Coordination | New nodes running P₂ join via delegation | Coherence preserved |
| 2. Dual-write | Messages translated at version boundaries | Typed by async subtyping |
| 3. Cutover | Old nodes delegate to new and exit | DelegationWF ensures safety |
| 4. Cleanup | Legacy edges drain | Lyapunov-bounded completion |

Each phase is a choreography with crash tolerance decidability: "can this upgrade phase complete if nodes F crash?" is answerable at compile time. Typed guards gate phase transitions: "if all P₂ nodes reachable and W ≤ drain_budget, proceed to cutover."

The result is **live migration with machine-checked safety**—no flag days and no required downtime window. This addresses a major operational pain point where protocol upgrades are often the riskiest operations in production distributed systems.

### Typed Guards with Decidable Preconditions

The decision to transition can itself be a typed guard with compile-time guarantees:

| Guard condition | Decidability source | Guarantee if guard passes |
|-----------------|---------------------|---------------------------|
| Reachable nodes ≥ 2f+1 | Crash tolerance decidability | Consensus can complete |
| Pending updates < threshold | Buffer bounds Bc | Bounded synchronization cost |
| W(state) ≤ budget | Lyapunov measure | Bounded steps to quiescence |
| No conflicting transactions | Async subtyping | Safe type evolution |

The guard is evaluated at runtime, but its correctness is verified at compile time: **if the guard passes, the transition has the guaranteed properties**. This connects:

- **Paper 2's decidability results** → guards that check "can this operation complete?"
- **Paper 2's quantitative bounds** → guards that check "is this operation within budget?"
- **Paper 3's Harmony** → transitions preserve Coherence when guards are satisfied

The result is protocols that make environment-aware decisions with machine-checked guarantees about the consequences of those decisions.

---

## Practical Payoff

The physics framing translates to an engineering split between guarantees and predictions.

| Result class | What you get | Assumption sensitivity |
|--------------|--------------|------------------------|
| **Structural guarantees [Formal+Consequence]** | Safety/preservation, productive-step liveness bounds, decidability, compositionality | Low |
| **Equilibrium predictions [Consequence]** | Throughput/variance/load-balance style baselines | Medium to high |
| **Statistical limit laws [Program/Consequence]** | Large-n and rare-event behavior | High |

The meta-payoff: **typing provides structural guarantees; analysis layers add quantitative predictions**. Engineering quality determines how close production behavior is to equilibrium baselines.

**Appendix reference [Program].** Expanded payoff/regime tables are preserved in **Appendix B** below.

## Deferred Work

One direction is not included in any paper:

- **End-to-end compilation correctness.** Composing Harmony → compiler correctness → monitor soundness → VM adequacy into a single theorem. Blocked on Iris shims and compiler correctness proofs. Could form a future Paper 4 targeting the verified compilation pipeline, with the effect architecture from Paper 1 as the central device.

---

## Appendix A: Full Regime Analysis

This appendix contains the expanded version of the regime discussion from the main text.

### Scheduling and Failure Regimes

Real distributed systems often deviate from thermal equilibrium along two independent axes, skewing closer to the upper- or lower-bound:

**Scheduling hierarchy:**
```
Adversarial  ≤  Random (thermal)  ≤  Designed (optimized)
  (worst)         (baseline)            (typical)
```

- **Designed** (round-robin, priority queues, work-stealing): engineered for efficiency, *better* than random
- **Random** (thermal): the baseline equilibrium physics assumes; pessimistic for real systems
- **Adversarial** (attacker-controlled): worst case for security analysis

**Failure hierarchy:**
```
Adversarial  ≤  Random (IID)  ≤  Mitigated (fault-tolerant)
  (worst)        (baseline)         (engineered)
```

- **Mitigated** (redundancy, replicas, circuit breakers, graceful degradation): engineered resilience, *better* than random failures
- **Random** (IID, Poisson, exponential): the baseline equilibrium physics assumes
- **Adversarial** (Byzantine, targeted, correlated, cascading): worst case for security analysis

**The 3×3 regime matrix:**

| | Adversarial failures | Random failures | Mitigated failures |
|---|:---:|:---:|:---:|
| **Designed scheduling** | Sched helps, failures hurt | Better than equilibrium | Best case (production) |
| **Random scheduling** | Equilibrium sched, worst failures | Equilibrium baseline | Better than equilibrium |
| **Adversarial scheduling** | Fully adversarial | Worst sched, random failures | Sched hurts, failures helped |

**Structural results (hold in all 9 regimes):**

| Result | Why it survives | Interpretation |
|--------|-----------------|----------------|
| **Lyapunov bound W₀** | W decreases under productive steps | Termination in ≤W₀ productive steps (total-step bounds require scheduler assumptions) |
| **Phase transition B_c** | Structural property of types | Critical threshold separating bounded-buffer progress regimes from deadlock-permitting regimes |
| **Decidability** | Existence results | Cannot be affected by scheduling or failures |
| **Little's Law (stable regime)** | Flow conservation + stationarity identity | Average queue length predicted from throughput and delay |
| **Crash tolerance predicate** | `CrashTolerant G F` decidable for any F | Can check against any crash set |

**Scheduling-sensitive results:**

| Result | Designed (typical) | Random (baseline) | Adversarial (worst) |
|--------|:------------------:|:-----------------:|:-------------------:|
| **MaxWeight/backpressure throughput optimality** | Policy actively stabilizes admissible load region | Baseline under stochastic arrivals | Adversary can force overload patterns |
| **Mixing-time bounds** | Faster practical mixing under engineered schedulers | Baseline burn-in horizon | Mixing can be delayed/arbitrarily slow |
| **Foster-Lyapunov + Harris ergodicity** | Drift/minorization often easier to satisfy | Baseline geometric ergodicity regime | Ergodicity may fail without randomness/fairness |
| **Heavy-traffic diffusion limits** | Better constants due to smoother dispatch | Baseline reflected-diffusion approximation | Approximation quality degrades under adversarial bursts |
| **Functional CLT / invariance principles** | Cleaner Gaussian limit behavior | Baseline weak-convergence regime | Non-mixing/adversarial bursts can break scaling assumptions |

Key insight: **equilibrium scheduling results are pessimistic baselines**. Designed schedulers beat them; adversarial schedulers are worse.

**Failure-sensitive results:**

| Result | Mitigated (engineered) | Random (baseline) | Adversarial (worst) |
|--------|:----------------------:|:-----------------:|:-------------------:|
| **Large deviations** | Tighter bounds (redundancy helps) | Baseline rate function I(ε) | Rate function degenerate |
| **Propagation of chaos / mean-field limits** | Cleaner limits (replicas stabilize) | Baseline large-n limit | Targeted failures break exchangeability |
| **Fluid-limit stability** | Better drain/repair dynamics preserve stability | Baseline fluid-stability assumptions | Cascades can invalidate fluid assumptions |
| **Heavy-traffic diffusion limits** | Better diffusion constants under mitigation | Baseline heavy-traffic scaling | Correlated failures distort diffusion scaling |

Key insight: **equilibrium failure results are baseline assumptions**. Mitigated systems beat them; adversarial failures are worse.

**The symmetric picture:**

| Dimension | Adversarial | Random (equilibrium) | Designed/Mitigated |
|-----------|:-----------:|:--------------------:|:------------------:|
| **Scheduling** | Worst case | Pessimistic baseline | Typical (better) |
| **Failures** | Worst case | Baseline assumption | Engineered (better) |

Both dimensions have the same structure: equilibrium is the middle ground. Engineering improves on it; adversaries degrade it.

**Practical regime selection:**

| Use case | Scheduling | Failures | What applies | Interpretation |
|----------|:----------:|:--------:|--------------|----------------|
| **Production (optimistic)** | Designed | Mitigated | All results | Best-case analysis |
| **Production (realistic)** | Designed | Random | Equilibrium conservative for sched | Typical operation |
| **Capacity planning** | Random | Random | Full equilibrium theory | Baseline predictions |
| **SLA guarantees** | Adversarial | Random | Structural + failure statistics | Worst-case latency |
| **Reliability analysis** | Designed | Adversarial | Structural + sched equilibrium | Targeted attack resilience |
| **Security analysis** | Adversarial | Adversarial | Structural only | Byzantine tolerance |
| **Chaos engineering** | Random | Adversarial | Equilibrium sched + worst failures | Fault injection testing |

### Heavy tails and non-normal distributions

Adversarial conditions (either dimension) produce skewed, heavy-tailed distributions:

| Distribution issue | Cause | Mitigation |
|-------------------|-------|------------|
| **Heavy-tailed latency** | Adversarial scheduling concentrates delays | Use worst-case Lyapunov bound W₀ |
| **Correlated failures** | Cascading failures, common-mode faults | Check crash tolerance against correlated crash sets |
| **Bursty arrivals** | Non-Poisson message patterns | Phase transition B_c still applies (structural) |
| **Bimodal completion** | Adversary creates fast/slow split | Lyapunov bound covers slow case |

**The framework's response:**

- **Guarantees** (structural results): worst-case bounds that hold unconditionally
- **Predictions** (equilibrium results): accurate under benign conditions, become lower bounds under adversarial conditions
- **Benchmarks** (equilibrium optima): what's achievable; adversary can only do worse

For adversarial analysis, the equilibrium results tell you what performance is *possible*; structural results tell you what performance is *guaranteed*. The gap between them is the adversary's power.

---

## Appendix B: Expanded Practical Payoff Tables

This table focuses on **transported** results only, ordered by practical/theorem strength (strongest first). It is intentionally the ten-result transport set; the two spine results already in the main papers are: (Paper 1) Coherence/erasure characterization and (Paper 2) Lyapunov descent + capacity/decision framework. The **Sched** and **Fail** columns indicate minimum regime required: **A** = works under Adversarial, **R** = requires Random baseline, **D** = requires Designed/Mitigated.

| Classical result                                 | Sched | Fail | Engineering guarantee                                                                                     |
|--------------------------------------------------|:-----:|:----:|-----------------------------------------------------------------------------------------------------------|
| **Foster-Lyapunov + Harris ergodicity**          |   R   |  R   | Unique invariant regime and geometric convergence for long-run metrics.                                  |
| **Mixing-time bounds**                           |   R   |  R   | Explicit burn-in horizons before steady-state estimation/control actions.                                |
| **MaxWeight/backpressure throughput optimality** |   D   |  R   | Stabilizes all arrival rates in the capacity region under deployed backpressure policy.                  |
| **Little's Law (stable regime)**                 |   A   |  A   | Converts throughput targets directly into queue-length/latency budgets.                                  |
| **Fluid-limit stability theorems**               |   A   |  A   | ODE-scale stability implies queue stability and drain guarantees at scale.                               |
| **Large deviation principle**                    |   A   |  R   | Exponential tail bounds for rare deadline/SLA violations.                                                |
| **Concentration inequalities**                   |   A   |  R   | High-probability finite-sample bounds on aggregate latency/load.                                         |
| **Heavy-traffic diffusion limits**               |   R   |  R   | Near-capacity reflected-diffusion approximations for staffing and buffer sizing.                         |
| **Propagation of chaos / mean-field limits**     |   R   |  R   | Large-n decoupling to deterministic mean-field control laws.                                             |
| **Functional CLT / invariance principles**       |   R   |  R   | Path-level Gaussian approximations for burst/excursion behavior.                                         |

**The 3×3 interpretation:**

| | Adversarial fail | Random fail | Mitigated fail |
|---|:---:|:---:|:---:|
| **Designed sched** | Structural + sched equilibrium | Better than equilibrium | Best case |
| **Random sched** | Structural + failure stats | Full equilibrium (baseline) | Better than equilibrium |
| **Adversarial sched** | Structural only | Structural + failure stats | Structural + failure stats |

**Regime selection guide:**

| Use case | Sched | Fail | Available tools |
|----------|:-----:|:----:|-----------------|
| **Production (optimistic)** | D | D | All results; predictions are conservative |
| **Production (realistic)** | D | R | Equilibrium conservative for scheduling |
| **Capacity planning** | R | R | Full equilibrium baseline |
| **SLA guarantees** | A | R | Structural + LDP/concentration |
| **Reliability engineering** | D | A | Structural + scheduling equilibrium |
| **Security analysis** | A | A | Structural only |
| **Chaos engineering** | R | A | Equilibrium sched + worst-case failures |

The meta-payoff: **typing provides the structural foundation for classical reasoning**. Structural results (A/A) are unconditional guarantees. Equilibrium results (R/R) are baselines: designed/mitigated systems beat them, adversarial systems can be worse. The gap between structural and equilibrium bounds is the space where engineering matters.

---

## Appendix C: Paper 2 Expanded Instantiations and Inventory

This appendix contains additional Paper 2 material.

### Expanded Decision Instantiations

**Crash tolerance (now elevated to main body as Theorem 3).**
- Predicate: `CrashTolerant G F`
- Method: residual-graph reachability / finite search over `CanComplete`
- Exact iff-characterization via residual graph connectivity
- Key phenomenon: tolerance is non-monotone in crash set F (proved constructively)
- This is now a core theorem, not demoted material

**Branching feasibility (single-shot combinatorial criterion).**
- Criterion: feasibility iff confusability-graph independence number ≥ label count
- Interpretation: replaces entropy-capacity intuition in the one-shot setting with exact combinatorics

### Expanded Mechanization Inventory (Paper 2 Scope)

- `Lyapunov.lean` (381 lines)
- File 09 (305 lines, measure additivity)
- File 09b (352 lines, weighted measure)
- File 10b (709 lines, bounded-buffer step semantics with concrete example)
- File 05 (306 lines, asynchronous subtyping)
- File 05b (244 lines, finiteness and decidability)
- File 07 (630 lines, Shannon-style bound development)
- File 07b (402 lines, confusability-graph iff theorem)
- File 03 (174 lines, residual coherence)
- File 04 (321 lines, crash predicate)
- File 04b (402 lines, crash decidability)
- `DeadlockFreedom.lean` (632 lines)
- Cross-session diamond (1,180 lines)
- Bisimulation development (1,184 lines)

---

## Appendix D: Full Theorem-Transport Catalog (Paper 3)

This appendix contains the expanded transported-theorem catalog referenced from Paper 3 main text.
It is the transport-only ten-theorem set, in addition to the two core main-paper results (Paper 1 Coherence/erasure characterization and Paper 2 Lyapunov/capacity/decision framework).

### Transport Matrix (Expanded)

The **Sched** and **Fail** columns indicate minimum regime required: **A** = Adversarial (strongest), **R** = Random baseline, **D** = Designed/Mitigated.
Transport assumption profiles are tagged with necessity status (`proven-necessary` vs `sufficient-only`) to make one-way vs exact-side-condition claims explicit.

| Classical result                                 | Sched | Fail | Hypothesis typing provides                                   | What you still check                                           | Conclusion for protocols                                              |
|--------------------------------------------------|:-----:|:----:|--------------------------------------------------------------|----------------------------------------------------------------|-----------------------------------------------------------------------|
| **Foster-Lyapunov + Harris ergodicity**          |   R   |  R   | Markov dynamics, finite-state abstraction, irreducibility scaffolding | Drift + minorization (petite set) conditions                     | Unique invariant law and geometric convergence                        |
| **Mixing-time bounds**                           |   R   |  R   | Ergodic finite-state transition system                       | Spectral gap or coupling bound                                  | Explicit burn-in bounds and convergence-rate certificates             |
| **MaxWeight/backpressure throughput optimality** |   D   |  R   | Queue network with typed conservation constraints            | Arrival rates interior to capacity region; policy assumptions    | Stability for all admissible loads under deployed scheduler           |
| **Little's Law (stable regime)**                 |   A   |  A   | Flow conservation and well-defined arrivals/completions      | Steady-state existence; finite first moments                    | `L = λW` queue-length/latency/throughput identities                   |
| **Fluid-limit stability theorems**               |   A   |  A   | Scaled state process and Lipschitz drift templates           | Global stability of fluid ODE; tightness back to stochastic model | Positive recurrence and drain guarantees at network scale             |
| **Large deviation principle**                    |   A   |  R   | Markov dynamics, finite state space                          | Non-degenerate rate function; exponential tightness             | Exponential tail bounds for completion/SLA violations                 |
| **Concentration inequalities**                   |   A   |  R   | Bounded-increment or weak-dependence structure               | Bounded differences / sub-Gaussian mgf bounds                   | High-probability finite-sample aggregate guarantees                   |
| **Heavy-traffic diffusion limits**               |   R   |  R   | Critical-load scaling and centered increment decomposition    | Functional tightness; reflection-map regularity                 | Reflected-diffusion approximations near capacity                      |
| **Propagation of chaos / mean-field limits**     |   R   |  R   | Exchangeability from delegation and mean-field interaction form | Lipschitz interaction kernel; uniform moment bounds             | As n→∞, empirical distribution converges to deterministic mean-field  |
| **Functional CLT / invariance principles**       |   R   |  R   | Martingale decomposition for cumulative process observables   | Lindeberg condition; quadratic-variation convergence            | Path-level Gaussian weak limits for burst/excursion statistics        |

### Fully Discharged Exemplars (Expanded)

**1. Foster-Lyapunov + Harris ergodicity (steady-state legitimacy).**  
Drift/minorization side conditions establish a unique invariant law and geometric convergence to it.

**2. Mixing-time bounds (burn-in certification).**  
Spectral-gap/coupling arguments give explicit time-to-near-stationarity guarantees.

**3. MaxWeight/backpressure throughput optimality (capacity-region operation).**  
Given policy and arrival assumptions, throughput-optimal scheduling stabilizes all admissible loads.

**4. Little's Law (operational conversion law).**  
Steady-state first-moment assumptions convert throughput objectives directly into delay and queue-size budgets.

**5. Fluid-limit stability (scale-up guarantee).**  
Stable fluid ODE limits lift to stochastic-network stability and drain guarantees.

**6. Large deviations (SLA guarantees).**  
Tail-latency probabilities decay exponentially with explicit rate function I(ε), yielding probabilistic SLA guarantees.

**7. Concentration bounds (aggregate behavior).**  
Bounded-difference/sub-Gaussian side conditions yield high-probability completion and performance bounds.

**8. Heavy-traffic diffusion limits (near-capacity planning).**  
Critical-load scaling yields reflected-diffusion approximations for staffing and buffer sizing.

**9. Propagation of chaos / mean-field limits (large-n simplification).**  
Exchangeability + Lipschitz interactions yield deterministic mean-field limits as participant count grows.

**10. Functional CLT / invariance principles (path-level uncertainty).**  
Weak-convergence conditions yield Gaussian process approximations for excursions and burst envelopes.

### Limitation Statement

Transport conclusions apply only when theorem-specific analytic side conditions (drift/minorization, spectral gap/coupling, policy assumptions, moment bounds, diffusion scaling, Lipschitz kernels, and Lindeberg-style conditions) are discharged. Typing and Coherence provide structural hypotheses; analysis discharges the remaining hypotheses.
