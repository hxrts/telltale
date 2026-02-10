# Lean Verification Code Map

**Last Updated:** 2026-02-10

Comprehensive map of the Telltale Lean 4 verification library — formal verification of choreographic programming with multiparty session types.

## Table of Contents

1. [Overview](#overview)
2. [SessionTypes](#sessiontypes)
3. [SessionCoTypes](#sessioncotypes)
4. [Choreography](#choreography)
5. [Semantics](#semantics)
6. [Classical](#classical)
7. [Distributed](#distributed)
8. [Protocol](#protocol)
9. [Runtime](#runtime)
10. [Build Configuration](#build-configuration)
11. [Axiom Inventory](#axiom-inventory)
12. [Proof Strategies](#proof-strategies)
13. [Quick Navigation Guide](#quick-navigation-guide)

---

## Overview

**Toolchain:** Lean 4 v4.26.0
**Build:** Lake with 8 library targets
**Dependencies:** mathlib, paco-lean v0.1.3, iris-lean

| Library        | Files | Lines   | Focus                                                      |
|----------------|------:|--------:|------------------------------------------------------------|
| SessionTypes   |    31 |  ~8,572 | Global/local type definitions, de Bruijn, participation    |
| SessionCoTypes |    67 | ~14,963 | Coinductive EQ2, bisimulation, duality, async subtyping    |
| Choreography   |    70 | ~17,552 | Projection, harmony, blindness, embedding, erasure         |
| Semantics      |     8 |  ~2,171 | Operational semantics, determinism, deadlock freedom       |
| Classical      |    15 |  ~2,019 | Transported theorems (queueing, large deviations, mixing)  |
| Distributed    |    19 |  ~3,509 | Distributed assumptions, validation, FLP/CAP theorem packaging|
| Protocol       |    78 | ~37,474 | Async buffered MPST, coherence, preservation, monitoring   |
| Runtime        |    87 | ~19,179 | VM, Iris backend via iris-lean, resource algebras, WP      |
| **Total**      | **375** | **~105,439** |                                                      |

**Architectural Layers:**
```
Layer 8: Runtime          → VM, iris-lean backend, resource algebras, WP, adequacy
Layer 7: Protocol         → Async MPST, coherence, typing, preservation, monitoring, deployment
Layer 6: Distributed      → Distributed assumptions, validation, FLP/CAP theorem packaging
Layer 5: Classical        → Transported theorems from queueing/probability theory
Layer 4: Semantics        → Operational semantics, typing judgments, determinism, deadlock freedom
Layer 3: Choreography     → Projection, harmony, blindness, embedding, erasure
Layer 2: SessionCoTypes   → Coinductive EQ2, bisimulation, duality, roundtrip bridge, async subtyping
Layer 1: SessionTypes     → Global/local types, de Bruijn, participation
```

---

## SessionTypes

**Root Module:** `SessionTypes.lean`
**Description:** Inductive session type definitions with de Bruijn indices and recursive binders.

### Global Types

| File | Lines | Description |
|------|-------|-------------|
| GlobalType/Core.lean | 329 | Global type definitions and operations |
| GlobalType/Semantics.lean | 357 | Global type substitution |
| GlobalType/WellFormedLemmas.lean | 346 | Global stepping semantics |
| GlobalType/ProductivityLemmas.lean | 294 | Well-formedness and properties |
| GlobalType/Closedness.lean | 577 | Observable behavior and duality |

### Local Types (Recursive)

| File | Lines | Description |
|------|-------|-------------|
| LocalTypeR/Core.lean | 513 | Recursive local type definitions |
| LocalTypeR/Environments.lean | 354 | Well-formedness and operations |
| LocalTypeR/Unfolding.lean | 249 | Observable predicates |
| LocalTypeR/Substitution.lean | 398 | Substitution and operations |
| LocalTypeR/WellFormedness.lean | 274 | Duality and properties |

### Local Types (De Bruijn)

| File | Lines | Description |
|------|-------|-------------|
| LocalTypeDB/Core.lean | 258 | De Bruijn representation with clean substitution |
| LocalTypeDB/Preservation.lean | 556 | De Bruijn type preservation and correctness |
| LocalTypeDBExamples.lean | 157 | Examples demonstrating de Bruijn usage |

### Conversions

| File | Lines | Description |
|------|-------|-------------|
| LocalTypeConv.lean | 187 | Named ↔ de Bruijn conversions |
| LocalTypeConvDefs.lean | 210 | Conversion definition predicates |
| LocalTypeConvProofs/Helpers.lean | 433 | Soundness of named → de Bruijn |
| LocalTypeConvProofs/ClosedRoundtrip.lean | 404 | Completeness of named → de Bruijn |
| LocalTypeConvProofs/Roundtrip.lean | 575 | Substitution equivalence under conversion |
| LocalTypeRDBBridge.lean | 47 | Bridge between LocalTypeR and LocalTypeDB |

### Supporting Modules

| File | Lines | Description |
|------|-------|-------------|
| Core.lean | 72 | Core protocol types |
| Participation/Core.lean | 297 | Participant classification in global protocols |
| Participation/Extra.lean | 410 | Extended participation properties |
| TypeContext.lean | 518 | Unified parametric context infrastructure |
| ValType.lean | 39 | Shared value types for message payloads (unit, bool, nat, string, prod, chan) |
| ObservableClosed.lean | 267 | Termination for observable behavior of closed types |

---

## SessionCoTypes

**Root Module:** `SessionCoTypes.lean`
**Description:** Coinductive theory — equi-recursive equality (EQ2), bisimulation, duality, observables, and inductive/coinductive roundtrip bridge.

### Coinductive Infrastructure

| File | Lines | Description |
|------|-------|-------------|
| CoinductiveRel.lean | 50 | Monotone endofunctors on complete lattices |
| CoinductiveRelPaco.lean | 45 | Wrappers around paco coinduction principles |

### EQ2 (Equi-Recursive Equality)

| File | Lines | Description |
|------|-------|-------------|
| EQ2/Core.lean | 493 | Core EQ2 definition and basic properties |
| EQ2/TransBase.lean | 182 | Base transitivity properties |
| EQ2Paco.lean | 243 | EQ2 with paco parametrized coinduction |
| EQ2Props.lean | 24 | Properties via bisimulation |

### Bisimulation (10 parts)

| File | Lines | Description |
|------|-------|-------------|
| Bisim/Core.lean | 360 | Definition and basic properties |
| Bisim/UnfoldingLemmas.lean | 356 | Preservation and respects relations |
| Bisim/Bisimulation.lean | 337 | Transitivity and composition |
| Bisim/EQ2Equivalence.lean | 476 | Duality and observable predicates |
| Bisim/ObservableFromEQ2.lean | 220 | Symmetry and equivalence |
| Bisim/EQ2Extraction.lean | 464 | Mu-unfold preservation |
| Bisim/EQ2ToBisim.lean | 156 | Transitive closure |
| Bisim/Congruence.lean | 367 | Substitution and duality |
| Bisim/Substitution.lean | 491 | Bisimulation as equivalence for EQ2 |
| Bisim/UnfoldSubstitute.lean | 219 | Auxiliary lemmas |

### Substitution Theory

| File | Lines | Description |
|------|-------|-------------|
| Substitute.lean | 230 | Substitution preserves EQ2 |
| SubstCommBarendregt/General.lean | 235 | General substitution commutation |
| SubstCommBarendregt/Main.lean | 551 | Main proof under Barendregt convention |
| SubstCommBarendregt/Predicates.lean | 388 | Auxiliary predicates |
| SubstCommBarendregt/SubstRel.lean | 115 | Substitution relation properties |

### Coinductive Type System

| File | Lines | Description |
|------|-------|-------------|
| Coinductive/LocalTypeC.lean | 156 | Coinductive local types via polynomial functors |
| Coinductive/Observable.lean | 138 | Observable behavior predicates |
| Coinductive/ProjectC.lean | 322 | Coinductive projection as greatest fixed point |
| Coinductive/EQ2C.lean | 419 | Equi-recursive equality for coinductive types |
| Coinductive/EQ2CProps.lean | 451 | EQ2C properties |
| Coinductive/EQ2CEnv.lean | 354 | EQ2C under environments and substitution |
| Coinductive/EQ2CMu.lean | 183 | Mu-unfolding properties for EQ2C |
| Coinductive/EQ2CPaco.lean | 73 | EQ2C with paco |

### Decidable Bisimulation

| File | Lines | Description |
|------|-------|-------------|
| Coinductive/BisimDecidable/Core.lean | 392 | Decidability framework and fuel-based computation |
| Coinductive/BisimDecidable/BisimAux.lean | 382 | Decision procedure implementation |
| Coinductive/BisimDecidable/Correctness.lean | 410 | Correctness proofs |

### Roundtrip Bridge (Inductive ↔ Coinductive)

| File | Lines | Description |
|------|-------|-------------|
| Coinductive/Bridge.lean | 52 | Bridge between representations |
| Coinductive/Regularity.lean | 101 | Regularity constraints |
| Coinductive/ToInductive.lean | 172 | Coinductive → inductive conversion |
| Coinductive/WellFormed.lean | 125 | Well-formedness conditions |
| Coinductive/Roundtrip/Core.lean | 302 | Inductive → coinductive correctness |
| Coinductive/Roundtrip/PacoCollapse.lean | 321 | Coinductive → inductive conversion |
| Coinductive/Roundtrip/EnvDefs.lean | 200 | Roundtrip composition |
| Coinductive/Roundtrip/RoundtripTheorem.lean | 544 | Completeness and characterization |
| Coinductive/Roundtrip/RoundtripCorollaries.lean | 86 | Final auxiliary lemmas |
| Coinductive/RoundtripHelpers.lean | 394 | Helper lemmas |
| Coinductive/ToCoindInjectivity.lean | 145 | Injectivity of toCoind conversion |
| Coinductive/ToCoindRegular.lean | 86 | Regularity preservation for toCoind |
| Coinductive/RegularityLemmas.lean | 81 | Auxiliary regularity lemmas |
| Coinductive/Roundtrip/GpacoCollapse.lean | 111 | Paco collapse for roundtrip proofs |

### Supporting Modules

| File | Lines | Description |
|------|-------|-------------|
| Observable.lean | 394 | Membership predicates for observable behavior |
| Dual.lean | 266 | Duality lemmas |
| FullUnfold.lean | 265 | Full unfolding with termination argument |
| Quotient.lean | 111 | Quotient by EQ2 equivalence |
| DBBridge.lean | 50 | Bridge lemmas for de Bruijn |
| Coinductive/Bisim.lean | 84 | Coinductive bisimulation definition |
| Coinductive/BisimHelpers.lean | 322 | Bisimulation helpers |
| Coinductive/Congruence.lean | 36 | Congruence properties |
| Coinductive/Coalgebra.lean | 30 | Coalgebraic structure |
| Coinductive/Dual.lean | 140 | Duality for coinductive types |
| Coinductive/RegularSystemBisim.lean | 159 | Bisimulation for finite regular systems |
| Coinductive/FiniteSystem.lean | 68 | Finite regular system representation |

### Asynchronous Subtyping

| File | Lines | Description |
|------|-------|-------------|
| AsyncSubtyping.lean | 39 | Re-export wrapper for async subtyping module |
| AsyncSubtyping/Core.lean | 382 | AsyncTriple, MsgBuffer, 7 async step rules, AsyncSubtypeRel coinductive relation |
| AsyncSubtyping/Decidable.lean | 381 | checkAsync worklist algorithm, isAsyncSubtype decision function, soundness/completeness |

Plus 5 namespace re-export modules: Bisim.lean, EQ2.lean, SubstCommBarendregt.lean, Coinductive/BisimDecidable.lean, Coinductive/Roundtrip.lean.

---

## Choreography

**Root Module:** `Choreography.lean`
**Description:** Projection from global to local session types and its correctness (harmony), includes blindness predicates, erasure, and embedding.

### Trans Projection (Coq-style)

| File | Lines | Description |
|------|-------|-------------|
| Projection/Trans/Core.lean | 428 | Core projection algorithm |
| Projection/Trans/Participation.lean | 196 | Participation filtering |
| Projection/Trans/Contractive.lean | 333 | Guardedness analysis for recursive projection |

### Boolean Projection Checker

| File | Lines | Description |
|------|-------|-------------|
| Projection/Projectb/Checker.lean | 205 | Boolean projection definition |
| Projection/Projectb/Coinductive.lean | 465 | Branch handling |
| Projection/Projectb/Soundness.lean | 387 | Correctness lemmas |
| Projection/Projectb/Completeness.lean | 566 | Mu-type handling |

### Proof-Carrying Projection API

| File | Lines | Description |
|------|-------|-------------|
| Projection/Project/Core.lean | 123 | Core API definitions |
| Projection/Project/MuveImplBase.lean | 561 | Base mu-unfolding cases |
| Projection/Project/MuveImplParticipant.lean | 544 | Participant mu-unfolding elimination |
| Projection/Project/MuveImplNonPart.lean | 429 | Non-participant mu-unfolding elimination |
| Projection/Project/ImplBase.lean | 431 | Base projection implementation |
| Projection/Project/ImplConstructors/Base.lean | 427 | End, var, mu cases |
| Projection/Project/ImplConstructors/SendRecv.lean | 366 | Send/recv cases |
| Projection/Project/ImplConstructors/Mu.lean | 192 | Branching cases |
| Projection/Project/ImplCompleteness.lean | 314 | Completeness proof |
| Projection/Project/ImplObservables.lean | 362 | Observable properties preservation |
| Projection/Project/ImplHeadPreservation.lean | 463 | Head shape preservation |
| Projection/Project/ImplExtraction/ObservableExtraction.lean | 306 | Observable extraction |
| Projection/Project/ImplExtraction/RecvExtraction.lean | 330 | Payload and branch extraction |
| Projection/Project/ImplTransRelComp/Core.lean | 331 | Transition relation base cases |
| Projection/Project/ImplTransRelComp/CommCases.lean | 354 | Transition relation properties |
| Projection/Project/ImplCompPostfix/WellFormedClosure.lean | 321 | Observable postfix computation |
| Projection/Project/ImplCompPostfix/PrefixCases.lean | 219 | Observable list postfix |
| Projection/Project/ImplCompPostfix/SuffixCases.lean | 356 | Postfix properties |
| Projection/Project/ImplU/EQ2Closure.lean | 355 | Unfolding base cases |
| Projection/Project/ImplU/CommCases.lean | 363 | Unfolding lemmas and composition |

### Blindness Predicate

| File | Lines | Description |
|------|-------|-------------|
| Projection/Blind/Core.lean | 492 | Definition and basic properties |
| Projection/Blind/Preservation.lean | 187 | Preservation and composition |
| Projection/Blind.lean | 7 | Re-export wrapper for Blind/Core and Blind/Preservation |

### Harmony (Projection Correctness)

| File | Lines | Description |
|------|-------|-------------|
| Harmony.lean | 150 | Main harmony structure |
| Harmony/MuUnfoldLemmas.lean | 257 | Mu-unfolding auxiliary lemmas |
| Harmony/StepProjection.lean | 255 | Projection preserves stepping semantics |
| Harmony/SubstEndUnguarded.lean | 239 | Substitution with guardedness constraints |
| Harmony/StepHarmony.lean | 423 | Main structure |
| Harmony/Substitution.lean | 519 | Communication handling |
| Harmony/ParticipantSteps.lean | 533 | Branching |
| Harmony/NonParticipantHelpers.lean | 126 | Recursion |
| Harmony/NonParticipantSteps.lean | 147 | Final properties |

### Supporting Modules

| File | Lines | Description |
|------|-------|-------------|
| Projection/ProjSubst.lean | 410 | Projection-substitution commutation |
| Projection/ProjectProps.lean | 143 | General projection properties |
| Projection/ComposeProof.lean | 60 | Composition of projection lemmas |
| Projection/Embed.lean | 233 | Coinductive embedding relation |
| Projection/EmbedProps.lean | 510 | Embedding properties |
| Projection/Erasure/Core.lean | 80 | Erasure definition |
| Projection/Erasure/Merge.lean | 358 | Erasure lemmas |
| Projection/Erasure/MergeSoundness.lean | 425 | Erasure correctness |
| Assumptions.lean | 15 | Centralized assumptions |

### JSON and Validation Infrastructure

| File | Lines | Description |
|------|-------|-------------|
| Projection/Json.lean | 177 | JSON serialization for GlobalType, LocalTypeR matching lean-bridge schema |
| Projection/Validator.lean | 198 | CLI validator for projection results, runValidation, runExportProjection |

---

## Semantics

**Root Module:** `Semantics.lean`
**Description:** Operational semantics, typing judgments, determinism, deadlock freedom, subject reduction.

| File | Lines | Description |
|------|-------|-------------|
| Environment.lean | 299 | Environment configuration (message queues, timeouts, actions) |
| EnvStep.lean | 191 | Environment-step relation |
| Typing.lean | 23 | Typing judgment interface |
| Determinism/Core.lean | 600 | Determinism proof part 1 |
| Determinism/Diamond.lean | 516 | Determinism proof part 2 |
| DeadlockFreedom.lean | 293 | Deadlock freedom with fairness |
| SubjectReduction.lean | 201 | Subject reduction for well-typed processes |

---

## Classical

**Root Module:** `Classical.lean`
**Description:** Transported theorems from queueing theory, probability, and stochastic processes, organized into family kernels and a layered transport API.

### Families

| File | Description |
|------|-------------|
| Families/FosterLyapunovHarris.lean | Foster-Lyapunov-Harris theorem for stability/recurrence |
| Families/MaxWeightBackpressure.lean | MaxWeight scheduling optimality and backpressure |
| Families/LargeDeviationPrinciple.lean | Large deviation bounds for rare events |
| Families/HeavyTrafficDiffusion.lean | Heavy traffic diffusion limits |
| Families/MixingTimeBounds.lean | Mixing-time bounds for Markov chains |
| Families/FluidLimitStability.lean | Fluid-limit stability analysis |
| Families/ConcentrationInequalities.lean | Concentration inequalities |
| Families/LittlesLaw.lean | Little's law identities |
| Families/FunctionalCLT.lean | Functional central limit theorem |
| Families/PropagationOfChaos.lean | Mean-field limits and propagation of chaos |
| Families/SpectralGapTermination.lean | Spectral-gap / Cheeger / hitting-time interfaces |

### Transport Layers

| File | Description |
|------|-------------|
| Transport/Context.lean | Shared transport context |
| Transport/Contracts.lean | Input/Conclusion contracts per theorem family |
| Transport/Theorems.lean | Facade theorem wrappers |
| Transport/API.lean | Stable transport facade import |

---

## Distributed

**Root Module:** `Distributed.lean`
**Description:** Family-oriented distributed characterization with a transport layer for validation and family usage.

### Model

| File | Description |
|------|-------------|
| Model/Assumptions.lean | Base distributed assumptions and assumption-check functions |
| Model/Types.lean | Protocol-space model types and protocol spec |
| Model/Classifier.lean | BFT/Nakamoto/Hybrid classification predicates |

### Families

| File | Description |
|------|-------------|
| Families/FLP.lean | FLP assumptions, premises, and auto-derived lower-bound/impossibility packaging |
| Families/CAP.lean | CAP assumptions, premises, and auto-derived impossibility packaging |
| Families/QuorumGeometry.lean | Quorum-intersection safety family: no-conflict commits, fork exclusion, safe finality |
| Families/PartialSynchrony.lean | Partial-synchrony liveness family: eventual decision and bounded post-GST termination |
| Families/Responsiveness.lean | Responsiveness family: optimistic post-GST latency bound independent of timeout |
| Families/Nakamoto.lean | Nakamoto security family: probabilistic safety, settlement-depth finality, churn-liveness |
| Families/Reconfiguration.lean | Reconfiguration safety family: no split-brain, safe handoff, liveness preservation |
| Families/AtomicBroadcast.lean | Atomic-broadcast family: total-order consistency, log-prefix compatibility, consensus bridge |
| Families/AccountableSafety.lean | Accountable-safety family: safety-or-evidence theorem with slashable fault evidence |
| Families/FailureDetectors.lean | Failure-detector family: detector-class solvability/impossibility boundary forms |
| Families/DataAvailability.lean | Data-availability family: k-of-n availability/retrievability under sampling and withholding bounds |
| Families/Coordination.lean | Coordination family: CALM-style monotonicity characterization of coordination necessity |

### Transport

| File | Description |
|------|-------------|
| Transport/Context.lean | Transported-family eligibility context and assumption atoms |
| Transport/Contracts.lean | Validation summary contracts |
| Transport/Theorems.lean | High-level validation/combination APIs |
| Transport/API.lean | Transport facade import |

### Facade

| File | Description |
|------|-------------|
| Distributed.lean | Distributed root facade import |

---

## Protocol

**Root Module:** `Protocol.lean`
**Description:** Async buffered multiparty session types with coherence invariant, preservation, deadlock freedom, monitoring, and deployment composition.

### Foundational Types

| File | Lines | Description |
|------|-------|-------------|
| Basic.lean | 185 | SessionId, Role, Endpoint, Label, Edge, RoleSet |
| LocalType.lean | 254 | Local session types with send/recv/select/branch/mu, depth functions |
| Values.lean | 191 | Runtime values, linear capability tokens, session ID bounds |
| Process.lean | 149 | Process language (skip, seq, par, send, recv, select, branch, newSession) |

### Environments

| File | Lines | Description |
|------|------:|-------------|
| Environments/Core.lean | 1,338 | Store, SEnv, GEnv, DEnv, Buffers — lookup/update/init, DEnvUnion |
| Environments/Renaming.lean | 493 | Session renaming with injectivity/commutativity |
| Environments/RoleRenaming.lean | 83 | Role-based session renaming with correctness properties |

### Coherence (21 parts)

Central invariant replacing traditional duality for multiparty async settings.

| File | Lines | Description |
|------|------:|-------------|
| Coherence/Consume.lean | 253 | `Consume`, `EdgeCoherent`, `Coherent`, `HasTypeVal` |
| Coherence/EdgeCoherence.lean | 525 | `BufferTyped`, `StoreTyped`, `ActiveEdge` |
| Coherence/StoreTyping.lean | 136 | `StoreTypedStrong`, irrelevance lemmas |
| Coherence/Preservation.lean | 545 | `Coherent_send_preserved`, `Coherent_recv_preserved` |
| Coherence/SelectPreservation.lean | 356 | `Coherent_select_preserved`, `Coherent_branch_preserved` |
| Coherence/HeadPreservationSend.lean | 507 | Helper lemmas |
| Coherence/HeadPreservationSelect.lean | 376 | `HeadCoherent_select/branch_preserved` |
| Coherence/ValidLabels.lean | 660 | `Coherent_empty`, `initSession_coherent`, ValidLabels |
| Coherence/Renaming.lean | 305 | `CoherentRenaming`, `Dual_implies_Coherent_empty` |
| Coherence/ConfigEquiv.lean | 737 | `CoherenceConfig`, `ConfigEquiv`, quotient structure for session isomorphisms |
| Coherence/Unified.lean | 31 | `edge_case_split` — 3-way edge case analysis for preservation proofs |
| Coherence/EdgeCoherenceM.lean | 115 | Model-parametric `EdgeCoherent` variants |
| Coherence/HeadCoherenceM.lean | 28 | Model-parametric `HeadCoherent` |
| Coherence/PreservationDeliveryModels.lean | 157 | Parametrized preservation lemmas for different delivery models |
| Coherence/SubtypeReplacement.lean | 517 | `RecvCompatible`, `Consume_mono`, `Coherent_type_replacement`, liveness preservation |
| Coherence/GraphDelta.lean | 547 | Higher-order `Consume` with graph deltas for channel delegation |
| Coherence/Delegation.lean | 878 | `DelegationStep`, `DelegationWF`, `delegation_preserves_coherent` |
| Coherence/RoleSwap.lean | 895 | Bijective role renaming within session, coherence preservation under role swap |
| Coherence/ErasureCharacterization.lean | 165 | Erasure characterization and configuration equivalence |
| Coherence/Conserved.lean | 203 | Conserved quantities and Noether-style correspondence |
| Coherence/Minimality.lean | 207 | Weak coherence, strictness witness, minimality theorem |

### Typing (8 parts)

| File | Lines | Description |
|------|-------|-------------|
| Typing/Core.lean | 651 | Disjointness, splitting (`ParSplit`), `DConsistent` |
| Typing/Judgments.lean | 567 | `HasTypeProcN` / `HasTypeProcPreOut` / `TypedStep`, plus `ParWitness` inversion and par-index irrelevance |
| Typing/Compatibility.lean | 992 | SEnv append/lookup lemmas |
| Typing/MergeLemmas.lean | 327 | Additional environment lemmas |
| Typing/StepLemmas.lean | 478 | `WTConfigN` well-typed configuration |
| Typing/Framing.lean | 13 | Framing entry point (re-exports) |
| Typing/Framing/Lemmas.lean | 1,331 | Constructive frame lemmas (including middle-frame preservation; no framing axioms) |
| Typing/Framing/FramedPreUpdate.lean | 308 | Pre-out preservation under G frames |
| Typing/Framing/PreUpdateHelpers.lean | 293 | Alignment helpers for framed pre-update proofs |
| Typing/Framing/LeftCases.lean | 266 | Left-frame step cases for pre-update |
| Typing/Framing/RightCases.lean | 280 | Right-frame step cases for pre-update |
| Typing/Framing/PreUpdatePreservation.lean | 409 | Lifting pre-update preservation to main theorems |
| Typing/Framing/GEnvFrame.lean | 11 | GEnv framing re-exports |
| Typing/Framing/GEnvFramePre.lean | 81 | Pre-typing right-frame lemma |
| Typing/Framing/GEnvFrameHelpers.lean | 50 | Shared disjointness helpers |
| Typing/Framing/GEnvFrameRight.lean | 202 | Pre-out right-frame lemma + framed par `nG` irrelevance regression lemma |
| Typing/Framing/GEnvFrameLeft.lean | 280 | Pre-out left-frame lemma + framed par `nG` irrelevance regression lemma |
| Typing/Preservation.lean | 2,137 | Constructive preservation sub-lemmas (`Compatible`) |
| Typing/Progress.lean | 472 | DEnv union and environment append properties |

### Par Witness / Quotient View (Typing Layer)

- `Typing/Judgments.lean` now encodes par split identity via `ParWitness` (split + left-length witness).
- Inversion APIs are witness-oriented: `HasTypeProcPreOut_par_inv_witness`, `TypedStep_par_inv`.
- Ambient par index on the right (`nG`) is quotient-style/irrelevant at typing level:
  - `HasTypeProcPre_par_nG_irrel`
  - `HasTypeProcPreOut_par_nG_irrel`
- Framed regression lemmas make this explicit at transport boundaries:
  - `HasTypeProcPreOut_frame_G_right_par_nG_irrel` (`Typing/Framing/GEnvFrameRight.lean`)
  - `HasTypeProcPreOut_frame_G_left_par_nG_irrel` (`Typing/Framing/GEnvFrameLeft.lean`)

### Operational Semantics

| File | Lines | Description |
|------|-------|-------------|
| Semantics.lean | 358 | `StepBase` (send/recv/select/branch/newSession/assign), `Step` (contextual closure) |

### Main Theorems

| File | Lines | Description |
|------|-------|-------------|
| Preservation.lean | 1,933 | `preservation_typed`, `progress_*`, `subject_reduction` |
| Determinism.lean | 359 | `stepBase_det`, `diamond_independent`, `session_isolation` |
| DeadlockFreedom.lean | 632 | `Guarded`, `ReachesComm`, `deadlock_free`, `not_stuck` |

### Runtime Monitoring

| File | Lines | Description |
|------|-------|-------------|
| Monitor/Core.lean | 477 | `ProtoAction`, `MonitorState`, `MonStep`, `WTMon` |
| Monitor/Preservation.lean | 187 | `MonStep_preserves_WTMon`, `newSession_preserves_WTMon` — 2 axioms |

### Deployment Composition

| File | Lines | Description |
|------|-------|-------------|
| Deployment/Interface.lean | 438 | `InterfaceType`, `DeployedProtocol`, `ProtocolBundle` |
| Deployment/Merge.lean | 296 | `MergeDEnv`, disjoint sessions |
| Deployment/Linking.lean | 87 | Composition metatheory — 8 axioms |

### Supporting Modules

| File | Lines | Description |
|------|------:|-------------|
| Spatial.lean | 515 | `SpatialReq`, `Topology`, `Satisfies`, `spatial_le_sound`, `ConfusabilityGraph`, branching feasibility |
| Symmetry.lean | 863 | Symmetry properties, role-symmetric protocols, symmetry-preserving operations |
| BufferBoundedness.lean | 1,217 | Buffer boundedness analysis, depth bounds, capacity constraints |
| Simulation.lean | 540 | `stepDecide`, `runSteps`, `traceSteps`, soundness/completeness |
| Decidability.lean | 108 | DecidableEq instances |
| Examples.lean | 19 | Protocol examples (stubbed) |
| CrashTolerance.lean | 225 | `CommGraph`, `CrashTolerant`, `Critical`, crash tolerance predicates |
| Noninterference.lean | 552 | `CEquiv`, `BlindTo`, `blind_step_preserves_CEquiv` noninterference theorem |
| DeliveryModel.lean | 214 | `DeliveryModel` typeclass, FIFO/causal/lossy instances |
| CoherenceM.lean | 15 | Model-parametric coherence re-export wrapper |
| InformationCost.lean | 1050 | `ProjectionMap`, entropy, mutual information, blind projection |

### Classical Regime (5 parts)

Protocol-specific instantiation of the classical transport framework.

| File | Lines | Description |
|------|-------|-------------|
| Classical/Regime.lean | 74 | Classical regime definition, totality, determinism, exchangeability |
| Classical/Framework.lean | 126 | TransportFramework, step induction, classical regime instantiation |
| Classical/TransportLedger.lean | 88 | Ledger bookkeeping for transported theorem discharge planning |
| Classical/SpectralGap.lean | 97 | Spectral gap bounds, mixing time analysis, Cheeger inequality interface |
| Classical/Instantiation.lean | 474 | Protocol-facing instantiation (Foster-Lyapunov, MaxWeight, Mean-field) |

---

## Runtime

**Root Module:** `Runtime.lean`
**Description:** VM definition, Iris separation logic backend via iris-lean, resource algebras, session invariants, WP rules, and adequacy.

### Iris Bridge (iris-lean integration)

Consolidated interface to iris-lean separation logic. Ghost maps use `Positive` keys with encoding. Contains 10 axioms for WP/invariant rules.

| File | Lines | Description |
|------|------:|-------------|
| IrisBridge.lean | 545 | `TelltaleIris` typeclass, iProp, sep logic connectives, ghost_map/ghost_var, invariants, WP rules |

### VM Model (VM/Model/)

| File | Lines | Description |
|------|------:|-------------|
| Core.lean | 67 | Register file, instruction set, coroutine |
| Config.lean | 85 | VMConfig, VMState, ResourcePool |
| State.lean | 304 | Full machine state, session table, buffer management |
| Program.lean | 137 | Program representation and code segments |
| TypeClasses.lean | 251 | Identity, guard, persistence, effect, verification model typeclasses |
| CompileLocalTypeR.lean | 190 | Compiler from LocalTypeR to VM bytecode instructions |
| Knowledge.lean | 30 | Knowledge base and fact management |
| Violation.lean | 29 | Violation policy and fault types |
| SchedulerTypes.lean | 26 | Scheduler type definitions |
| UnitModel.lean | 184 | Minimal computable instances for all VM domain typeclasses |
| OutputCondition.lean | 54 | Output-condition model for commit gating |

### VM Semantics (VM/Semantics/)

| File | Lines | Description |
|------|------:|-------------|
| Exec.lean | 127 | Top-level step function dispatch |
| ExecHelpers.lean | 422 | Register operations, buffer lookup, shared helpers |
| ExecComm.lean | 449 | Send/recv/select/branch execution |
| ExecSession.lean | 304 | Session open/close/fork/join |
| ExecOwnership.lean | 162 | Ownership transfer and capability operations |
| ExecControl.lean | 103 | Control flow (jump, call, return, halt) |
| ExecGuardEffect.lean | 111 | Guard chain evaluation and effect dispatch |
| ExecSpeculation.lean | 66 | Speculative execution (fork/join/abort) |
| ExecSteps.lean | 54 | Multi-step execution wrapper |
| InstrSpec.lean | 324 | Denotational specs for 8 instruction types |

### VM Runtime (VM/Runtime/)

| File | Lines | Description |
|------|------:|-------------|
| Loader.lean | 109 | Dynamic choreography loading into running VM state |
| Runner.lean | 104 | N-concurrent scheduler-driven execution loop |
| Scheduler.lean | 294 | Process scheduler with fairness and priority |
| Monitor.lean | 139 | SessionKind, WellTypedInstr judgment, unified session monitor |
| Failure.lean | 290 | Failure modes (crash, partition, heal), FStep relation, recovery predicates |
| Json.lean | 145 | JSON serialization for runtime values and trace events |

### VM Composition (VM/Composition/)

| File | Lines | Description |
|------|------:|-------------|
| DomainComposition.lean | 326 | Domain-specific composition and guard chain |

### Resources

| File | Lines | Description |
|------|-------|-------------|
| Resources/ResourceModel.lean | 179 | Resource model interface and profiles |
| Resources/SessionRA.lean | 88 | Session resource algebra with auth/frag |
| Resources/BufferRA.lean | 317 | Message buffer resource algebra with auth/frag |
| Resources/Arena.lean | 1,379 | Memory arena with pointsto, allocation, and ownership tracking |
| Resources/ProfilesV1.lean | 42 | V1 resource profile definitions |

### Program Logic

| File | Lines | Description |
|------|-------|-------------|
| ProgramLogic/LanguageInstance.lean | 93 | Iris `Language`/`EctxLanguage` instances |
| ProgramLogic/SessionWP.lean | 122 | Session-level WP rules |
| ProgramLogic/GhostState.lean | 281 | Ghost state management (session maps, buffer maps) |
| ProgramLogic/CodeLoading.lean | 99 | Code loading and program verification |
| ProgramLogic/ProofInterfaces.lean | 91 | Proof interface typeclasses |
| ProgramLogic/WPPair.lean | 131 | WP pairing for send/recv duality |
| ProgramLogic/WPPipeline.lean | 25 | WP pipeline composition |
| ProgramLogic/FinalizationWP.lean | 39 | Finalization and cleanup WP rules |

### Invariants and Transport

| File | Lines | Description |
|------|------:|-------------|
| Invariants/SessionInv.lean | 256 | Session invariant: coherence, buffers, endpoint state |
| Transport/Transport.lean | 232 | Abstract transport layer with handler specs |
| Cost/Credits.lean | 56 | Cost credit resource algebra |

### Proofs/VM (VM Instruction Proofs)

| File | Lines | Description |
|------|------:|-------------|
| Proofs/VM/InstrSpec.lean | 1,415 | Preservation theorems for all 8 instruction types, quotient-respecting variants |
| Proofs/VM/Scheduler.lean | 136 | Scheduler proof infrastructure |
| Proofs/VM/DomainComposition.lean | 49 | Domain composition and guard chain proofs |
| Proofs/VM/ExecOwnership.lean | 22 | Ownership transfer proof bridge |
| Proofs/VM/LoadChoreography.lean | 37 | Choreography loading and verification |

### Adequacy and Proofs

| File | Lines | Description |
|------|------:|-------------|
| Adequacy/Adequacy.lean | 168 | Adequacy theorem connecting WP to execution |
| Proofs/RuntimeTheorems.lean | 465 | Runtime theorem facade unifying proof exports |
| Proofs/Concurrency.lean | 109 | Iris-backed N-invariance and policy-invariance proofs |
| Proofs/CompileLocalTypeRCorrectness.lean | 53 | Compiler correctness stubs (nonempty, ends with halt/jmp) |
| Proofs/SessionLocal.lean | 337 | `SessionSlice`, `SessionCoherent`, session-local frame infrastructure |
| Proofs/Frame.lean | 128 | `session_local_op_preserves_other`, `disjoint_ops_preserve_unrelated` |
| Proofs/Delegation.lean | 6 | Re-export wrapper importing `Protocol.Coherence.Delegation` |
| Proofs/Progress.lean | 607 | `CoherentVMState`, `ProgressVMState`, `vm_progress`, instruction enablement |
| Proofs/ProgressApi.lean | 181 | Bundle-oriented liveness API and optional progress hypothesis surface |
| Proofs/InvariantSpace.lean | 61 | Proof-carrying invariant-space bundle for VM theorem derivation |
| Proofs/Adapters/Progress.lean | 50 | Invariant-space adapters for liveness/progress theorems |
| Proofs/Adapters/Distributed.lean | 447 | Invariant-space adapters for distributed profiles (FLP/CAP, quorum-geometry, partial-synchrony, responsiveness, Nakamoto, reconfiguration, atomic-broadcast, accountable-safety, failure-detectors, data-availability, coordination) |
| Proofs/Adapters/Classical.lean | 416 | Invariant-space adapters for classical transport profiles and artifacts |
| Proofs/TheoremPack.lean | 499 | Unified VM theorem pack and theorem inventory summary |
| Proofs/Lyapunov.lean | 381 | `progressMeasure`, weighted measure W = 2·depth + buffer |
| Proofs/VMPotential.lean | 266 | VM potential integration and transported Foster bridge |
| Proofs/WeightedMeasure.lean | 1,198 | Lyapunov measure infrastructure, step decrease theorems |
| Proofs/SchedulingBound.lean | 670 | k-fair scheduler termination bounds, round-robin corollary |
| Proofs/Diamond.lean | 468 | Cross-session diamond lemmas and main confluence theorem |
| Proofs/Examples/DistributedProfiles.lean | 115 | End-to-end VM examples: profile attachment auto-materializes distributed theorem artifacts |
| Proofs/Examples/InvariantBundle.lean | 74 | One-shot invariant-bundle examples for liveness/progress, FLP/CAP, and classical artifact derivation |

### Examples and Tests

| File | Lines | Description |
|------|-------|-------------|
| Examples/SimpleProtocol.lean | 127 | Simple two-party protocol example |
| Examples/Aura.lean | 133 | Aura instantiation example |
| Tests/Main.lean | 98 | Runtime test harness |
| Tests/VMRunner.lean | 116 | JSON-driven VM runner (stdin choreographies, stdout traces) |

---

## Build Configuration

### lakefile.lean

Eight library targets with glob-based module discovery:

```
telltale (package)
├── SessionTypes     ← Global/local types, de Bruijn, participation
├── SessionCoTypes   ← Coinductive EQ2, bisimulation, roundtrip
├── Choreography     ← Projection, harmony, blindness, erasure
├── Semantics        ← Operational semantics, typing, determinism
├── ClassicalLayer   ← Transported queueing/probability theorem families + transport API
├── Distributed      ← Distributed theorem families (FLP/CAP, quorum safety, liveness, ordering, DA, coordination)
├── Protocol         ← Async MPST, coherence, preservation, monitoring
└── Runtime          ← VM, Iris backend, WP, adequacy (default target)
```

**Dependencies:** mathlib, paco-lean v0.1.3, iris-lean

---

## Axiom Inventory

### Global Status

`rg -n "^axiom " -g'*.lean'` returns no results. The repository is currently axiom-free.

### Sorry Concentration

**Status:** All sorries eliminated. The codebase is fully proved.

| Library | Sorry Count | Status |
|---------|------------:|--------|
| SessionCoTypes | 0 | AsyncSubtyping/Core.lean, Decidable.lean — complete |
| Protocol | 0 | Coherence, CrashTolerance, Noninterference — complete |
| Runtime | 0 | Progress, SchedulingBound, WeightedMeasure, Diamond — complete |
| **Total** | **0** | **Fully proved** |

---

## Proof Strategies

### 1. Coherence as Central Invariant
Replaces traditional binary duality with coherence: for each directed edge, consuming the in-flight message trace from the receiver's perspective succeeds. Generalizes to multiparty async settings.

### 2. Consumption Function
`Consume` models how a receiver's local type evolves as buffered messages arrive. Key composition: `Consume L (ts1 ++ ts2) = (Consume L ts1).bind (fun L' => Consume L' ts2)`.

### 3. Three-Way Edge Analysis
Coherence preservation proofs split per edge: updated (type+trace change), related (shares endpoint), unrelated (trivially preserved).

### 4. Parametrized Coinduction (paco)
EQ2 and bisimulation proofs use paco-lean for parametrized coinduction, avoiding manual guardedness arguments.

### 5. Iris Integration via iris-lean
Runtime library connects to iris-lean for separation logic primitives. Ghost maps use `Positive` keys with application-level encoding. The `GhostMapSlot V` typeclass registers value types.

### 6. Linear Capability Tokens
Unforgeable tokens tied to endpoints enforce linear resource usage. The monitor validates token ownership before permitting actions.

---

## Quick Navigation Guide

**Want to understand...**

- **Session type definitions?** → SessionTypes/GlobalType/Core.lean, LocalTypeR/Core.lean
- **De Bruijn indices?** → SessionTypes/LocalTypeDB/Core.lean
- **Coinductive equality (EQ2)?** → SessionCoTypes/EQ2/Core.lean
- **Bisimulation?** → SessionCoTypes/Bisim/Core.lean
- **Inductive ↔ coinductive bridge?** → SessionCoTypes/Coinductive/Roundtrip/
- **Asynchronous subtyping?** → SessionCoTypes/AsyncSubtyping/Core.lean, Decidable.lean
- **Projection algorithm?** → Choreography/Projection/Project/Core.lean, ImplBase.lean
- **Projection correctness (harmony)?** → Choreography/Harmony.lean, Harmony/StepHarmony.lean
- **Operational semantics?** → Semantics/Environment.lean, Protocol/Semantics.lean
- **Coherence invariant?** → Protocol/Coherence/Consume.lean, Protocol/Coherence/EdgeCoherence.lean
- **Coherence preservation?** → Protocol/Coherence/Preservation.lean, Protocol/Coherence/SelectPreservation.lean
- **Subtype replacement preservation?** → Protocol/Coherence/SubtypeReplacement.lean
- **Configuration equivalence (quotient)?** → Protocol/Coherence/ConfigEquiv.lean
- **Unified preservation skeleton?** → Protocol/Coherence/Unified.lean
- **Higher-order Consume (delegation)?** → Protocol/Coherence/GraphDelta.lean
- **Role renaming proofs?** → Protocol/Coherence/RoleSwap.lean
- **Type system?** → Protocol/Typing/Judgments.lean (`HasTypeProcN`, `WTConfigN`)
- **Type safety?** → Protocol/Preservation.lean
- **Deadlock freedom?** → Protocol/DeadlockFreedom.lean
- **Runtime monitoring?** → Protocol/Monitor/Core.lean
- **Deployment composition?** → Protocol/Deployment/Interface.lean, Protocol/Deployment/Linking.lean
- **Crash tolerance?** → Protocol/CrashTolerance.lean
- **Noninterference?** → Protocol/Noninterference.lean
- **Delivery models?** → Protocol/DeliveryModel.lean
- **Classical transport framework?** → Classical/Transport.lean
- **Foster-Lyapunov-Harris?** → Classical/FosterLyapunovHarris.lean
- **Protocol-level classical instantiation?** → Protocol/Classical/Instantiation.lean
- **Iris separation logic (iris-lean)?** → Runtime/IrisBridge.lean
- **Ghost state?** → Runtime/ProgramLogic/GhostState.lean
- **Session-local proofs?** → Runtime/Proofs/SessionLocal.lean, Runtime/Proofs/Frame.lean
- **Delegation proofs?** → Protocol/Coherence/Delegation.lean
- **VM-level progress theorem?** → Runtime/Proofs/Progress.lean
- **Lyapunov measure?** → Runtime/Proofs/Lyapunov.lean, Runtime/Proofs/WeightedMeasure.lean
- **Scheduling bounds?** → Runtime/Proofs/SchedulingBound.lean
- **VM instruction specifications?** → Runtime/VM/Semantics/InstrSpec.lean
- **VM instruction preservation proofs?** → Runtime/Proofs/VM/InstrSpec.lean
- **VM bytecode compiler?** → Runtime/VM/Model/CompileLocalTypeR.lean
- **Dynamic choreography loading?** → Runtime/VM/Runtime/Loader.lean
- **N-concurrent scheduling?** → Runtime/VM/Runtime/Runner.lean, Runtime/Proofs/Concurrency.lean
- **VM failure model?** → Runtime/VM/Runtime/Failure.lean
- **Buffer boundedness?** → Protocol/BufferBoundedness.lean
- **Protocol symmetry?** → Protocol/Symmetry.lean
- **Spectral gap bounds?** → Protocol/Classical/SpectralGap.lean
- **VM JSON runner?** → Runtime/Tests/VMRunner.lean
- **What is axiomatized?** → [Axiom Inventory](#axiom-inventory)
