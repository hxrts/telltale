# Lean Verification Code Map

**Last Updated:** 2026-01-31

Comprehensive map of the Telltale Lean 4 verification library — formal verification of choreographic programming with multiparty session types.

## Table of Contents

1. [Overview](#overview)
2. [SessionTypes](#sessiontypes)
3. [SessionCoTypes](#sessioncotypes)
4. [Choreography](#choreography)
5. [Semantics](#semantics)
6. [Protocol](#protocol)
7. [Runtime](#runtime)
8. [Build Configuration](#build-configuration)
9. [Axiom Inventory](#axiom-inventory)
10. [Proof Strategies](#proof-strategies)
11. [Quick Navigation Guide](#quick-navigation-guide)

---

## Overview

**Toolchain:** Lean 4 v4.26.0
**Build:** Lake with 6 library targets
**Dependencies:** mathlib, paco-lean v0.1.3

| Library | Files | Lines | Focus |
|---------|-------|-------|-------|
| SessionTypes | 31 | ~8,054 | Global/local type definitions, de Bruijn, participation |
| SessionCoTypes | 60 | ~10,357 | Coinductive EQ2, bisimulation, duality, roundtrip bridge |
| Choreography | 54 | ~8,783 | Projection, harmony, blindness, embedding, erasure |
| Semantics | 8 | ~2,177 | Operational semantics, determinism, deadlock freedom |
| Protocol | 51 | ~12,409 | Async buffered MPST, coherence, preservation, monitoring |
| Runtime | 19 | ~601 | VM scaffold, Iris separation logic shims, resource algebras |
| **Total** | **223** | **~42,381** | |

**Architectural Layers:**
```
Layer 6: Runtime          → VM, Iris backend, resource algebras, WP, adequacy
Layer 5: Protocol         → Async MPST, coherence, typing, preservation, monitoring, deployment
Layer 4: Semantics        → Operational semantics, typing judgments, determinism, deadlock freedom
Layer 3: Choreography     → Projection, harmony, blindness, embedding, erasure
Layer 2: SessionCoTypes   → Coinductive EQ2, bisimulation, duality, roundtrip bridge
Layer 1: SessionTypes     → Global/local types, de Bruijn, participation, spatial
```

---

## SessionTypes

**Root Module:** `SessionTypes.lean`
**Description:** Inductive session type definitions with de Bruijn indices and recursive binders.

### Global Types

| File | Lines | Description |
|------|-------|-------------|
| GlobalType/Part1.lean | 329 | Global type definitions and operations |
| GlobalType/Part2.lean | 357 | Global type substitution |
| GlobalType/Part3.lean | 346 | Global stepping semantics |
| GlobalType/Part4.lean | 294 | Well-formedness and properties |
| GlobalType/Part5.lean | 577 | Observable behavior and duality |

### Local Types (Recursive)

| File | Lines | Description |
|------|-------|-------------|
| LocalTypeR/Part1.lean | 513 | Recursive local type definitions |
| LocalTypeR/Part2.lean | 354 | Well-formedness and operations |
| LocalTypeR/Part3.lean | 249 | Observable predicates |
| LocalTypeR/Part4.lean | 398 | Substitution and operations |
| LocalTypeR/Part5.lean | 274 | Duality and properties |

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
| LocalTypeConvProofs/Part1.lean | 433 | Soundness of named → de Bruijn |
| LocalTypeConvProofs/Part2.lean | 404 | Completeness of named → de Bruijn |
| LocalTypeConvProofs/Part3.lean | 575 | Substitution equivalence under conversion |
| LocalTypeRDBBridge.lean | 47 | Bridge between LocalTypeR and LocalTypeDB |

### Supporting Modules

| File | Lines | Description |
|------|-------|-------------|
| Core.lean | 72 | Core protocol types |
| Participation/Core.lean | 297 | Participant classification in global protocols |
| Participation/Extra.lean | 410 | Extended participation properties |
| TypeContext.lean | 518 | Unified parametric context infrastructure |
| Spatial.lean | 323 | Spatial type system with topology satisfaction |
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
| Bisim/Part1.lean | 360 | Definition and basic properties |
| Bisim/Part2.lean | 356 | Preservation and respects relations |
| Bisim/Part3.lean | 337 | Transitivity and composition |
| Bisim/Part4.lean | 476 | Duality and observable predicates |
| Bisim/Part5.lean | 220 | Symmetry and equivalence |
| Bisim/Part6.lean | 464 | Mu-unfold preservation |
| Bisim/Part7.lean | 156 | Transitive closure |
| Bisim/Part8.lean | 367 | Substitution and duality |
| Bisim/Part9.lean | 491 | Bisimulation as equivalence for EQ2 |
| Bisim/Part10.lean | 219 | Auxiliary lemmas |

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
| Coinductive/BisimDecidable/Part1.lean | 392 | Decidability framework and fuel-based computation |
| Coinductive/BisimDecidable/Part2.lean | 382 | Decision procedure implementation |
| Coinductive/BisimDecidable/Part3.lean | 410 | Correctness proofs |

### Roundtrip Bridge (Inductive ↔ Coinductive)

| File | Lines | Description |
|------|-------|-------------|
| Coinductive/Bridge.lean | 52 | Bridge between representations |
| Coinductive/Regularity.lean | 101 | Regularity constraints |
| Coinductive/ToInductive.lean | 172 | Coinductive → inductive conversion |
| Coinductive/WellFormed.lean | 125 | Well-formedness conditions |
| Coinductive/Roundtrip/Part1.lean | 302 | Inductive → coinductive correctness |
| Coinductive/Roundtrip/Part2.lean | 321 | Coinductive → inductive conversion |
| Coinductive/Roundtrip/Part3.lean | 200 | Roundtrip composition |
| Coinductive/Roundtrip/Part4.lean | 544 | Completeness and characterization |
| Coinductive/Roundtrip/Part5.lean | 86 | Final auxiliary lemmas |
| Coinductive/RoundtripHelpers.lean | 394 | Helper lemmas |

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
| Projection/Projectb/Part1.lean | 205 | Boolean projection definition |
| Projection/Projectb/Part2.lean | 465 | Branch handling |
| Projection/Projectb/Part3.lean | 387 | Correctness lemmas |
| Projection/Projectb/Part4.lean | 566 | Mu-type handling |

### Proof-Carrying Projection API

| File | Lines | Description |
|------|-------|-------------|
| Projection/Project/Core.lean | 123 | Core API definitions |
| Projection/Project/MuveImplBase.lean | 561 | Base mu-unfolding cases |
| Projection/Project/MuveImplParticipant.lean | 544 | Participant mu-unfolding elimination |
| Projection/Project/MuveImplNonPart.lean | 429 | Non-participant mu-unfolding elimination |
| Projection/Project/ImplBase.lean | 431 | Base projection implementation |
| Projection/Project/ImplConstructors/Part1.lean | 427 | End, var, mu cases |
| Projection/Project/ImplConstructors/Part2.lean | 366 | Send/recv cases |
| Projection/Project/ImplConstructors/Part3.lean | 192 | Branching cases |
| Projection/Project/ImplCompleteness.lean | 314 | Completeness proof |
| Projection/Project/ImplObservables.lean | 362 | Observable properties preservation |
| Projection/Project/ImplHeadPreservation.lean | 463 | Head shape preservation |
| Projection/Project/ImplExtraction/Part1.lean | 306 | Observable extraction |
| Projection/Project/ImplExtraction/Part2.lean | 330 | Payload and branch extraction |
| Projection/Project/ImplTransRelComp/Part1.lean | 331 | Transition relation base cases |
| Projection/Project/ImplTransRelComp/Part2.lean | 354 | Transition relation properties |
| Projection/Project/ImplCompPostfix/Part1.lean | 321 | Observable postfix computation |
| Projection/Project/ImplCompPostfix/Part2.lean | 219 | Observable list postfix |
| Projection/Project/ImplCompPostfix/Part3.lean | 356 | Postfix properties |
| Projection/Project/ImplU/Part1.lean | 355 | Unfolding base cases |
| Projection/Project/ImplU/Part2.lean | 363 | Unfolding lemmas and composition |

### Blindness Predicate

| File | Lines | Description |
|------|-------|-------------|
| Projection/Blind/Part1.lean | 492 | Definition and basic properties |
| Projection/Blind/Part2.lean | 187 | Preservation and composition |

### Harmony (Projection Correctness)

| File | Lines | Description |
|------|-------|-------------|
| Harmony.lean | 150 | Main harmony structure |
| Harmony/MuUnfoldLemmas.lean | 257 | Mu-unfolding auxiliary lemmas |
| Harmony/StepProjection.lean | 255 | Projection preserves stepping semantics |
| Harmony/SubstEndUnguarded.lean | 239 | Substitution with guardedness constraints |
| Harmony/Part1.lean | 423 | Main structure |
| Harmony/Part2.lean | 519 | Communication handling |
| Harmony/Part3.lean | 533 | Branching |
| Harmony/Part4.lean | 126 | Recursion |
| Harmony/Part5.lean | 147 | Final properties |

### Supporting Modules

| File | Lines | Description |
|------|-------|-------------|
| Projection/ProjSubst.lean | 410 | Projection-substitution commutation |
| Projection/ProjectProps.lean | 143 | General projection properties |
| Projection/ComposeProof.lean | 60 | Composition of projection lemmas |
| Projection/Embed.lean | 233 | Coinductive embedding relation |
| Projection/EmbedProps.lean | 510 | Embedding properties |
| Projection/Erasure/Part1.lean | 80 | Erasure definition |
| Projection/Erasure/Part2.lean | 358 | Erasure lemmas |
| Projection/Erasure/Part3.lean | 425 | Erasure correctness |
| Assumptions.lean | 15 | Centralized assumptions |

---

## Semantics

**Root Module:** `Semantics.lean`
**Description:** Operational semantics, typing judgments, determinism, deadlock freedom, subject reduction.

| File | Lines | Description |
|------|-------|-------------|
| Environment.lean | 299 | Environment configuration (message queues, timeouts, actions) |
| EnvStep.lean | 191 | Environment-step relation |
| Typing.lean | 23 | Typing judgment interface |
| Determinism/Part1.lean | 600 | Determinism proof part 1 |
| Determinism/Part2.lean | 516 | Determinism proof part 2 |
| DeadlockFreedom.lean | 293 | Deadlock freedom with fairness |
| SubjectReduction.lean | 201 | Subject reduction for well-typed processes |

---

## Protocol

**Root Module:** `Protocol.lean`
**Description:** Async buffered multiparty session types with coherence invariant, preservation, deadlock freedom, monitoring, and deployment composition.

### Foundational Types

| File | Lines | Description |
|------|-------|-------------|
| Basic.lean | 185 | SessionId, Role, Endpoint, Label, Edge, RoleSet |
| LocalType.lean | 155 | Local session types with send/recv/select/branch/mu |
| Values.lean | 191 | Runtime values, linear capability tokens, session ID bounds |
| Process.lean | 149 | Process language (skip, seq, par, send, recv, select, branch, newSession) |

### Environments

| File | Lines | Description |
|------|-------|-------------|
| Environments/Part1.lean | 938 | Store, SEnv, GEnv, DEnv, Buffers — lookup/update/init |
| Environments/Part2.lean | 493 | Session renaming with injectivity/commutativity |

### Coherence (9 parts)

Central invariant replacing traditional duality for multiparty async settings.

| File | Lines | Description |
|------|-------|-------------|
| Coherence/Part1.lean | 253 | `Consume`, `EdgeCoherent`, `Coherent`, `HasTypeVal` |
| Coherence/Part2.lean | 458 | `BufferTyped`, `StoreTyped` |
| Coherence/Part3.lean | 136 | `StoreTypedStrong`, irrelevance lemmas |
| Coherence/Part4.lean | 601 | `Coherent_send_preserved`, `Coherent_recv_preserved` |
| Coherence/Part5.lean | 356 | `Coherent_select_preserved`, `Coherent_branch_preserved` |
| Coherence/Part6.lean | 507 | Helper lemmas |
| Coherence/Part7.lean | 376 | `HeadCoherent_select/branch_preserved` |
| Coherence/Part8.lean | 661 | `Coherent_empty`, `initSession_coherent`, ValidLabels |
| Coherence/Part9.lean | 303 | `CoherentRenaming`, `Dual_implies_Coherent_empty` |

### Typing (8 parts)

| File | Lines | Description |
|------|-------|-------------|
| Typing/Part1.lean | 651 | Disjointness, splitting (`ParSplit`), `DConsistent` — 1 axiom |
| Typing/Part2.lean | 567 | `HasTypeProcN` judgment |
| Typing/Part3.lean | 992 | SEnv append/lookup lemmas |
| Typing/Part4.lean | 327 | Additional environment lemmas |
| Typing/Part5.lean | 478 | `WTConfigN` well-typed configuration |
| Typing/Part6.lean | 1,633 | Frame lemmas — 2 axioms |
| Typing/Part7.lean | 2,128 | Preservation sub-lemmas (`Compatible`) — 1 axiom |
| Typing/Part8.lean | 472 | DEnv union and environment append properties |

### Operational Semantics

| File | Lines | Description |
|------|-------|-------------|
| Semantics.lean | 358 | `StepBase` (send/recv/select/branch/newSession/assign), `Step` (contextual closure) |

### Main Theorems

| File | Lines | Description |
|------|-------|-------------|
| Preservation.lean | 192 | `preservation_typed`, `progress_*`, `subject_reduction` — 6 axioms |
| Determinism.lean | 359 | `stepBase_det`, `diamond_independent`, `session_isolation` |
| DeadlockFreedom.lean | 490 | `Guarded`, `ReachesComm`, `deadlock_free`, `not_stuck` — 7 axioms |

### Runtime Monitoring

| File | Lines | Description |
|------|-------|-------------|
| Monitor/Part1.lean | 477 | `ProtoAction`, `MonitorState`, `MonStep`, `WTMon` |
| Monitor/Part2.lean | 187 | `MonStep_preserves_WTMon`, `newSession_preserves_WTMon` — 2 axioms |

### Deployment Composition

| File | Lines | Description |
|------|-------|-------------|
| Deployment/Part1.lean | 391 | `InterfaceType`, `DeployedProtocol`, `ProtocolBundle` — 6 axioms |
| Deployment/Part2.lean | 296 | `MergeDEnv`, disjoint sessions |
| Deployment/Part3.lean | 78 | Composition metatheory — 9 axioms |

### Supporting Modules

| File | Lines | Description |
|------|-------|-------------|
| Spatial.lean | 364 | `SpatialReq`, `Topology`, `Satisfies`, `spatial_le_sound` |
| Simulation.lean | 540 | `stepDecide`, `runSteps`, `traceSteps`, soundness/completeness |
| Decidability.lean | 108 | DecidableEq instances |
| Examples.lean | 19 | Protocol examples — 1 axiom |

---

## Runtime

**Root Module:** `Runtime.lean`
**Description:** VM definition, Iris separation logic backend, resource algebras, session invariants, WP rules, and adequacy. Scaffolded per `work/iris_3.md` — shims populated, task stubs expanding incrementally.

### Iris Separation Logic Shims

Axiom shims for Iris primitives. Each retires when the corresponding upstream PR lands.

| File | Lines | Description |
|------|-------|-------------|
| Shim/ResourceAlgebra.lean | 130 | `iProp`, `GhostName`, sep logic connectives, `own`, `bupd`, `Auth`, `GMap`, `ghost_map_*`, `big_sepL/M` |
| Shim/Invariants.lean | 78 | `Mask`, `Namespace`, `fupd`, `inv`, `cinv`, `CancelToken` |
| Shim/WeakestPre.lean | 103 | `Language`/`EctxLanguage` classes, `wp`, `state_interp`, WP rules, `MultiStep`, `wp_adequacy` |
| Shim/SavedProp.lean | 33 | `saved_prop_own/alloc/agree/persistent`, `ghost_var` operations |
| Shim/GenHeap.lean | 35 | `HeapLookup/Insert`, `pointsto`, `gen_heap_alloc/valid/update` |

### VM Definition (Tasks 10–12)

| File | Lines | Description |
|------|-------|-------------|
| VM/TypeClasses.lean | 19 | Type class definitions for VM |
| VM/Definition.lean | 25 | VM machine definition |
| VM/LanguageInstance.lean | 22 | Iris `Language` instance |

### Session Resources (Tasks 13–15)

| File | Lines | Description |
|------|-------|-------------|
| Resources/SessionRA.lean | 20 | Session resource algebra |
| Resources/BufferRA.lean | 21 | Message buffer resource algebra |
| Resources/Arena.lean | 24 | Memory arena management |

### Invariants and Scheduling (Tasks 16–18)

| File | Lines | Description |
|------|-------|-------------|
| Invariants/SessionInv.lean | 25 | Session invariant properties |
| Scheduler/Scheduler.lean | 23 | Process scheduler |
| Transport/Transport.lean | 23 | Abstract transport layer |

### Program Logic (Tasks 19–21)

| File | Lines | Description |
|------|-------|-------------|
| ProgramLogic/SessionWP.lean | 25 | Session-level WP rules |
| ProgramLogic/GhostState.lean | 24 | Ghost state management |
| ProgramLogic/CodeLoading.lean | 23 | Code loading infrastructure |

### Adequacy and Monitoring (Tasks 22–24)

| File | Lines | Description |
|------|-------|-------------|
| Adequacy/Adequacy.lean | 27 | Adequacy theorem |
| Monitor/UnifiedMonitor.lean | 31 | Unified monitoring |
| Monitor/DomainComposition.lean | 26 | Domain composition for monitors |

---

## Build Configuration

### lakefile.lean

Six library targets with glob-based module discovery:

```
telltale (package)
├── SessionTypes     ← Global/local types, de Bruijn, participation
├── SessionCoTypes   ← Coinductive EQ2, bisimulation, roundtrip
├── Choreography     ← Projection, harmony, blindness, erasure
├── Semantics        ← Operational semantics, typing, determinism
├── Protocol         ← Async MPST, coherence, preservation, monitoring
└── Runtime          ← VM, Iris backend, WP, adequacy (default target)
```

**Dependencies:** mathlib, paco-lean v0.1.3

---

## Axiom Inventory

### Protocol Library (35 axioms)

| File | Count | Axioms |
|------|-------|--------|
| Preservation.lean | 6 | `preservation_typed`, `progress_send`, `progress_recv`, `progress_select`, `progress_branch`, `subject_reduction` |
| DeadlockFreedom.lean | 7 | `muDepth_subst_of_decide`, `reachesComm_unfold_mu`, `reachesComm_body_implies_unfold_aux`, `reachesComm_body_implies_unfold`, `reachesCommDecide_sound`, `deadlock_free`, `not_stuck` |
| Deployment/Part1.lean | 6 | `mkInitGEnv_lookup`, `mkInitGEnv_sessionsOf_of_mem`, `mkInitBufs_lookup_mem`, `mkInit_bConsistent`, `mkInit_bufsDom`, `mkInit_dConsistent` |
| Deployment/Part3.lean | 9 | `mergeBufs_typed`, `mergeLin_valid`, `mergeLin_unique`, `link_preserves_WTMon_full`, `link_preserves_WTMon`, `link_preserves_WTMon_complete`, `link_preserves_WTMon_complete_full`, `disjoint_sessions_independent`, `compose_deadlock_free` |
| Monitor/Part2.lean | 2 | `MonStep_preserves_WTMon`, `newSession_preserves_WTMon` |
| Typing/Part1.lean | 1 | `ParSplit.unique` |
| Typing/Part6.lean | 2 | `SessionsOf_subset_of_HasTypeProcPreOut`, `updateSEnv_append_left_any` |
| Typing/Part7.lean | 1 | `DisjointS_preserved_TypedStep_right` |
| Examples.lean | 1 | `examples_stub` |

### Runtime Library (~108 shim axioms)

All shim axioms retire when upstream Iris PRs land. See `work/iris_3.md` for retirement schedule.

| File | Count | Description |
|------|-------|-------------|
| Shim/ResourceAlgebra.lean | 39 | iProp connectives, sep logic rules, own, bupd, Auth RA, GMap, ghost_map ops, big_sep |
| Shim/Invariants.lean | 20 | Mask/Namespace ops, fupd rules, inv alloc/acc, cinv alloc/acc/cancel |
| Shim/WeakestPre.lean | 14 | wp rules (value, mono, bind, frame, fupd, lift_step), MultiStep, adequacy, invariance |
| Shim/SavedProp.lean | 8 | saved_prop (own/alloc/agree/persistent), ghost_var (alloc/agree/update) + ghost_var itself |
| Shim/GenHeap.lean | 7 | HeapLookup, HeapInsert, pointsto, gen_heap (alloc/valid/update) |

**Sorries:** 0 across all libraries.

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

### 5. Iris Axiom Shims
Runtime library axiomatizes Iris separation logic primitives to enable parallel development. Shims retire individually as upstream PRs are merged.

### 6. Linear Capability Tokens
Unforgeable tokens tied to endpoints enforce linear resource usage. The monitor validates token ownership before permitting actions.

---

## Quick Navigation Guide

**Want to understand...**

- **Session type definitions?** → SessionTypes/GlobalType/Part1.lean, LocalTypeR/Part1.lean
- **De Bruijn indices?** → SessionTypes/LocalTypeDB/Core.lean
- **Coinductive equality (EQ2)?** → SessionCoTypes/EQ2/Core.lean
- **Bisimulation?** → SessionCoTypes/Bisim/Part1.lean
- **Inductive ↔ coinductive bridge?** → SessionCoTypes/Coinductive/Roundtrip/
- **Projection algorithm?** → Choreography/Projection/Project/Core.lean, ImplBase.lean
- **Projection correctness (harmony)?** → Choreography/Harmony.lean, Harmony/Part1-5.lean
- **Operational semantics?** → Semantics/Environment.lean, Protocol/Semantics.lean
- **Coherence invariant?** → Protocol/Coherence/Part1.lean
- **Coherence preservation?** → Protocol/Coherence/Part4.lean (send/recv), Part5.lean (select/branch)
- **Type system?** → Protocol/Typing/Part2.lean (`HasTypeProcN`), Part5.lean (`WTConfigN`)
- **Type safety?** → Protocol/Preservation.lean
- **Deadlock freedom?** → Protocol/DeadlockFreedom.lean
- **Runtime monitoring?** → Protocol/Monitor/Part1.lean
- **Deployment composition?** → Protocol/Deployment/Part1-3.lean
- **Iris separation logic shims?** → Runtime/Shim/ResourceAlgebra.lean
- **Weakest preconditions?** → Runtime/Shim/WeakestPre.lean
- **What is axiomatized?** → [Axiom Inventory](#axiom-inventory)
