# Lean Verification Code Map

**Last Updated:** 2026-02-06

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
**Dependencies:** mathlib, paco-lean v0.1.3, iris-lean

| Library        | Files | Lines   | Focus                                                      |
|----------------|------:|--------:|------------------------------------------------------------|
| SessionTypes   |    30 |  ~8,253 | Global/local type definitions, de Bruijn, participation    |
| SessionCoTypes |    63 | ~14,058 | Coinductive EQ2, bisimulation, duality, roundtrip bridge   |
| Choreography   |    69 | ~16,251 | Projection, harmony, blindness, embedding, erasure         |
| Semantics      |     8 |  ~2,171 | Operational semantics, determinism, deadlock freedom       |
| Protocol       |    49 | ~24,094 | Async buffered MPST, coherence, preservation, monitoring   |
| Runtime        |    68 | ~10,542 | VM, Iris backend via iris-lean, resource algebras, WP      |
| **Total**      | **287** | **~75,369** |                                                      |

**Architectural Layers:**
```
Layer 6: Runtime          → VM, iris-lean backend, resource algebras, WP, adequacy
Layer 5: Protocol         → Async MPST, coherence, typing, preservation, monitoring, deployment
Layer 4: Semantics        → Operational semantics, typing judgments, determinism, deadlock freedom
Layer 3: Choreography     → Projection, harmony, blindness, embedding, erasure
Layer 2: SessionCoTypes   → Coinductive EQ2, bisimulation, duality, roundtrip bridge
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
|------|------:|-------------|
| Environments/Core.lean | 938 | Store, SEnv, GEnv, DEnv, Buffers — lookup/update/init |
| Environments/Renaming.lean | 493 | Session renaming with injectivity/commutativity |
| Environments/RoleRenaming.lean | 83 | Role-based session renaming with correctness properties |

### Coherence (14 parts)

Central invariant replacing traditional duality for multiparty async settings.

| File | Lines | Description |
|------|------:|-------------|
| Coherence/Consume.lean | 253 | `Consume`, `EdgeCoherent`, `Coherent`, `HasTypeVal` |
| Coherence/EdgeCoherence.lean | 492 | `BufferTyped`, `StoreTyped`, `ActiveEdge` |
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
| Coherence/SubtypeReplacement.lean | 438 | `RecvCompatible`, `Consume_mono`, `Coherent_type_replacement`, liveness preservation |

### Typing (8 parts)

| File | Lines | Description |
|------|-------|-------------|
| Typing/Core.lean | 651 | Disjointness, splitting (`ParSplit`), `DConsistent` — 1 axiom |
| Typing/Judgments.lean | 567 | `HasTypeProcN` judgment |
| Typing/Compatibility.lean | 992 | SEnv append/lookup lemmas |
| Typing/MergeLemmas.lean | 327 | Additional environment lemmas |
| Typing/StepLemmas.lean | 478 | `WTConfigN` well-typed configuration |
| Typing/Framing.lean | 1,228 | Frame lemmas — 1 axiom |
| Typing/Preservation.lean | 2,137 | Preservation sub-lemmas (`Compatible`) — 1 axiom |
| Typing/Progress.lean | 472 | DEnv union and environment append properties |

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
| Spatial.lean | 364 | `SpatialReq`, `Topology`, `Satisfies`, `spatial_le_sound` |
| Simulation.lean | 540 | `stepDecide`, `runSteps`, `traceSteps`, soundness/completeness |
| Decidability.lean | 108 | DecidableEq instances |
| Examples.lean | 19 | Protocol examples (stubbed) |
| CrashTolerance.lean | 225 | `CommGraph`, `CrashTolerant`, `Critical`, crash tolerance predicates |
| Noninterference.lean | 264 | `CEquiv`, `BlindTo`, noninterference security properties |
| DeliveryModel.lean | 214 | `DeliveryModel` typeclass, FIFO/causal/lossy instances |
| CoherenceM.lean | 15 | Model-parametric coherence re-export wrapper |
| InformationCost.lean | 1050 | `ProjectionMap`, entropy, mutual information, blind projection |

---

## Runtime

**Root Module:** `Runtime.lean`
**Description:** VM definition, Iris separation logic backend via iris-lean, resource algebras, session invariants, WP rules, and adequacy.

### Iris Bridge (iris-lean integration)

Consolidated interface to iris-lean separation logic. **0 sorry** — ghost maps use `Positive` keys with encoding.

| File | Lines | Description |
|------|------:|-------------|
| IrisBridge.lean | 398 | `TelltaleIris` typeclass, iProp, sep logic connectives, ghost_map/ghost_var, invariants, WP rules |

### Compat Layer

Thin adapters that re-export IrisBridge definitions for downstream modules.

| File | Lines | Description |
|------|------:|-------------|
| Compat.lean | 13 | Single import point for all Iris compat modules |
| Compat/RA.lean | 10 | Resource algebra compat |
| Compat/Inv.lean | 10 | Invariant compat |
| Compat/WP.lean | 10 | Weakest precondition compat |
| Compat/SavedProp.lean | 10 | Saved proposition compat |
| Compat/GenHeap.lean | 10 | Generalized heap compat |

### VM Core

| File | Lines | Description |
|------|-------|-------------|
| VM/TypeClasses.lean | 247 | Identity, guard, persistence, effect, verification model typeclasses |
| VM/Core.lean | 66 | Register file, instruction set, coroutine |
| VM/Config.lean | 74 | VMConfig, VMState, ResourcePool |
| VM/State.lean | 207 | Full machine state, session table, buffer management |
| VM/Program.lean | 108 | Program representation and code segments |
| VM/Definition.lean | 14 | Re-export wrapper for VM.State and VM.Exec |
| VM/InstrSpec.lean | ~330 | Denotational specs for instructions (SendSpec, RecvSpec, etc.) |
| VM/Knowledge.lean | 30 | Knowledge base and fact management |
| VM/Violation.lean | 29 | Violation policy and fault types |
| VM/SchedulerTypes.lean | 28 | Scheduler type definitions |
| VM/UnitModel.lean | 181 | Minimal computable instances for all VM domain typeclasses |

### VM Execution

| File | Lines | Description |
|------|-------|-------------|
| VM/Exec.lean | 89 | Top-level step function dispatch |
| VM/ExecHelpers.lean | 421 | Register operations, buffer lookup, shared helpers |
| VM/ExecComm.lean | 449 | Send/recv/select/branch execution |
| VM/ExecSession.lean | 304 | Session open/close/fork/join |
| VM/ExecOwnership.lean | 157 | Ownership transfer and capability operations |
| VM/ExecControl.lean | 103 | Control flow (jump, call, return, halt) |
| VM/ExecGuardEffect.lean | 111 | Guard chain evaluation and effect dispatch |
| VM/ExecSpeculation.lean | 66 | Speculative execution (fork/join/abort) |
| VM/ExecSteps.lean | 54 | Multi-step execution wrapper |
| VM/CompileLocalTypeR.lean | 150 | Compiler from LocalTypeR to VM bytecode instructions |

### VM Loading and Scheduling

| File | Lines | Description |
|------|-------|-------------|
| VM/LoadChoreography.lean | 140 | Dynamic choreography loading into running VM state |
| VM/RunScheduled.lean | 104 | N-concurrent scheduler-driven execution loop |
| VM/Json.lean | 145 | JSON serialization for runtime values and trace events |

### Resources

| File | Lines | Description |
|------|-------|-------------|
| Resources/ResourceModel.lean | 179 | Resource model interface and profiles |
| Resources/SessionRA.lean | 44 | Session resource algebra |
| Resources/BufferRA.lean | 317 | Message buffer resource algebra with auth/frag |
| Resources/Arena.lean | 260 | Memory arena with pointsto and allocation |
| Resources/ProfilesV1.lean | 42 | V1 resource profile definitions |

### Program Logic

| File | Lines | Description |
|------|-------|-------------|
| ProgramLogic/LanguageInstance.lean | 93 | Iris `Language`/`EctxLanguage` instances |
| ProgramLogic/SessionWP.lean | 122 | Session-level WP rules |
| ProgramLogic/GhostState.lean | 247 | Ghost state management (session maps, buffer maps) |
| ProgramLogic/CodeLoading.lean | 99 | Code loading and program verification |
| ProgramLogic/ProofInterfaces.lean | 91 | Proof interface typeclasses |
| ProgramLogic/WPPair.lean | 131 | WP pairing for send/recv duality |
| ProgramLogic/WPPipeline.lean | 25 | WP pipeline composition |
| ProgramLogic/FinalizationWP.lean | 39 | Finalization and cleanup WP rules |

### Invariants, Scheduling, Transport

| File | Lines | Description |
|------|-------|-------------|
| Invariants/SessionInv.lean | 215 | Session invariant: coherence, buffers, endpoint state |
| VM/Scheduler.lean | 240 | Process scheduler with fairness and priority |
| Transport/Transport.lean | 232 | Abstract transport layer with handler specs |
| Cost/Credits.lean | 56 | Cost credit resource algebra |

### Domain Composition and Monitoring

| File | Lines | Description |
|------|-------|-------------|
| VM/DomainComposition.lean | 326 | Domain-specific composition and guard chain |
| VM/Monitor.lean | 123 | SessionKind, WellTypedInstr judgment, unified session monitor |
| VM/Failure.lean | 235 | Failure modes (crash, partition, heal), FStep relation, recovery predicates |

### Adequacy and Proofs

| File | Lines | Description |
|------|------:|-------------|
| Adequacy/Adequacy.lean | 145 | Adequacy theorem connecting WP to execution |
| Proofs/TheoremStubs.lean | 294 | Top-level theorem statements |
| Proofs/Concurrency.lean | 109 | Iris-backed N-invariance and policy-invariance proofs |
| Proofs/CompileLocalTypeRCorrectness.lean | 53 | Compiler correctness stubs (nonempty, ends with halt/jmp) |
| Proofs/SessionLocal.lean | 278 | `SessionSlice`, `SessionCoherent`, session-local frame infrastructure |
| Proofs/Frame.lean | 128 | `session_local_op_preserves_other`, `disjoint_ops_preserve_unrelated` |
| Proofs/Delegation.lean | 482 | `DelegationStep`, `DelegationWF`, role-renaming Consume lemmas |
| Proofs/Progress.lean | ~315 | `CoherentVMState`, `ProgressVMState`, `vm_progress`, instruction enablement |
| Proofs/Lyapunov.lean | 381 | `progressMeasure`, weighted measure W = 2·depth + buffer |
| Proofs/Diamond/Lemmas.lean | 364 | Cross-session diamond lemmas |
| Proofs/Diamond/Proof.lean | 816 | Main diamond theorem proof |

### Examples and Tests

| File | Lines | Description |
|------|-------|-------------|
| Examples/SimpleProtocol.lean | 301 | Simple two-party protocol example |
| Examples/Aura.lean | 133 | Aura instantiation example |
| Tests/Main.lean | 54 | Runtime test harness |
| Tests/VMRunner.lean | 116 | JSON-driven VM runner (stdin choreographies, stdout traces) |

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

**Dependencies:** mathlib, paco-lean v0.1.3, iris-lean

---

## Axiom Inventory

### Protocol Library (9 axioms)

| File | Count | Axioms |
|------|------:|--------|
| Deployment/Linking.lean | 6 | `mergeBufs_typed`, `link_preserves_WTMon` (4 variants), `compose_deadlock_free` |
| Monitor/Preservation.lean | 2 | `MonStep_preserves_WTMon`, `newSession_preserves_WTMon` |
| Typing/Core.lean | 1 | `ParSplit.unique` |

**Retired this cycle:** `mergeLin_valid`, `mergeLin_unique`, `SessionsOf_subset`, `DisjointS_preserved`

### Runtime Library (IrisBridge — 0 sorry)

**IrisBridge.lean now connects to iris-lean directly.** Ghost maps use `Positive` keys with application-level encoding via `Iris.Countable.encode`. The `GhostMapSlot V` typeclass registers value types.

| Category | Status | Description |
|----------|:------:|-------------|
| Sep logic connectives | Done | `iProp.sep`, `iProp.wand`, `iProp.pure`, etc. via iris-lean |
| Ghost variables | Done | `ghost_var`, `ghost_var_alloc`, `ghost_var_agree`, `ghost_var_update` |
| Ghost maps | Done | `ghost_map_auth`, `ghost_map_elem`, `ghost_map_alloc`, `ghost_map_lookup`, `ghost_map_insert`, `ghost_map_update`, `ghost_map_delete` |
| Invariants | Done | `inv`, `fupd`, `Mask`, `Namespace` via iris-lean |
| Saved props | Done | `saved_prop_own`, `saved_prop_alloc`, `saved_prop_agree` |

**Remaining downstream work:** polymorphic CMRA for `own`, Language instance for WP/adequacy, cancelable invariants need `CinvR` instance.

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
- **Projection algorithm?** → Choreography/Projection/Project/Core.lean, ImplBase.lean
- **Projection correctness (harmony)?** → Choreography/Harmony.lean, Harmony/StepHarmony.lean
- **Operational semantics?** → Semantics/Environment.lean, Protocol/Semantics.lean
- **Coherence invariant?** → Protocol/Coherence/Consume.lean, Protocol/Coherence/EdgeCoherence.lean
- **Coherence preservation?** → Protocol/Coherence/Preservation.lean, Protocol/Coherence/SelectPreservation.lean
- **Subtype replacement preservation?** → Protocol/Coherence/SubtypeReplacement.lean
- **Configuration equivalence (quotient)?** → Protocol/Coherence/ConfigEquiv.lean
- **Unified preservation skeleton?** → Protocol/Coherence/Unified.lean
- **Type system?** → Protocol/Typing/Judgments.lean (`HasTypeProcN`, `WTConfigN`)
- **Type safety?** → Protocol/Preservation.lean
- **Deadlock freedom?** → Protocol/DeadlockFreedom.lean
- **Runtime monitoring?** → Protocol/Monitor/Core.lean
- **Deployment composition?** → Protocol/Deployment/Interface.lean, Protocol/Deployment/Linking.lean
- **Crash tolerance?** → Protocol/CrashTolerance.lean
- **Noninterference?** → Protocol/Noninterference.lean
- **Delivery models?** → Protocol/DeliveryModel.lean
- **Iris separation logic (iris-lean)?** → Runtime/IrisBridge.lean
- **Ghost state?** → Runtime/ProgramLogic/GhostState.lean
- **Session-local proofs?** → Runtime/Proofs/SessionLocal.lean, Runtime/Proofs/Frame.lean
- **Delegation proofs?** → Runtime/Proofs/Delegation.lean
- **VM-level progress theorem?** → Runtime/Proofs/Progress.lean
- **Lyapunov measure?** → Runtime/Proofs/Lyapunov.lean
- **VM bytecode compiler?** → Runtime/VM/CompileLocalTypeR.lean
- **Dynamic choreography loading?** → Runtime/VM/LoadChoreography.lean
- **N-concurrent scheduling?** → Runtime/VM/RunScheduled.lean, Runtime/Proofs/Concurrency.lean
- **VM failure model?** → Runtime/VM/Failure.lean
- **VM JSON runner?** → Runtime/Tests/VMRunner.lean
- **What is axiomatized?** → [Axiom Inventory](#axiom-inventory)
