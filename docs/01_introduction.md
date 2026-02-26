# Introduction

Telltale is a Rust framework for choreographic programming with multiparty session types. It enables writing distributed protocols from a global perspective with automatic projection to local implementations. The Lean 4 formalization provides mechanized proofs of preservation, progress, coherence, and harmony.

The framework includes a bytecode VM with deterministic scheduling and configurable buffer backpressure policies. Asynchronous subtyping uses SISO decomposition with orphan-free deadlock checks. Endpoint transfer semantics support ownership handoff at runtime with progress token migration. Content addressing assigns cryptographic identities to protocol artifacts. The same choreography compiles to native and WASM targets.

## Core Concepts

Session types encode communication protocols as types. A type like `!String.?Int.end` specifies: send a string, receive an integer, close the channel. The compiler checks that implementations follow the protocol contract.

Multiparty session types extend this to protocols with three or more participants. Global types describe the full protocol. Projection transforms global types into local types for each participant. The type system tracks dependencies between participants to prevent deadlocks.

Choreographic programming builds on global types. A choreography describes computations and message flow from a neutral perspective. Endpoint projection generates the local implementation for each role.

## Effect Handlers

Communication operations are algebraic effects. Sending and receiving messages are abstract operations that handlers implement concretely. Programs specify what to communicate. Handlers determine how: in-memory channels for testing, TCP for deployment. The protocol logic remains unchanged across execution strategies.

## Bytecode VM

The VM compiles local types to bytecode instructions. It manages scheduling, message buffers, and session lifecycle. The concurrency parameter N controls how many coroutines advance per round. Per-session traces are invariant over N.

## Lean Verification

The Lean 4 formalization spans approximately 620 files and 126,000 lines. It covers global types, local types, projection, and operational semantics. Deadlock-freedom claims are assumption-scoped with explicit premises for well-typedness, progress reachability, and fair scheduling.

The `telltale-lean-bridge` crate provides JSON export and import for cross-validation between Rust and Lean. See [Lean Verification](23_lean_verification.md) for the verification pipeline.

## Documentation Classification

Documents are classified by purpose.

| Type | Purpose |
|---|---|
| Guide | Workflow-oriented and task-oriented |
| Reference | Runtime or API contract surfaces |
| Concept | Theory, framing, or context |

Normative status indicates contract scope.

| Status | Meaning |
|---|---|
| Normative | Defines behavior contracts |
| Informative | Explains usage without guarantees |
| Mixed | Contains both; read section-by-section |

## Document Index

| Document | Type | Status |
|---|---|---|
| [Getting Started](02_getting_started.md) | Guide | Informative |
| [Architecture](03_architecture.md) | Concept | Mixed |
| [Crate Organization](04_crate_organization.md) | Reference | Informative |
| [Theory](05_theory.md) | Concept | Informative |
| [Choreographic DSL](06_choreographic_dsl.md) | Guide | Mixed |
| [Choreographic Projection Patterns](07_projection.md) | Reference | Mixed |
| [DSL Extensions](08_extensions.md) | Guide | Mixed |
| [Choreography Effect Handlers](09_effect_handlers.md) | Guide | Mixed |
| [Using Telltale Handlers](10_telltale_handler.md) | Guide | Informative |
| [Effect Handlers and Session Types](11_effect_session_bridge.md) | Reference | Normative |
| [VM Architecture](12_vm_architecture.md) | Reference | Normative |
| [Bytecode Instructions](13_bytecode_instructions.md) | Reference | Normative |
| [Session Lifecycle](14_session_lifecycle.md) | Reference | Normative |
| [VM Simulation](15_vm_simulation_overview.md) | Guide | Mixed |
| [VM Simulation Runner](16_vm_simulation_runner.md) | Reference | Normative |
| [VM Simulation Scenarios](17_vm_simulation_scenarios.md) | Guide | Mixed |
| [VM Simulation Materials](18_vm_simulation_materials.md) | Reference | Informative |
| [VM Parity](19_vm_parity.md) | Reference | Normative |
| [Content Addressing](20_content_addressing.md) | Reference | Mixed |
| [Resource Heap](21_resource_heap.md) | Reference | Mixed |
| [Topology](22_topology.md) | Guide | Mixed |
| [Lean Verification](23_lean_verification.md) | Reference | Mixed |
| [Lean-Rust Bridge](24_lean_rust_bridge.md) | Reference | Normative |
| [Capability and Admission](25_capability_admission.md) | Reference | Normative |
| [Theorem Program](26_theorem_program.md) | Concept | Mixed |
| [Distributed and Classical Families](27_distributed_classical_families.md) | Reference | Mixed |
| [Examples](28_examples.md) | Guide | Informative |
| [WASM Guide](29_wasm_guide.md) | Guide | Informative |
| [API Reference](30_api_reference.md) | Reference | Informative |
| [Glossary and Notation Index](31_glossary_notation.md) | Reference | Informative |

## Reading Paths

### Library User

Start with [Getting Started](02_getting_started.md), then [Choreographic DSL](06_choreographic_dsl.md). Continue with [Examples](28_examples.md) and [API Reference](30_api_reference.md).

### VM Integrator

Start with [Architecture](03_architecture.md), then [Effect Handlers and Session Types](11_effect_session_bridge.md), then [VM Architecture](12_vm_architecture.md). Continue with [Bytecode Instructions](13_bytecode_instructions.md), [Session Lifecycle](14_session_lifecycle.md), and [VM Simulation](15_vm_simulation_overview.md).

### Lean and Proof Reader

Start with [Theory](05_theory.md), then [Lean Verification](23_lean_verification.md), then [Lean-Rust Bridge](24_lean_rust_bridge.md). Continue with [Capability and Admission](25_capability_admission.md), [Theorem Program](26_theorem_program.md), and [Distributed and Classical Families](27_distributed_classical_families.md).

### Paper Reviewer

Start with [Architecture](03_architecture.md) and [Theory](05_theory.md). Then read [Theorem Program](26_theorem_program.md) and [Glossary and Notation Index](31_glossary_notation.md).

## Further Reading

For MPST theory, see [A Very Gentle Introduction to Multiparty Session Types](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf). For asynchronous subtyping, see [Precise Subtyping for Asynchronous Multiparty Sessions](http://mrg.doc.ic.ac.uk/publications/precise-subtyping-for-asynchronous-multiparty-sessions/main.pdf).

For choreographic programming, see [Introduction to Choreographies](https://www.fabriziomontesi.com/files/m13_choreographies_behaviorally.pdf). For integration with session types, see [Applied Choreographies](https://arxiv.org/pdf/2209.01886.pdf).

See [Glossary and Notation Index](31_glossary_notation.md) for shared terminology.
