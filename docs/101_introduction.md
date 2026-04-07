# Introduction

[Telltale](https://github.com/hxrts/telltale) is a session-typed execution system for building protocol-critical concurrent and distributed programs. It is designed as a conservation system over protocol semantics: all semantically meaningful behavior is expressed in terms of six conserved quantities, and all other behavior is erased or reduced to those quantities. See [Conservation Framework](102_conservation_framework.md) for the full design philosophy.

The system enables writing distributed protocols from a global perspective with automatic projection to local implementations. The Lean 4 formalization provides mechanized proofs of preservation, progress, coherence, and harmony. The same choreography compiles to native and WASM targets.

Content addressing assigns cryptographic identities to protocol artifacts. Asynchronous subtyping uses SISO decomposition with orphan-free deadlock checks. Endpoint transfer semantics support ownership handoff at runtime with progress token migration.

## Core Concepts

Session types encode communication protocols as types. A type like `!String.?Int.end` sends a string, receives an integer, then closes the channel. The compiler checks that implementations follow the protocol contract.

Multiparty session types extend this to protocols with three or more participants. Global types describe the full protocol. Projection transforms global types into local types for each participant.

Choreographic programming builds on global types. A choreography describes computations and message flow from a neutral perspective. Endpoint projection generates the local implementation for each role.

## Design Philosophy

Telltale enforces conservation over six properties: evidence, authority, identity, commitment, structure, and premise. These properties are mutually constitutive. A coherent protocol state is a simultaneous assignment of all six. See [Conservation Framework](102_conservation_framework.md) for the conservation laws, erasure and reduction principles, and the closed semantic core object set.

Within that conservation framework, protocol-critical capability semantics are first class. The runtime and Lean model distinguish four capability classes: admission, ownership, evidence, and transition. This taxonomy covers protocol-critical authority, finalization, and handoff/reconfiguration semantics. It does not attempt to absorb general host application authorization.

See [Capability Model](701_capability_model.md) for the full taxonomy.

## Runtime Architecture

The execution architecture has three layers. The protocol machine is a deterministic small-step reducer that commits all protocol-visible truth. The guest runtime wraps the protocol machine with typed effect interfaces and concrete handlers. The host runtime is the surrounding application that provides time, storage, network, and process lifecycle.

Typed effect interfaces are the operational vocabulary between the protocol machine and the world. Internal handlers realize scheduling, dispatch, and replay. External handlers realize storage, network, and domain-specific integrations. See [Architecture](104_architecture.md) and [Protocol Machine Architecture](401_protocol_machine_architecture.md) for details.

The protocol machine also derives a first-class finalization subsystem from its
semantic objects. Observed reads, authoritative reads, publications,
materialization proofs, canonical handles, receipts, and semantic handoffs are
not just helpers. They are explicit replay-visible objects in the runtime and
the Lean model.

## Effect Handlers

Communication operations are algebraic effects. Sending and receiving messages are abstract operations that handlers implement concretely. Programs specify what to communicate.

Handlers determine how messages are delivered. In-memory channels serve testing scenarios. TCP connections serve deployment scenarios. The protocol logic remains unchanged across execution strategies.

## Protocol Machine

The protocol machine compiles local types to bytecode instructions. It manages scheduling, message buffers, and session lifecycle. The concurrency parameter `N` controls how many coroutines advance per round.

## Lean Verification

The Lean 4 formalization spans roughly 653 files and 133k lines in the core libraries (generated metrics in `lean/CODE_MAP.md`). It covers global types, local types, projection, and operational semantics. Deadlock-freedom claims are assumption-scoped with explicit premises for well-typedness, progress reachability, and fair scheduling.

The `telltale-bridge` crate provides JSON export and import for cross-validation between Rust and Lean. See [Lean Verification](801_lean_verification.md) for the verification pipeline.

## Document Index

| Document | Type | Status |
|---|---|---|
| [Getting Started](201_getting_started.md) | Guide | Informative |
| [Architecture](104_architecture.md) | Concept | Mixed |
| [Code Organization](105_code_organization.md) | Reference | Informative |
| [Theory](103_theory.md) | Concept | Informative |
| [Choreographic DSL](202_choreographic_dsl.md) | Guide | Mixed |
| [Choreographic Projection Patterns](203_projection.md) | Reference | Mixed |
| [DSL Extensions](204_extensions.md) | Guide | Mixed |
| [Choreography Effect Handlers](301_effect_handlers.md) | Guide | Mixed |
| [Using Telltale Handlers](302_telltale_handler.md) | Guide | Informative |
| [Effect Handlers and Session Types](303_effect_session_bridge.md) | Reference | Normative |
| [Protocol Machine Architecture](401_protocol_machine_architecture.md) | Reference | Normative |
| [Protocol-Machine Bytecode Instructions](402_bytecode_instructions.md) | Reference | Normative |
| [Session Lifecycle](403_session_lifecycle.md) | Reference | Normative |
| [Simulation Overview](501_simulation_overview.md) | Guide | Mixed |
| [Simulation Runner](502_simulation_runner.md) | Reference | Normative |
| [Simulation Scenarios](503_simulation_scenarios.md) | Guide | Mixed |
| [Simulation Fields](504_simulation_fields.md) | Reference | Informative |
| [Simulation Viewer](505_simulation_viewer.md) | Reference | Mixed |
| [Simulation Viewer Webapp](506_simulation_viewer_webapp.md) | Guide | Mixed |
| [Rust-Lean Bridge and Parity](802_rust_lean_parity.md) | Reference | Normative |
| [Content Addressing](601_content_addressing.md) | Reference | Mixed |
| [Resource Heap](602_resource_heap.md) | Reference | Mixed |
| [Topology](603_topology.md) | Guide | Mixed |
| [Lean Verification](801_lean_verification.md) | Reference | Mixed |
| [Capability Admission](702_capability_admission.md) | Reference | Normative |
| [Theorem Program](803_theorem_program.md) | Concept | Mixed |
| [Distributed and Classical Families](804_distributed_classical_families.md) | Reference | Mixed |
| [Examples](205_examples.md) | Guide | Informative |
| [WASM Guide](206_wasm_guide.md) | Guide | Informative |
| [API Reference](901_api_reference.md) | Reference | Informative |
| [Glossary and Notation Index](903_glossary_notation.md) | Reference | Informative |
| [Verification Inventory](902_verification_inventory.md) | Reference | Informative |
| [Capability Model](701_capability_model.md) | Reference | Normative |
| [Authority Language Surface](703_authority_language_surface.md) | Reference | Normative |
| [Conservation Framework](102_conservation_framework.md) | Concept | Normative |

## Paths by Role

### Library Users

Start with [Getting Started](201_getting_started.md). Then read [Choreographic DSL](202_choreographic_dsl.md). Continue with [Examples](205_examples.md) and [API Reference](901_api_reference.md).

### Protocol-Machine Integrators

Start with [Architecture](104_architecture.md). Then read [Effect Handlers and Session Types](303_effect_session_bridge.md) and [Protocol Machine Architecture](401_protocol_machine_architecture.md). Continue with [Protocol-Machine Bytecode Instructions](402_bytecode_instructions.md) and [Session Lifecycle](403_session_lifecycle.md). See [Simulation Overview](501_simulation_overview.md) for testing.

### Paper Reviewers

Start with [Conservation Framework](102_conservation_framework.md) and [Architecture](104_architecture.md). Then read [Theory](103_theory.md), [Lean Verification](801_lean_verification.md), and [Rust-Lean Bridge and Parity](802_rust_lean_parity.md). Continue with [Capability Admission](702_capability_admission.md) and [Theorem Program](803_theorem_program.md). See [Distributed and Classical Families](804_distributed_classical_families.md) and [Glossary and Notation Index](903_glossary_notation.md) for reference.

## Further Reading

For MPST theory, see [A Very Gentle Introduction to Multiparty Session Types](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf). For asynchronous subtyping, see [Precise Subtyping for Asynchronous Multiparty Sessions](http://mrg.doc.ic.ac.uk/publications/precise-subtyping-for-asynchronous-multiparty-sessions/main.pdf).

For choreographic programming, see [Introduction to Choreographies](https://www.fabriziomontesi.com/files/m13_choreographies_behaviorally.pdf). For integration with session types, see [Applied Choreographies](https://arxiv.org/pdf/2209.01886.pdf).

See [Glossary and Notation Index](903_glossary_notation.md) for shared terminology.
