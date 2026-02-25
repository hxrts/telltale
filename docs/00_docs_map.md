# Documentation Map

This page classifies docs by purpose and normative status, and provides role-based reading paths.

## Classification Model

`Guide` pages are workflow-oriented and task-oriented.
`Reference` pages define runtime or API contract surfaces.
`Concept` pages provide theory, framing, or context.

Normative status is per document.
`Normative` pages define behavior contracts.
`Informative` pages explain usage or concepts without defining contract-level guarantees.
`Mixed` pages contain both and should be read section-by-section.

## Doc Index

| Document | Type | Normative Status |
|---|---|---|
| [Background](01_introduction.md) | Concept | Informative |
| [Getting Started](02_getting_started.md) | Guide | Informative |
| [Architecture](03_architecture.md) | Concept | Mixed |
| [Crate Organization](04_crate_organization.md) | Reference | Informative |
| [Choreographic DSL](06_choreographic_dsl.md) | Guide | Mixed |
| [Choreographic Projection Patterns](07_projection.md) | Reference | Mixed |
| [Theory](05_theory.md) | Concept | Informative |
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
| [Lean Verification](23_lean_verification.md) | Reference | Mixed |
| [Lean-Rust Bridge](24_lean_rust_bridge.md) | Reference | Normative |
| [Topology](22_topology.md) | Guide | Mixed |
| [WASM Guide](29_wasm_guide.md) | Guide | Informative |
| [API Reference](30_api_reference.md) | Reference | Informative |
| [Examples](28_examples.md) | Guide | Informative |
| [Capability and Admission](25_capability_admission.md) | Reference | Normative |
| [Theorem Program](26_theorem_program.md) | Concept | Mixed |
| [Distributed and Classical Families](27_distributed_classical_families.md) | Reference | Mixed |
| [Glossary and Notation Index](31_glossary_notation.md) | Reference | Informative |

## Paths by Role

### Library User

Start with [Background](01_introduction.md), then [Getting Started](02_getting_started.md), then [Choreographic DSL](06_choreographic_dsl.md).
Continue with [Examples](28_examples.md) and [API Reference](30_api_reference.md).

### VM Integrator

Start with [Architecture](03_architecture.md), then [Effect Handlers and Session Types](11_effect_session_bridge.md), then [VM Architecture](12_vm_architecture.md).
Continue with [Bytecode Instructions](13_bytecode_instructions.md), [Session Lifecycle](14_session_lifecycle.md), and [VM Simulation](15_vm_simulation_overview.md).

### Lean and Proof Reader

Start with [Theory](05_theory.md), then [Lean Verification](23_lean_verification.md), then [Lean-Rust Bridge](24_lean_rust_bridge.md).
Continue with [Capability and Admission](25_capability_admission.md), [Theorem Program](26_theorem_program.md), and [Distributed and Classical Families](27_distributed_classical_families.md).

### Paper Reviewer

Start with [Background](01_introduction.md), [Architecture](03_architecture.md), and [Theory](05_theory.md).
Then read [Theorem Program](26_theorem_program.md) and [Glossary and Notation Index](31_glossary_notation.md).

## Reading Notes

Guide-first readers should prioritize Guide docs, then selective Reference docs.
Integrator and verifier readers should prioritize Normative Reference docs.
Use [Glossary and Notation Index](31_glossary_notation.md) to normalize terminology across tracks.
