# Documentation Map

This page classifies docs by purpose and normative status.
Use [Start Here by Role](00_start_here.md) for onboarding paths.

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
| [Start Here by Role](00_start_here.md) | Guide | Informative |
| [Background](00_introduction.md) | Concept | Informative |
| [Getting Started](01_getting_started.md) | Guide | Informative |
| [Architecture](02_architecture.md) | Concept | Mixed |
| [Crate Organization](03_crate_organization.md) | Reference | Informative |
| [Choreographic DSL](04_choreographic_dsl.md) | Guide | Mixed |
| [Choreographic Projection Patterns](05_projection.md) | Reference | Mixed |
| [Theory](06_theory.md) | Concept | Informative |
| [DSL Extensions](07_extensions.md) | Guide | Mixed |
| [Choreography Effect Handlers](08_effect_handlers.md) | Guide | Mixed |
| [Using Telltale Handlers](09_telltale_handler.md) | Guide | Informative |
| [Effect Handlers and Session Types](10_effect_session_bridge.md) | Reference | Normative |
| [VM Architecture](11_vm_architecture.md) | Reference | Normative |
| [Bytecode Instructions](12_bytecode_instructions.md) | Reference | Normative |
| [Session Lifecycle](13_session_lifecycle.md) | Reference | Normative |
| [VM Simulation](14_vm_simulation.md) | Guide | Mixed |
| [VM Simulation Runner](14_vm_simulation_runner.md) | Reference | Normative |
| [VM Simulation Scenarios](14_vm_simulation_scenarios.md) | Guide | Mixed |
| [VM Simulation Materials](14_vm_simulation_materials.md) | Reference | Informative |
| [VM Parity](15_vm_parity.md) | Reference | Normative |
| [Content Addressing](16_content_addressing.md) | Reference | Mixed |
| [Resource Heap](17_resource_heap.md) | Reference | Mixed |
| [Lean Verification](18_lean_verification.md) | Reference | Mixed |
| [Lean-Rust Bridge](19_lean_rust_bridge.md) | Reference | Normative |
| [Topology](20_topology.md) | Guide | Mixed |
| [WASM Guide](21_wasm_guide.md) | Guide | Informative |
| [API Reference](22_api_reference.md) | Reference | Informative |
| [Examples](23_examples.md) | Guide | Informative |
| [Physical Analogies for the Telltale Runtime](24_physical_analogy.md) | Concept | Informative |
| [Capability and Admission](25_capability_admission.md) | Reference | Normative |
| [Theorem Program](26_theorem_program.md) | Concept | Mixed |
| [Distributed and Classical Families](27_distributed_classical_families.md) | Reference | Mixed |
| [Glossary and Notation Index](28_glossary_notation.md) | Reference | Informative |

## Quick Views

Guide-first readers should prioritize Guide docs, then selective Reference docs.
Integrator and verifier readers should prioritize Normative Reference docs.
Use [Glossary and Notation Index](28_glossary_notation.md) to normalize terminology across tracks.
