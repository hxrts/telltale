# Lean Verification

This document summarizes the current Lean implementation surface and the proof APIs consumed by runtime gates.

## Source of Truth

Verification scale and proof-hole status are tracked by generated reports.

| Source | Purpose |
|---|---|
| [Lean Verification Code Map](../lean/CODE_MAP.md) | generated library map with file counts and module inventory |
| `just escape` | machine check for axiom and sorry budget |

Current scale and proof-hole status are tracked in these generated artifacts.

## Library Layers

The Lean tree is organized as a layered stack.

| Layer | Main content |
|---|---|
| SessionTypes | global and local syntax, de Bruijn forms, conversions |
| SessionCoTypes | coinductive equality, bisimulation, decidable regular checks |
| Choreography | projection, blindness, erasure, harmony |
| Semantics | small-step semantics, determinism, deadlock surfaces |
| Protocol | coherence, typing, monitoring, deployment composition |
| Runtime | VM model, semantics, runtime adapters, theorem-pack APIs |
| Distributed | FLP, CAP, quorum, synchrony, Nakamoto, reconfiguration, safety families |
| Classical | transported queueing and stochastic theorem families |
| IrisExtraction | runtime proof extraction and ghost logic bridge |

## VM Model and Runtime Surfaces

The VM model is centered under `lean/Runtime/VM`.

| Surface | Location |
|---|---|
| Core instruction and state model | `Runtime/VM/Model/*` |
| Executable semantics | `Runtime/VM/Semantics/*` |
| Runtime adapters and monitor | `Runtime/VM/Runtime/*` |
| Composition and domain instances | `Runtime/VM/Composition/*` |

The effect model uses the current split `EffectRuntime` and `EffectSpec`. Monitor typing lives in `Runtime/VM/Runtime/Monitor.lean`.

## Proof Packs and Admission APIs

Runtime proof inventory is exported through theorem-pack modules.

| Surface | Purpose |
|---|---|
| `Runtime/Proofs/TheoremPack/API.lean` | public theorem-pack facade and runtime gate aliases |
| `Runtime/Proofs/TheoremPack/Inventory.lean` | capability inventory keys and determinism extension |
| `Runtime/Proofs/TheoremPack/ReleaseConformance.lean` | release gate and replay conformance report |
| `Runtime/Adequacy/EnvelopeCore/AdmissionLogic.lean` | admission soundness, completeness, diagnostics vocabulary |

These APIs are consumed by Rust runtime gates and composition admission checks.

## Premise-Scoped Interfaces

Some surfaces are intentionally premise-scoped.

| Interface class | Example |
|---|---|
| Threaded refinement beyond `n = 1` | `ThreadedRoundRefinementPremises` |
| Envelope admission and profile diagnostics | admission protocol structures in `AdmissionLogic.lean` |
| Mixed-profile runtime gates | theorem-pack and runtime-contract capability checks |

These are explicit interfaces and not unconditional global theorems.

## Distributed and Classical Reach

Distributed and classical families are part of the active theorem-pack space. They are not side notes.

Distributed families include FLP, CAP, quorum geometry, partial synchrony, responsiveness, Nakamoto security, reconfiguration, atomic broadcast, accountable safety, failure detectors, data availability, coordination, CRDT, Byzantine safety, consensus envelope, and failure envelope.

Classical transport families include Foster-Lyapunov, MaxWeight, large deviations, mean-field, heavy-traffic, mixing, fluid limits, concentration bounds, Little's law, and functional CLT.

## Runtime Alignment Lanes

Lean and Rust alignment is checked by automation lanes.

| Lane | Command |
|---|---|
| Runtime capability gates | `just check-capability-gates` |
| Release conformance | `just check-release-conformance` |
| VM parity suite | `just check-parity --suite` |
| Type and schema parity | `just check-parity --types` |
| Consolidated parity lane | `just check-parity --all` |

## Related Docs

- [VM Architecture](12_vm_architecture.md)
- [VM Parity](19_vm_parity.md)
- [Lean-Rust Bridge](24_lean_rust_bridge.md)
- [Capability and Admission](25_capability_admission.md)
- [Distributed and Classical Families](27_distributed_classical_families.md)
