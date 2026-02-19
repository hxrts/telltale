# Capability and Admission

This document defines the capability gates that control runtime admission and profile selection.

## Gate Layers

Admission is enforced across Lean theorem-pack surfaces and Rust runtime checks.

| Layer | Main API |
|---|---|
| Lean theorem-pack facade | `Runtime/Proofs/TheoremPack/API.lean` |
| Lean capability inventory | `Runtime/Proofs/TheoremPack/Inventory.lean` |
| Lean admission logic | `Runtime/Adequacy/EnvelopeCore/AdmissionLogic.lean` |
| Rust runtime gates | `rust/vm/src/runtime_contracts.rs` |
| Rust composition admission | `rust/vm/src/composition.rs` |

## Runtime Gate Flow

Rust runtime admission uses a fixed gate sequence.

| Step | Function | Result class |
|---|---|---|
| advanced mode check | `requires_vm_runtime_contracts` | boolean requirement |
| runtime admission | `admit_vm_runtime` | `Admitted` or `RejectedMissingContracts` |
| profile request | `request_determinism_profile` | selected profile or `None` |
| unified gate | `enforce_vm_runtime_gates` | `Admitted`, `RejectedMissingContracts`, or `RejectedUnsupportedDeterminismProfile` |

The unified gate is the admission decision used by higher-level runtime loaders.

## Determinism Profiles

Determinism profiles are validated against artifacts and capability switches.

| Profile | Rust enum | Artifact flag |
|---|---|---|
| full | `DeterminismMode::Full` | `determinism_artifacts.full` |
| modulo effect trace | `DeterminismMode::ModuloEffects` | `determinism_artifacts.modulo_effect_trace` |
| modulo commutativity | `DeterminismMode::ModuloCommutativity` | `determinism_artifacts.modulo_commutativity` |
| replay | `DeterminismMode::Replay` | `determinism_artifacts.replay` |

Non-full profiles also require `can_use_mixed_determinism_profiles`.

## Theorem-Pack Capability Inventory

The theorem-pack inventory publishes machine-readable capability keys.

| Inventory family | Example keys |
|---|---|
| protocol safety and liveness | `termination`, `output_condition_soundness` |
| distributed impossibility and safety | `flp_impossibility`, `cap_impossibility`, `quorum_geometry_safety` |
| distributed deployment families | `partial_synchrony_liveness`, `reconfiguration_safety`, `atomic_broadcast_ordering` |
| advanced envelope families | `consensus_envelope`, `failure_envelope`, `vm_envelope_adherence`, `vm_envelope_admission`, `protocol_envelope_bridge` |
| classical transport families | `classical_foster`, `classical_maxweight`, `classical_ldp`, `classical_functional_clt` |

Rust capability snapshots should align with this inventory for release and admission claims.

## Composition Admission

Composed runtime admission in `rust/vm/src/composition.rs` enforces both proof artifacts and runtime gates.

| Requirement | Failure mode |
|---|---|
| `link_ok_full` compatibility evidence | `MissingCompatibilityProof` |
| runtime contracts for advanced mode | `MissingRuntimeContracts` |
| required scheduler capability | `MissingCapability` |
| required determinism capability | `MissingCapability` |
| output-condition gating capability | `MissingCapability` |
| memory budget | `BudgetExceeded` |

This path guarantees that admitted bundles carry both semantic and operational evidence.

## Admission Diagnostics

Lean and Rust both expose structured rejection categories.

| Surface | Rejection classes |
|---|---|
| Lean admission logic | `maxDiffExceeded`, `eqSafeNotSupported`, `missingRequiredProfiles` |
| Rust runtime gate | `RejectedMissingContracts`, `RejectedUnsupportedDeterminismProfile` |
| Rust composition | typed `CompositionError` variants with capability key strings |

These categories are intended for machine-visible reporting and CI gate failures.

## Governance and CI

Admission and capability drift are controlled by repository lanes.

| Check | Script |
|---|---|
| runtime contract gate shape | `scripts/check-runtime-contract-gates.sh` |
| theorem-pack release conformance | `scripts/check-release-conformance.sh` |
| VM parity suite | `scripts/check-vm-parity-suite.sh` |
| parity ledger policy | `scripts/check-parity-ledger.sh` |

## Related Docs

- [VM Architecture](11_vm_architecture.md)
- [VM Parity](15_vm_parity.md)
- [Lean Verification](18_lean_verification.md)
- [Theorem Program](26_theorem_program.md)
