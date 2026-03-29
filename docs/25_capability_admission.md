# Capability and Admission

This document defines the capability gates that control runtime admission and profile selection.

Admission is not the same thing as current ownership.
Admission answers whether a runtime/profile/configuration is allowed in principle.
Ownership answers who may currently drive session-local host mutation for one live session or fragment.

## Gate Layers

Admission is enforced across Lean theorem-pack surfaces and Rust runtime checks.

| Layer | Main API |
|---|---|
| Lean theorem-pack facade | `Runtime/Proofs/TheoremPack/API.lean` |
| Lean capability inventory | `Runtime/Proofs/TheoremPack/Inventory.lean` |
| Lean admission logic | `Runtime/Adequacy/EnvelopeCore/AdmissionLogic.lean` |
| Rust runtime gates | `rust/machine/src/runtime_contracts.rs` |
| Rust composition admission | `rust/machine/src/composition.rs` |

## Runtime Gate Flow

Rust runtime admission uses a fixed gate sequence.

| Step | Function | Result class |
|---|---|---|
| advanced mode check | `requires_protocol_machine_runtime_contracts` | boolean requirement |
| runtime admission | `admit_protocol_machine_runtime` | `Admitted` or `RejectedMissingContracts` |
| profile request | `request_determinism_profile` | selected profile or `None` |
| unified gate | `enforce_protocol_machine_runtime_gates` | `Admitted`, `RejectedMissingContracts`, or `RejectedUnsupportedDeterminismProfile` |

The unified gate is the admission decision used by higher-level runtime loaders.

## Admission vs Ownership

These concepts are intentionally separate.

| Question | Admission answers | Ownership answers |
|---|---|---|
| can this runtime mode/profile be used? | yes | no |
| does this theorem-pack/runtime-contract inventory admit the feature? | yes | no |
| may this caller mutate session-local host state right now? | no | yes |
| does this caller hold current fragment/session authority? | no | yes |

Practical consequence:

- passing `enforce_protocol_machine_runtime_gates(...)` does not authorize session-local mutation
- hosts still need a live ownership capability such as `OwnedSession`
- stale-owner rejection can occur even when admission remains valid
- a choreography `uses Runtime, Audit` declaration states external protocol
  dependencies. It does not replace runtime admission or ownership checks

## Effect Interfaces vs Admission

Language-level effect interfaces and runtime admission solve different problems.

| Surface | Main question |
|---|---|
| `effect` declaration | what typed host operation does the protocol depend on? |
| `uses` clause | which named external interfaces may this protocol call? |
| admission gate | may this runtime/profile/configuration run at all? |
| ownership capability | who may currently drive one live session or fragment? |

Nominal effect interfaces therefore narrow protocol dependencies without
weakening theorem-pack admission or ownership enforcement.

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
| advanced envelope families | `consensus_envelope`, `failure_envelope`, `protocol_machine_envelope_adherence`, `protocol_machine_envelope_admission`, `protocol_envelope_bridge` |
| classical transport families | `classical_foster`, `classical_maxweight`, `classical_ldp`, `classical_functional_clt` |

Rust capability snapshots should align with this inventory for release and admission claims.

## Transported Theorem Boundary

Not every transported theorem family influences shipped runtime admission.
Telltale now tracks that boundary explicitly in Lean and Rust.

| Usage class | Meaning | Current examples |
|---|---|---|
| `runtime_critical_instantiated_premise` | materially influences a shipped runtime gate/guarantee surface | `protocol_machine_envelope_adherence`, `protocol_machine_envelope_admission`, `protocol_envelope_bridge` |
| `black_box_premise_only` | used by verifier/reporting surfaces, but not consumed directly by shipped Rust runtime admission | `flp_impossibility`, `quorum_geometry_safety`, `failure_envelope` |
| `documentation_background_only` | carried for theorem-program inventory/docs only | `classical_foster`, `classical_functional_clt` |

The canonical ledger lives in:

- `lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean`
- `rust/machine/src/runtime_contracts.rs`

One runtime-critical theorem family is intentionally marked as a boundary rather
than a shipped Rust admission dependency today:

- `byzantine_safety_characterization` is consumed by a Lean theorem-pack gate
  alias, but Rust runtime admission does not currently use it. That gap is now
  explicit rather than implicit.

### Source-Derived Rows

The following rows are source-derived and checked against
`telltale_machine::transported_theorem_boundary()` by
`rust/tests/docs_contract_tests.rs`.

| Key | Usage class | Rust runtime admission | Lean runtime gate | Assumption boundary |
|---|---|---|---|---|
| `byzantine_safety_characterization` | `runtime_critical_instantiated_premise` | no | yes | Lean theorem-pack gate only. Rust runtime admission does not currently consume this key. |
| `protocol_machine_envelope_adherence` | `runtime_critical_instantiated_premise` | yes | yes | `none` |
| `protocol_machine_envelope_admission` | `runtime_critical_instantiated_premise` | yes | yes | `none` |
| `protocol_envelope_bridge` | `runtime_critical_instantiated_premise` | yes | yes | `none` |

## Composition Admission

Composed runtime admission in `rust/machine/src/composition.rs` enforces both proof artifacts and runtime gates.

| Requirement | Failure mode |
|---|---|
| `link_ok_full` compatibility evidence | `MissingCompatibilityProof` |
| runtime contracts for advanced mode | `MissingRuntimeContracts` |
| required scheduler capability | `MissingCapability` |
| required determinism capability | `MissingCapability` |
| output-condition gating capability | `MissingCapability` |
| memory budget | `BudgetExceeded` |

This path guarantees that admitted bundles carry both semantic and operational evidence.

When composition metadata defines fragment or bundle boundaries, runtime ownership should derive from that metadata rather than from ad hoc host-side reconstruction. Admission decides whether the bundle may run. Ownership decides who may currently drive it.

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

| Check | Command |
|---|---|
| runtime capability gate shape | `just check-capability-gates` |
| theorem-pack release conformance | `just check-release-conformance` |
| Protocol-machine parity suite | `just check-parity --suite` |
| parity type and schema policy | `just check-parity --types` |
| consolidated parity policy | `just check-parity --all` |

## Related Docs

- [Protocol Machine Architecture](12_protocol_machine_architecture.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
- [Lean Verification](23_lean_verification.md)
- [Theorem Program](26_theorem_program.md)
