# Lean-Rust Bridge

The `telltale-lean-bridge` crate is the typed boundary between Rust artifacts and Lean validation entrypoints.
It handles JSON conversion, schema versioning, runner invocation, trace comparison, and typed invariant bundle export.

The bridge does not define protocol-machine semantics.
Semantics remain in `telltale-vm`, `telltale-theory`, and Lean runtime modules.
The canonical public bridge surface uses `ProtocolMachineRunner`, `ProtocolMachineRunInput`, `ProtocolMachineRunOutput`, `ProtocolMachineSemanticObjects`, and the `protocol_machine_runner` / `protocol_machine_trace` modules.
No public `vm_runner` or `vm_trace` compatibility modules remain.

Bridge payloads describe guest-runtime and protocol-machine artifacts.
Host-runtime handlers remain outside the bridge and re-enter through typed effect surfaces.

On the Lean side, semantic-object modules live under `Runtime/VM/Model/SemanticObjects/`.

| Module | Content |
|---|---|
| `Core.lean`, `Invariants.lean` | Identity, ownership, observed-read discipline predicates |
| `OutstandingEffects.lean`, `OutstandingEffectsLemmas.lean` | Deferred-effect admissibility and stale late-result rejection |
| `SemanticHandoffTransition.lean`, `SemanticHandoffLemmas.lean` | Semantic handoff activation, delegation bridge |
| `AuthoritativeReadsPublication.lean`, `AuthoritativeReadsPublicationLemmas.lean` | Authoritative-read commitment, publication projection |
| `MaterializationSuccess.lean`, `MaterializationSuccessLemmas.lean` | Materialization-proof adequacy, canonical-handle adequacy |
| `ProgressContracts.lean`, `ProgressContractsLemmas.lean` | Progress-contract semantics and escalation lemmas |
| `TransformationLocalObligations.lean`, `TransformationLocalObligationsLemmas.lean` | Transformation-local obligation bundles |
| `ReplayFailureExactness.lean`, `ReplayFailureExactnessLemmas.lean` | Replay-failure exactness |
| `CrossTargetProgressDependentWork.lean`, `CrossTargetProgressDependentWorkLemmas.lean` | Cross-target progress and dependent work |

Semantic-object theorem families attach to theorem-pack proof spaces through `Runtime/Proofs/InvariantSpace.lean` via `SemanticObjectWitnessBundle`.
Canonical inventory and contract surfaces for those attachment points live in `Runtime/Proofs/TheoremPack/API.lean`, `Runtime/Proofs/TheoremPack/Inventory.lean`, and `Runtime/Proofs/Contracts/RuntimeContracts.lean`.

## Scope

This document covers runtime bridge behavior implemented in `rust/lean-bridge/src`.
It covers `export`, `import`, `schema`, `runner`, `protocol_machine_runner`,
`sim_reference`, `semantic_objects`, `protocol_machine_trace`, `invariants`,
`equivalence`, and `validate`.

This document also covers bridge CLIs and bridge test lanes in `rust/lean-bridge/tests`.
It does not restate theorem internals from Lean proof files.

## Crate Features and Binaries

The crate has feature-gated modules and binaries.
The default feature set enables Lean runner integration.

```toml
[features]
default = ["runner"]
cli = ["clap"]
runner = ["telltale-theory"]
exporter = ["telltale-choreography", "anyhow", "bpaf"]
golden = ["clap", "anyhow", "runner"]

[[bin]]
name = "lean-bridge"
required-features = ["cli"]

[[bin]]
name = "lean-bridge-exporter"
required-features = ["exporter"]

[[bin]]
name = "golden"
required-features = ["golden"]
```

`runner` controls `LeanRunner`, `ProtocolMachineRunner`, and equivalence modules.
Without `runner`, conversion and schema modules remain available.

## Conversion Layer

`export::global_to_json()` and `export::local_to_json()` map Rust protocol types into Lean-compatible JSON.
`import::json_to_global()` and `import::json_to_local()` parse those JSON forms back into `GlobalType` and `LocalTypeR`.

The bridge uses a stable shape for recursive and branch nodes.
Kinds are `end`, `comm`, `rec`, and `var` for global types.
Kinds are `end`, `send`, `recv`, `rec`, and `var` for local types.

```json
{
  "kind": "comm",
  "sender": "A",
  "receiver": "B",
  "branches": [
    {
      "label": { "name": "msg", "sort": "unit" },
      "continuation": { "kind": "end" }
    }
  ]
}
```

Branch labels carry payload sort metadata through the `label.sort` field.
Local branch `ValType` slots in `LocalTypeR` are currently not emitted as separate bridge fields.

## Schema Families

The bridge defines three schema families.
Each family has an explicit version constant.

| Family | Version Constant | Value | Primary Payloads |
|---|---|---|---|
| Lean bridge core | `LEAN_BRIDGE_SCHEMA_VERSION` | `lean_bridge.v1` | `ProtocolMachineRunInput`, `ProtocolMachineRunOutput`, `SimRunInput`, `SimRunOutput`, replay bundles |
| Protocol bundles | `PROTOCOL_BUNDLE_SCHEMA_VERSION` | `protocol_bundle.v1` | `ProtocolBundle` |
| Protocol-machine semantic objects | `SEMANTIC_OBJECTS_SCHEMA_VERSION` | `protocol_machine.semantic_objects.v1` | `ProtocolMachineSemanticObjects` export payloads |

`schema::ensure_supported_schema_version()` rejects unsupported `lean_bridge` versions.
Protocol-machine semantic objects now use one canonical schema family with no
legacy VM-state compatibility aliases.
Protocol-machine parity artifacts use the same string-based scheme: `vm.serialization.v1` and `vm.envelope_diff.v1`.
Unsupported or missing schema versions are rejected rather than normalized.

## Reference Simulation Payloads

`sim_reference` defines typed payloads for Lean-side simulator reference runs.
These payloads are exported at crate root when the `runner` feature is enabled.

```rust
pub struct SimRunInput {
    pub schema_version: String,
    pub scenario: Value,
    pub global_type: Value,
    pub local_types: BTreeMap<String, Value>,
    pub initial_states: BTreeMap<String, Vec<Value>>,
}

pub struct SimRunOutput {
    pub schema_version: String,
    pub trace: Vec<ProtocolMachineTraceEvent>,
    pub violations: Vec<Value>,
    pub artifacts: Value,
}

pub struct SimTraceValidation {
    pub valid: bool,
    pub errors: Vec<SimulationStructuredError>,
    pub artifacts: Value,
}
```

`SimRunInput` and `SimRunOutput` require `schema_version = "lean_bridge.v1"` during deserialization.

## Lean Runner

`LeanRunner` invokes the Lean validator binary at `lean/.lake/build/bin/telltale_validator`.
Path discovery walks upward from `CARGO_MANIFEST_DIR` and looks for a workspace root containing `lean/.lake`.

`LeanRunner::validate()` writes choreography and program JSON into temp files, runs the binary, and parses JSON log output when available.
The parsed result is `LeanValidationResult { success, role, message, raw_output }`.

Projection methods call validator export modes.
`project()` runs `--export-all-projections` and accepts both object and array projection formats from Lean output.
`export_projection()` and `export_all_projections()` expose single-role and all-role export modes directly.
`run_protocol_machine()` is also exposed on `LeanRunner` and forwards protocol-machine choreographies to the Lean protocol-machine runner binary through stdin JSON.

## Lean Protocol-Machine Runner Wrapper

`ProtocolMachineRunner` wraps the Lean protocol-machine binary at `lean/.lake/build/bin/vm_runner`.
It serializes `ProtocolMachineRunInput` to process stdin and parses `ProtocolMachineRunOutput` from stdout.

```rust
pub struct ProtocolMachineRunInput {
    pub schema_version: String,
    pub choreographies: Vec<ChoreographyJson>,
    pub concurrency: u64,
    pub max_steps: u64,
}

pub struct ProtocolMachineRunOutput {
    pub schema_version: String,
    pub trace: Vec<ProtocolMachineTraceEvent>,
    pub sessions: Vec<ProtocolMachineSessionStatus>,
    pub steps_executed: u64,
    pub concurrency: u64,
    pub status: String,
    pub effect_trace: Vec<EffectTraceEvent>,
    pub effect_exchanges: Vec<EffectExchangeRecord>,
    pub output_condition_trace: Vec<OutputConditionTraceEvent>,
    pub step_states: Vec<ProtocolMachineStepState>,
    pub semantic_objects: ProtocolMachineSemanticObjects,
}
```

`ProtocolMachineRunner::run()` enforces schema compatibility checks on both input and output.
It returns structured `ProtocolMachineRunnerError` values for binary lookup, process failure, IO, and parse failures.

`validate_trace()` invokes Lean operation `validateTrace`.
`run_reference_simulation()` invokes Lean operation `runSimulation`.
`validate_simulation_trace()` invokes Lean operation `validateSimulationTrace`.
`verify_invariants()` invokes Lean operation `verifyProtocolBundle`.
`compare_execution()` runs the same choreography in Lean and compares normalized traces.

`run_reference_simulation()` decodes `SimRunOutput` and enforces schema checks on response payloads.
`validate_simulation_trace()` returns typed `SimTraceValidation` values with structured `SimulationStructuredError` entries.

## Protocol-Machine Semantic Object Export Surface

`semantic_objects` provides the canonical bridge payloads for the protocol
machine’s semantic object family.

`ProtocolMachineSemanticObjects` carries:

- `OperationInstance`
- `OutstandingEffect`
- `SemanticHandoff`
- `TransformationObligation`
- `AuthoritativeRead`
- `ObservedRead`
- `MaterializationProof`
- `CanonicalHandle`
- `PublicationEvent`
- `ProgressContract`
- `ProgressTransition`

`semantic_objects_to_json()` and `semantic_objects_from_json()` encode and
decode the canonical schema directly. The bridge no longer treats generic
VM-state export as its primary cross-language contract.

`ProtocolMachineRunOutput.semantic_objects` carries the same canonical runtime
state used by replay export: live `OperationInstance` and `OutstandingEffect`
objects plus the derived handoff/obligation/read/proof/publication/progress
surfaces.

`ProtocolMachineRunOutput.effect_exchanges` is the canonical bridge-side export
for the typed effect boundary. It carries `EffectRequest`, `EffectOutcome`, and
the validated runtime metadata for each exchange.

Authoritative-read/materialization/publication parity now flows through the same
semantic-object payload:

- observational reads remain in `observed_reads`
- semantic-path evidence remains in `authoritative_reads`
- proof-bearing success remains in `materialization_proofs`
- strong follow-on handles remain in `canonical_handles`
- canonical publication remains in `publication_events`
- bounded waits, no-progress/degraded state, and timeout escalation remain in
  `progress_contracts` / `progress_transitions`

`compare_execution()` now reports handoff and invalidation agreement alongside
trace equivalence. In addition to normalized trace comparison, callers can
inspect:

- `semantic_handoffs_equivalent`
- `invalidation_artifacts_equivalent`

These booleans compare exported `SemanticHandoff` objects plus invalidated
effect ids and `TransformationObligation` bundles. This keeps stale-owner and
late-result mismatches visible even when the raw instruction trace still
normalizes successfully.

## Semantic-Audit Normalization and Equivalence

`protocol_machine_trace::event_session()` extracts session ids from common event shapes.
Supported fields include `session`, `sid`, `edge.sid`, and `endpoint.sid`.
The extractor also searches nested objects.

`normalize_semantic_audit()` rewrites tick values into per-session local counters.
Events that have no session id remain unchanged.

`semantic_audits_equivalent()` and `observationally_equivalent()` compare traces after this normalization.
`partition_by_session()` groups normalized events into per-session subsequences.

## Invariant Bundle Export

`invariants` defines typed claim schemas for Lean-side protocol bundle verification.
Top-level payload type is `ProtocolBundle`.

```rust
pub struct ProtocolBundle {
    pub schema_version: String,
    pub global_type: Value,
    pub local_types: BTreeMap<String, Value>,
    pub claims: InvariantClaims,
}
```

`export_protocol_bundle()` converts `GlobalType` and `LocalTypeR` maps into bridge JSON and attaches typed `InvariantClaims`.
Claims include liveness configuration, distributed systems claims, and classical queueing and stochastic claim families.

## Equivalence Workflows

`equivalence::EquivalenceChecker` supports two paths.
Golden mode compares Rust projections against stored expected JSON.
Live mode compares Rust projections against fresh Lean runner output.

Golden bundles are stored under `golden/<test_name>` with `input.json` and `<role>.expected.json` files.
`check_golden_drift()` detects divergence between stored and fresh Lean projections.

`EquivalenceResult` includes `equivalent`, `role`, both outputs, and a human-readable diff when unequal.
Comparison uses structural JSON equality rather than string formatting equality.

## Validator Utilities

`validate::Validator` provides lightweight checks that do not require full protocol-machine execution.
It supports global and local JSON roundtrip validation and projection result comparison.

`compare_subtyping()` compares Rust and Lean subtype decisions through `SubtypingDecision`.
`validate_projection_with_lean()` calls the Lean binary when available and returns `ValidationResult`.

`lean_available()` checks bridge runner availability using either an explicit path or default runner lookup.
These helpers are used by integration tests and tooling workflows.

## CLI Tools

The crate ships three CLIs behind features.
Each CLI targets a different workflow stage.

- `lean-bridge`: sample export, import, validate, and sample generation helpers.
- `lean-bridge-exporter`: convert choreography DSL input into choreography and program JSON files for Lean validation.
- `golden`: regenerate, check, add, and list projection golden files.

`lean-bridge` and `golden` use `clap` parsing. `lean-bridge-exporter` uses `bpaf`.

The `golden` CLI expects Lean validator availability for regeneration and drift checks.
It resolves relative `--golden-dir` paths from the crate manifest directory.

## Test Lanes

Bridge tests in `rust/lean-bridge/tests` cover conversion, projection parity, schema compatibility, invariant verification, and protocol-machine correspondence.
Most Lean-dependent tests skip when Lean binaries are missing.

- `coherence_tests.rs`
- `generated_effect_schema.rs`
- `golden_equivalence_tests.rs`
- `invariant_verification.rs`
- `lean_integration_tests.rs`
- `live_equivalence_tests.rs`
- `merge_semantics_tests.rs`
- `projection_equivalence.rs`
- `projection_runner_tests.rs`
- `property_tests.rs`
- `proptest_async_subtyping.rs`
- `proptest_bundle.rs`
- `proptest_json_roundtrip.rs`
- `proptest_projection.rs`
- `schema_version_tests.rs`
- `semantic_object_roundtrip.rs`
- `semantics_verification.rs`
- `vm_composition_stress.rs`
- `vm_correspondence_tests.rs`
- `vm_cross_target_tests.rs`
- `vm_differential_steps.rs`

These lanes are aligned with repository parity and release-gate lanes.
Examples include `just check-parity --types`, `just check-parity --suite`, and `just check-capability-gates`.

## Current Limits and Behaviors

Projection export methods accept multiple Lean projection output shapes.
This preserves compatibility with object and array forms from different validator revisions.

`ProtocolMachineRunner` comparison reports the first normalized event mismatch through `compute_trace_diff()`.
If event prefixes match, it reports a length mismatch summary.

The bridge normalizes per-session tick numbering for trace comparison.
This removes cross-session interleaving noise but keeps event payload differences visible.

## Related Docs

- [Lean Verification](23_lean_verification.md)
- [Protocol-Machine Simulation](15_vm_simulation_overview.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
- [Capability and Admission](25_capability_admission.md)
