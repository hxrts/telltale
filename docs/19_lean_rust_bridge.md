# Lean-Rust Bridge

The `telltale-lean-bridge` crate is the typed boundary between Rust artifacts and Lean validation entrypoints.
It handles JSON conversion, schema versioning, runner invocation, trace comparison, and typed invariant bundle export.

The bridge does not define VM semantics.
Semantics remain in `telltale-vm`, `telltale-theory`, and Lean runtime modules.

## Scope

This document covers runtime bridge behavior implemented in `rust/lean-bridge/src`.
It covers `export`, `import`, `schema`, `runner`, `vm_runner`, `sim_reference`, `vm_export`, `vm_trace`, `invariants`, `equivalence`, and `validate`.

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
exporter = ["telltale-choreography", "anyhow"]
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

`runner` controls `LeanRunner`, `VmRunner`, and equivalence modules.
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
| Lean bridge core | `LEAN_BRIDGE_SCHEMA_VERSION` | `lean_bridge.v1` | `VmRunInput`, `VmRunOutput`, `SimRunInput`, `SimRunOutput`, replay bundles |
| Protocol bundles | `PROTOCOL_BUNDLE_SCHEMA_VERSION` | `protocol_bundle.v1` | `ProtocolBundle` |
| VM state export | `VM_STATE_SCHEMA_VERSION` | `vm_state.v1` | `VMState` export payloads |

`schema::ensure_supported_schema_version()` rejects unsupported `lean_bridge` versions.
`vm_export` supports alias decoding for legacy `vm_state.v0` field names such as `next_coro_id` and `obs_trace`.

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
    pub trace: Vec<VmTraceEvent>,
    pub violations: Vec<Value>,
    pub artifacts: Value,
}

pub struct SimTraceValidation {
    pub valid: bool,
    pub errors: Vec<SimulationStructuredError>,
    pub artifacts: Value,
}
```

`SimRunInput` and `SimRunOutput` default `schema_version` to `lean_bridge.v1` during deserialization.
This preserves compatibility with legacy payloads that omit explicit schema fields.

## Lean Runner

`LeanRunner` invokes the Lean validator binary at `lean/.lake/build/bin/telltale_validator`.
Path discovery walks upward from `CARGO_MANIFEST_DIR` and looks for a workspace root containing `lean/.lake`.

`LeanRunner::validate()` writes choreography and program JSON into temp files, runs the binary, and parses JSON log output when available.
The parsed result is `LeanValidationResult { success, role, message, raw_output }`.

Projection methods call validator export modes.
`project()` runs `--export-all-projections` and accepts both object and array projection formats from Lean output.
`export_projection()` and `export_all_projections()` expose single-role and all-role export modes directly.
`run_vm_protocol()` is also exposed on `LeanRunner` and forwards VM choreographies to the Lean `vm_runner` binary through stdin JSON.

## Lean VM Runner Wrapper

`VmRunner` wraps the Lean VM binary at `lean/.lake/build/bin/vm_runner`.
It serializes `VmRunInput` to process stdin and parses `VmRunOutput` from stdout.

```rust
pub struct VmRunInput {
    pub schema_version: String,
    pub choreographies: Vec<ChoreographyJson>,
    pub concurrency: u64,
    pub max_steps: u64,
}

pub struct VmRunOutput {
    pub schema_version: String,
    pub trace: Vec<VmTraceEvent>,
    pub sessions: Vec<VmSessionStatus>,
    pub steps_executed: u64,
    pub concurrency: u64,
    pub status: String,
    pub effect_trace: Vec<EffectTraceEvent>,
    pub output_condition_trace: Vec<OutputConditionTraceEvent>,
    pub step_states: Vec<VmStepState>,
}
```

`VmRunner::run()` enforces schema compatibility checks on both input and output.
It returns structured `VmRunnerError` values for binary lookup, process failure, IO, and parse failures.

`validate_trace()` invokes Lean operation `validateTrace`.
`run_reference_simulation()` invokes Lean operation `runSimulation`.
`validate_simulation_trace()` invokes Lean operation `validateSimulationTrace`.
`verify_invariants()` invokes Lean operation `verifyProtocolBundle`.
`compare_execution()` runs the same choreography in Lean and compares normalized traces.

`run_reference_simulation()` decodes `SimRunOutput` and enforces schema checks on response payloads.
`validate_simulation_trace()` returns typed `SimTraceValidation` values with structured `SimulationStructuredError` entries.

## VM State Export Surface

`vm_export` provides generic payload structs that avoid a hard dependency on `telltale-vm` to prevent crate cycles.
Runtime adapters can map concrete VM data into these bridge structs.

`VMState<G, E>` carries clock, coroutine list, session view list, and ticked observable trace.
It includes `CompatibilityMeta { family, version, backward_compatible_from }`.

`vm_state_to_json()` emits canonical field names such as `nextCoroId` and `obsTrace`.
`vm_state_from_json()` accepts alias fields for compatibility with older payload shapes.

## Trace Normalization and Equivalence

`vm_trace::event_session()` extracts session ids from common event shapes.
Supported fields include `session`, `sid`, `edge.sid`, and `endpoint.sid`.
The extractor also searches nested objects.

`normalize_vm_trace()` rewrites tick values into per-session local counters.
Events that have no session id remain unchanged.

`traces_equivalent()` and `observationally_equivalent()` compare traces after this normalization.
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

Golden bundles are stored under `golden/projection/<test_name>` with `input.json` and `<role>.expected.json` files.
`check_golden_drift()` detects divergence between stored and fresh Lean projections.

`EquivalenceResult` includes `equivalent`, `role`, both outputs, and a human-readable diff when unequal.
Comparison uses structural JSON equality rather than string formatting equality.

## Validator Utilities

`validate::Validator` provides lightweight checks that do not require full VM execution.
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

The `golden` CLI expects Lean validator availability for regeneration and drift checks.
It resolves relative `--golden-dir` paths from the crate manifest directory.

## Test Lanes

Bridge tests in `rust/lean-bridge/tests` cover conversion, projection parity, schema compatibility, invariant verification, and VM correspondence.
Most Lean-dependent tests skip when Lean binaries are missing.

- `schema_version_tests.rs`
- `projection_runner_tests.rs`
- `golden_equivalence_tests.rs`
- `live_equivalence_tests.rs`
- `invariant_verification_tests.rs`
- `vm_correspondence_tests.rs`
- `vm_differential_step_tests.rs`
- `vm_cross_target_matrix_tests.rs`
- `property_tests.rs`
- `vm_composition_stress_tests.rs`

These lanes are aligned with repository parity and release gate scripts.
Examples include `scripts/check-parity-ledger.sh`, `scripts/check-vm-parity-suite.sh`, and `scripts/check-runtime-contract-gates.sh`.

## Current Limits and Behaviors

Projection export methods accept multiple Lean projection output shapes.
This preserves compatibility with object and array forms from different validator revisions.

`VmRunner` comparison reports the first normalized event mismatch through `compute_trace_diff()`.
If event prefixes match, it reports a length mismatch summary.

The bridge normalizes per-session tick numbering for trace comparison.
This removes cross-session interleaving noise but keeps event payload differences visible.

## Related Docs

- [Lean Verification](18_lean_verification.md)
- [VM Simulation](14_vm_simulation.md)
- [VM Parity](15_vm_parity.md)
