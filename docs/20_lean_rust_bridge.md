# Lean-Rust Bridge

The `telltale-lean-bridge` crate connects Rust implementations to Lean verification. It provides JSON export and import, cross validation utilities, and an optional runner for invoking the Lean binary.

For the normative VM architecture and proof-contract model used by bridge artifacts, see
`work/docs/vm_instructions.md`.

## Two Projection Implementations

The project maintains two independent projections that should agree on the common subset.

- Theory projection in `rust/theory/src/projection.rs`
- DSL projection in `rust/choreography/src/compiler/projection.rs`

Cross validation tests in `rust/lean-bridge/tests/projection_equivalence_tests.rs` compare the two outputs.

## JSON Format

The bridge uses a discriminated union with a `kind` field. Recursion uses `kind: "rec"` and `var`.
Top-level bridge payloads also carry a `schema_version` field (`lean_bridge.v1`) with backward-compatible defaulting for legacy payloads that omitted it.

```json
{ "kind": "end" }
```

This represents protocol termination.

```json
{
  "kind": "comm",
  "sender": "Client",
  "receiver": "Server",
  "branches": [
    {
      "label": { "name": "request", "sort": "unit" },
      "continuation": { "kind": "end" }
    }
  ]
}
```

This represents a global communication with labeled branches.

Local types follow the same pattern.

```json
{
  "kind": "send",
  "partner": "Server",
  "branches": [
    {
      "label": { "name": "request", "sort": "unit" },
      "continuation": { "kind": "end" }
    }
  ]
}
```

The payload sort supports `unit`, `nat`, `bool`, `string`, `real`, `vector`, and `prod`.

## Bridge Schemas

The bridge uses explicit versioned payload families. Current versions:

- `lean_bridge.v1` for runner payloads (`VmRunInput`, `VmRunOutput`, `ReplayTraceBundle`)
- `protocol_bundle.v1` for invariant verification bundles
- `vm_state.v1` for VM state export payloads

### VM State Export (`vm_state.v1`)

Exported by `telltale_lean_bridge::vm_state_to_json`:

```json
{
  "schema_version": "vm_state.v1",
  "compatibility": {
    "family": "vm_state",
    "version": "vm_state.v1",
    "backward_compatible_from": ["vm_state.v0"]
  },
  "clock": 7,
  "nextCoroId": 3,
  "nextSessionId": 2,
  "coroutines": [],
  "sessions": [],
  "obsTrace": []
}
```

Decoder compatibility in `vm_state_from_json` accepts legacy alias keys (for example
`next_coro_id`, `obs_trace`) so one prior shape can be read during migration.

### Protocol Bundle Export (`protocol_bundle.v1`)

Exported by `telltale_lean_bridge::export_protocol_bundle`:

```json
{
  "schema_version": "protocol_bundle.v1",
  "global_type": { "kind": "end" },
  "local_types": {},
  "claims": {
    "schema_version": "lean_bridge.v1",
    "liveness": null,
    "distributed": {},
    "classical": {}
  }
}
```

Core claim fields are typed enums/structs in Rust (not required string parsing) and serialized to JSON for Lean-side validation entrypoints.

### Trace Validation Payloads

`VmRunner` currently exposes two Lean validation operations:

- `validateTrace` request:
  - `{ "trace": [VmTraceEvent...] }`
- `verifyProtocolBundle` request:
  - `ProtocolBundle` JSON payload (schema `protocol_bundle.v1`)

Both responses are parsed into structured result types and include error objects with explicit `code` and `path` fields when validation fails.

## Replay and Effect Trace Schema

`telltale-lean-bridge` includes replay-oriented trace structures in `vm_trace`:

- `EffectTraceEvent`
  - `effect_id`
  - `effect_kind`
  - `inputs`
  - `outputs`
  - `handler_identity`
  - `ordering_key`
  - optional `topology` payload
- `TopologyPerturbationEvent`
  - `Crash`, `Partition`, `Heal`
- `OutputConditionTraceEvent`
  - `predicate_ref`
  - `witness_ref`
  - `output_digest`
  - `passed`
- `ReplayTraceBundle`
  - normalized VM trace
  - effect trace
  - output-condition trace

`VmRunOutput` accepts optional `effect_trace` and `output_condition_trace` arrays so runner integrations can carry deterministic replay artifacts without changing core VM event encoding.

## Test Suites

The bridge test coverage lives in `rust/lean-bridge/tests`:

- `projection_equivalence_tests.rs` compares theory and DSL projections
- `proptest_projection.rs` validates randomized protocols against Lean when available
- `proptest_json_roundtrip.rs` checks JSON round trip stability
- `lean_integration_tests.rs` runs the Lean validator. `projection_runner_tests.rs` exercises the validator export mode.
- `golden_equivalence_tests.rs` and `live_equivalence_tests.rs` compare fixed suites

Use `cargo test -p telltale-lean-bridge` to run the full suite.

## Lean Runner

`LeanRunner` invokes `lean/.lake/build/bin/telltale_validator` and validates a choreography against a local type export.

```rust
use telltale_lean_bridge::LeanRunner;

if LeanRunner::is_available() {
    let runner = LeanRunner::new()?;
    let result = runner.validate(&choreo_json, &program_json)?;
    assert!(result.success);
}
```

The runner returns a success flag plus a brief message when validation succeeds.

The program JSON is a `{ "role": "...", "local_type": { ... } }` wrapper around a LocalTypeR JSON object.

## Validator

`Validator` compares Rust results with Lean output and JSON round trips.

```rust
use telltale_lean_bridge::{ValidationResult, Validator};

let validator = Validator::new();
match validator.validate_projection_with_lean(&choreo_json, &program_json)? {
    ValidationResult::Valid => {}
    ValidationResult::Invalid(reason) => eprintln!("invalid: {reason}"),
    ValidationResult::Error(reason) => eprintln!("error: {reason}"),
}
```

Use `validate_global_roundtrip` and `validate_local_roundtrip` for JSON stability tests.

## CLI Tool

The `lean-bridge` binary is enabled by the `cli` feature.

```bash
cargo build -p telltale-lean-bridge --features cli --release
lean-bridge export --type global --pretty
lean-bridge import --type local --input protocol.json
lean-bridge validate --type global --input protocol.json
lean-bridge sample --sample ping-pong --pretty
```

The CLI supports `export`, `import`, `validate`, and `sample` commands for quick inspection.

See [Lean Verification](19_lean_verification.md) for the build recipes and [Choreographic DSL](04_choreographic_dsl.md) for the source syntax.
