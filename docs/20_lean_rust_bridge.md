# Lean-Rust Bridge

The `telltale-lean-bridge` crate connects Rust implementations to Lean verification. It provides JSON export and import, cross validation utilities, and an optional runner for invoking the Lean binary.

## Two Projection Implementations

The project maintains two independent projections that should agree on the common subset.

- Theory projection in `rust/theory/src/projection.rs`
- DSL projection in `rust/choreography/src/compiler/projection.rs`

Cross validation tests in `rust/lean-bridge/tests/projection_equivalence_tests.rs` compare the two outputs.

## JSON Format

The bridge uses a discriminated union with a `kind` field. Recursion uses `kind: "rec"` and `var`.

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

## Test Suites

The bridge test coverage lives in `rust/lean-bridge/tests`:

- `projection_equivalence_tests.rs` compares theory and DSL projections
- `proptest_projection.rs` validates randomized protocols against Lean when available
- `proptest_json_roundtrip.rs` checks JSON round trip stability
- `lean_integration_tests.rs` and `projection_runner_tests.rs` run the Lean runner
- `golden_equivalence_tests.rs` and `live_equivalence_tests.rs` compare fixed suites

Use `cargo test -p telltale-lean-bridge` to run the full suite.

## Lean Runner

`LeanRunner` invokes `lean/.lake/build/bin/telltale_runner` and validates a choreography against a program export.

```rust
use telltale_lean_bridge::LeanRunner;

if LeanRunner::is_available() {
    let runner = LeanRunner::new()?;
    let result = runner.validate(&choreo_json, &program_json)?;
    assert!(result.success);
}
```

The runner returns per branch results with exported and projected traces.

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
