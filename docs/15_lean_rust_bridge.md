# Lean-Rust Bridge

The `rumpsteak-lean-bridge` crate connects Rust implementations to Lean verification. It provides JSON serialization, test infrastructure, and the `LeanRunner` for invoking the Lean binary.

## Two Projection Implementations

The project maintains two independent projection implementations:

| Implementation | Location | Purpose |
|---------------|----------|---------|
| **Theory Projection** | `rust/theory/src/projection.rs` | Minimal, matches Lean formalization |
| **DSL Projection** | `rust/choreography/src/compiler/projection.rs` | Extended features for code generation |

The Theory Projection implements core MPST projection with direct correspondence to Lean. The DSL Projection extends this for practical use. Cross-validation tests verify both produce equivalent results on the common subset of protocols.

## JSON Format Specification

The JSON format mirrors Lean type definitions exactly. Each type uses a discriminated union with a `kind` field.

### GlobalType

```json
{ "kind": "end" }
```

Protocol termination.

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

Communication with labeled branches.

```json
{
  "kind": "mu",
  "var": "loop",
  "body": { "kind": "var", "name": "loop" }
}
```

Recursive type with explicit binding.

### LocalTypeR

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

Internal choice (sender selects).

```json
{
  "kind": "recv",
  "partner": "Client",
  "branches": [
    {
      "label": { "name": "response", "sort": "string" },
      "continuation": { "kind": "end" }
    }
  ]
}
```

External choice (sender selects, receiver handles).

### PayloadSort

```json
{ "sort": "unit" }
{ "sort": "nat" }
{ "sort": "bool" }
{ "sort": "string" }
{ "sort": { "prod": [{ "sort": "nat" }, { "sort": "bool" }] } }
```

## Test Infrastructure

### Cross-Validation Tests

Location: `rust/lean-bridge/tests/projection_equivalence_tests.rs`

These tests verify DSL and Theory projections produce equivalent results:

- Simple sends and multi-message sequences
- Binary and multi-way choices (3+ branches)
- Nested choices
- Three-party protocols
- Non-participant merging scenarios
- **Recursive protocols** with explicit `continue` statements

The tests parse DSL choreographies, project using both implementations, and compare results structurally. Recursive protocols use explicit `continue` syntax that maps directly to the theory's `Var` constructor:

```
rec Loop {
    A -> B: Ping
    B -> A: Pong
    continue Loop
}
```

### Property-Based Tests

Location: `rust/lean-bridge/tests/proptest_projection.rs`

Randomized testing with deterministic seeds covers:

- **Simple protocols**: End, single send, sequences
- **Choice protocols**: Binary and multi-way (3-5 branches)
- **Deep nesting**: 4-6 level depth
- **Three-party**: Non-participant merge scenarios
- **Continuation preservation**: Regression tests for fixed bugs

Each generated protocol is validated against the Lean binary when available.

### Lean Integration Tests

Location: `rust/lean-bridge/tests/lean_integration_tests.rs`

Direct validation against the Lean runner:

- Ping-pong protocols
- Three-party ring topologies
- Choice branching correctness
- Recursive protocols (unrolled one iteration)
- Error detection (invalid projections, wrong labels)
- Complex multi-branch protocols

## CI Enforcement

The GitHub Actions workflow ensures Lean verification runs on every push:

1. Build Lean binary: `cd lean && lake build`
2. Run Lean verification scripts: `just rumpsteak-lean-check*`
3. Run Lean-validated Rust tests: `cargo test -p rumpsteak-lean-bridge`

The test `test_lean_binary_available_for_ci` explicitly requires the Lean binary and fails if missing. This makes Lean verification mandatory in CI rather than silently skipped.

## Running Tests Locally

### Build Lean Binary

```bash
# With Nix (recommended)
nix develop --command bash -c "cd lean && lake build"

# Without Nix (requires Lean 4 toolchain)
cd lean && lake build
```

### Run All Lean-Validated Tests

```bash
# Full test suite
cargo test -p rumpsteak-lean-bridge

# Cross-validation only
cargo test -p rumpsteak-lean-bridge --test projection_equivalence_tests

# Property tests only
cargo test -p rumpsteak-lean-bridge --test proptest_projection

# Integration tests only
cargo test -p rumpsteak-lean-bridge --test lean_integration_tests
```

## Rust API

### Export and Import

```rust
use rumpsteak_lean_bridge::{global_to_json, local_to_json, json_to_global, json_to_local};
use rumpsteak_types::{GlobalType, LocalTypeR, Label};

let g = GlobalType::comm(
    "Client",
    "Server",
    vec![(Label::new("hello"), GlobalType::End)],
);
let json = global_to_json(&g);

let parsed = json_to_global(&json)?;
```

### LeanRunner

```rust
use rumpsteak_lean_bridge::LeanRunner;

// Check availability
if LeanRunner::is_available() {
    let runner = LeanRunner::new()?;
    let result = runner.validate(&choreography_json, &program_json)?;
    assert!(result.success);
}

// For CI: require Lean (panics if missing)
LeanRunner::require_available();
```

### Validator

```rust
use rumpsteak_lean_bridge::Validator;

let validator = Validator::new();
let result = validator.validate_projection_with_lean(&choreo, &program)?;
assert!(result.is_valid());
```

## CLI Tool

Build the CLI with the `cli` feature:

```bash
cargo build -p rumpsteak-lean-bridge --features cli --release
```

Commands:

```bash
# Generate sample protocol JSON
lean-bridge sample --sample ping-pong --pretty
lean-bridge sample --sample calculator --pretty

# Validate JSON round-trip
lean-bridge validate --input protocol.json --type global

# Parse and display JSON
lean-bridge import --input protocol.json --type local

# Export sample to file
lean-bridge export --type global --output protocol.json --pretty
```

## Merge Semantics

The Rust merge implementation matches the Lean formalization in `ProjectionR.lean`:

- **Send merge** (`mergeSendSorted`): Branches must have identical label sets. A non-participant cannot choose based on an unseen choice.
- **Receive merge** (`mergeRecvSorted`): Branches union their label sets. A non-participant can handle any incoming message.

The `rumpsteak-theory` crate implements these in `merge.rs`. Tests validate correspondence between Rust and Lean results.

## Error Handling

### Import Errors

```rust
use rumpsteak_lean_bridge::ImportError;

match json_to_global(&json) {
    Ok(g) => println!("Parsed: {:?}", g),
    Err(ImportError::UnknownKind(k)) => eprintln!("Unknown kind: {}", k),
    Err(ImportError::MissingField(f)) => eprintln!("Missing field: {}", f),
    Err(ImportError::InvalidFormat(msg)) => eprintln!("Invalid: {}", msg),
}
```

### Validation Results

```rust
use rumpsteak_lean_bridge::ValidationResult;

match validator.compare_local(&rust, &lean) {
    ValidationResult::Match => println!("Types match"),
    ValidationResult::StructuralMismatch(diff) => eprintln!("Differs: {}", diff),
    ValidationResult::LabelMismatch { expected, found } => {
        eprintln!("Label: expected {}, found {}", expected, found);
    }
}
```

## Extending the Bridge

### Adding Type Kinds

Update both export and import:

```rust
fn global_to_json(g: &GlobalType) -> Value {
    match g {
        GlobalType::MyNewType { field } => json!({
            "kind": "my_new_type",
            "field": field,
        }),
        // ...
    }
}

fn json_to_global(json: &Value) -> Result<GlobalType, ImportError> {
    match json["kind"].as_str() {
        Some("my_new_type") => {
            let field = json["field"].as_str()
                .ok_or(ImportError::MissingField("field"))?;
            Ok(GlobalType::MyNewType { field: field.to_string() })
        }
        // ...
    }
}
```

Update Lean definitions to match.

### Custom Validators

```rust
impl Validator {
    pub fn validate_with_options(
        &self,
        rust: &LocalTypeR,
        lean: &Value,
        options: ValidationOptions,
    ) -> ValidationResult {
        // Custom logic
    }
}
```

## References

- [Multiparty Session Types](https://doi.org/10.1145/1328438.1328472) - Honda et al.
- [Session Types and Choreographies](https://arxiv.org/abs/2301.00715) - Survey
- [Lean 4 Theorem Prover](https://lean-lang.org/)
