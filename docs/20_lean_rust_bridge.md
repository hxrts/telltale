# Lean-Rust Bridge

The `telltale-lean-bridge` crate connects Rust implementations to Lean verification. It provides JSON serialization, test infrastructure, and the `LeanRunner` for invoking the Lean binary.

## Two Projection Implementations

The project maintains two independent projection implementations.

| Implementation | Location | Purpose |
|---------------|----------|---------|
| Theory Projection | `rust/theory/src/projection.rs` | Minimal, matches Lean formalization |
| DSL Projection | `rust/choreography/src/compiler/projection.rs` | Extended features for code generation |

The Theory Projection implements core MPST projection with direct correspondence to Lean. The DSL Projection extends this for practical use. Cross-validation tests verify both produce equivalent results on the common subset of protocols.

## JSON Format Specification

The JSON format mirrors Lean type definitions exactly. Each type uses a discriminated union with a `kind` field.

### GlobalType

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

This represents communication with labeled branches.

```json
{
  "kind": "mu",
  "var": "loop",
  "body": { "kind": "var", "name": "loop" }
}
```

This represents a recursive type with explicit binding.

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

This represents internal choice where the sender selects a branch.

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

This represents external choice where the sender selects and the receiver handles.

### PayloadSort

```json
{ "sort": "unit" }
{ "sort": "nat" }
{ "sort": "bool" }
{ "sort": "string" }
{ "sort": { "prod": [{ "sort": "nat" }, { "sort": "bool" }] } }
```

These examples show the supported payload sorts including products.

## Test Infrastructure

### Cross-Validation Tests

Location: `rust/lean-bridge/tests/projection_equivalence_tests.rs`

These tests verify DSL and Theory projections produce equivalent results. Coverage includes simple sends, multi-message sequences, binary and multi-way choices, nested choices, three-party protocols, non-participant merging scenarios, and recursive protocols with explicit `continue` statements.

```
rec Loop {
    A -> B: Ping
    B -> A: Pong
    continue Loop
}
```

The tests parse DSL choreographies, project using both implementations, and compare results structurally. Recursive protocols use explicit `continue` syntax that maps directly to the theory's `Var` constructor.

### Projection Property Tests

Location: `rust/lean-bridge/tests/proptest_projection.rs`

Randomized testing with deterministic seeds covers simple protocols, choice protocols with binary and multi-way branches, deep nesting at 4-6 levels, three-party non-participant merge scenarios, and continuation preservation regressions. Each generated protocol is validated against the Lean binary when available.

### Async Subtyping Property Tests

Location: `rust/lean-bridge/tests/proptest_async_subtyping.rs`

These tests validate the SISO decomposition and asynchronous subtyping algorithms from `telltale-theory`. The test suite uses fixed seeds for full reproducibility.

```rust
// Example: Input tree contravariance property
let tree = InputTree::Node {
    partner: "Alice".to_string(),
    label: Label::new("msg"),
    children: vec![InputTree::Leaf],
};
assert!(tree.subtype(&InputTree::Leaf));
```

Input tree subtyping is contravariant where a process accepting more inputs is substitutable for one accepting fewer. Output tree subtyping is covariant where a process sending fewer outputs is substitutable for one sending more.

The property tests cover input tree reflexivity and contravariance, output tree reflexivity and covariance, SISO decomposition for simple types and sequences, `async_subtype` and `async_equivalent` reflexivity and symmetry, orphan freedom checks, choice type decomposition, recursive type handling, and segment subtyping.

### Lean Integration Tests

Location: `rust/lean-bridge/tests/lean_integration_tests.rs`

Direct validation against the Lean runner covers ping-pong protocols, three-party ring topologies, choice branching correctness, recursive protocols unrolled one iteration, error detection for invalid projections and wrong labels, and complex multi-branch protocols.

## CI Enforcement

The GitHub Actions workflow ensures Lean verification runs on every push.

1. Build Lean binary: `cd lean && lake build`
2. Run Lean verification scripts: `just telltale-lean-check*`
3. Run Lean-validated Rust tests: `cargo test -p telltale-lean-bridge`

The test `test_lean_binary_available_for_ci` explicitly requires the Lean binary and fails if missing. This makes Lean verification mandatory in CI rather than silently skipped.

## Running Tests Locally

### Build Lean Binary

```bash
# With Nix (recommended)
nix develop --command bash -c "cd lean && lake build"

# Without Nix (requires Lean 4 toolchain)
cd lean && lake build
```

These commands build the Lean binary required for cross-validation tests.

### Run All Lean-Validated Tests

```bash
# Full test suite
cargo test -p telltale-lean-bridge

# Cross-validation only
cargo test -p telltale-lean-bridge --test projection_equivalence_tests

# Projection property tests only
cargo test -p telltale-lean-bridge --test proptest_projection

# Async subtyping property tests only
cargo test -p telltale-lean-bridge --test proptest_async_subtyping

# Integration tests only
cargo test -p telltale-lean-bridge --test lean_integration_tests
```

These commands run specific test suites for focused debugging.

## Rust API

### Export and Import

```rust
use telltale_lean_bridge::{global_to_json, local_to_json, json_to_global, json_to_local};
use telltale_types::{GlobalType, LocalTypeR, Label};

let g = GlobalType::comm(
    "Client",
    "Server",
    vec![(Label::new("hello"), GlobalType::End)],
);
let json = global_to_json(&g);

let parsed = json_to_global(&json)?;
```

This example shows the round-trip export and import of a global type through JSON.

### LeanRunner

```rust
use telltale_lean_bridge::LeanRunner;

// Check availability
if LeanRunner::is_available() {
    let runner = LeanRunner::new()?;
    let result = runner.validate(&choreography_json, &program_json)?;
    assert!(result.success);
}

// For CI: require Lean (panics if missing)
LeanRunner::require_available();
```

The `LeanRunner` invokes the Lean binary for validation. Use `is_available()` to check for the binary before use. Use `require_available()` in CI environments where the binary must be present.

### Validator

```rust
use telltale_lean_bridge::Validator;

let validator = Validator::new();
let result = validator.validate_projection_with_lean(&choreo, &program)?;
assert!(result.is_valid());
```

The `Validator` provides a higher-level API for comparing Rust and Lean projections.

## CLI Tool

```bash
cargo build -p telltale-lean-bridge --features cli --release
```

This command builds the CLI with the `cli` feature enabled.

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

These commands demonstrate the CLI operations for generating, validating, and converting protocol JSON.

## Merge Semantics

The Rust merge implementation matches the Lean formalization in `ProjectionR.lean`.

Send merge follows `mergeSendSorted` where branches must have identical label sets. A non-participant cannot choose based on an unseen choice. Receive merge follows `mergeRecvSorted` where branches union their label sets. A non-participant can handle any incoming message.

The `telltale-theory` crate implements these in `merge.rs`. Tests validate correspondence between Rust and Lean results.

## Error Handling

### Import Errors

```rust
use telltale_lean_bridge::ImportError;

match json_to_global(&json) {
    Ok(g) => println!("Parsed: {:?}", g),
    Err(ImportError::UnknownKind(k)) => eprintln!("Unknown kind: {}", k),
    Err(ImportError::MissingField(f)) => eprintln!("Missing field: {}", f),
    Err(ImportError::InvalidFormat(msg)) => eprintln!("Invalid: {}", msg),
}
```

Import errors distinguish between unknown type kinds, missing required fields, and format violations.

### Validation Results

```rust
use telltale_lean_bridge::ValidationResult;

match validator.compare_local(&rust, &lean) {
    ValidationResult::Match => println!("Types match"),
    ValidationResult::StructuralMismatch(diff) => eprintln!("Differs: {}", diff),
    ValidationResult::LabelMismatch { expected, found } => {
        eprintln!("Label: expected {}, found {}", expected, found);
    }
}
```

Validation results indicate whether types match or describe the specific mismatch.

## Extending the Bridge

### Adding Type Kinds

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

Update both export and import functions when adding new type kinds. Update Lean definitions to match.

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

Extend the `Validator` with custom comparison options as needed.

## References

See the following resources for background on the theoretical foundations.

- [Multiparty Session Types](https://doi.org/10.1145/1328438.1328472) by Honda et al.
- [Session Types and Choreographies](https://arxiv.org/abs/2301.00715) survey
