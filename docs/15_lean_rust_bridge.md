# Lean-Rust Bridge

This document describes the bidirectional conversion between Rust session types and Lean-compatible JSON format. The bridge enables formal verification of protocol implementations.

## Overview

The `rumpsteak-lean-bridge` crate provides three capabilities. It exports Rust types to Lean-compatible JSON. It imports Lean JSON output into Rust types. It validates Rust implementations against Lean proofs.

## JSON Format Specification

The JSON format mirrors Lean type definitions exactly. Each type kind uses a discriminated union with a `kind` field. The following sections show the format for each type.

### GlobalType

The `GlobalType` represents protocols from a global perspective. It supports four constructors.

```json
{ "kind": "end" }
```

This represents protocol termination. No further communication occurs after this point.

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

This represents a communication from sender to receiver with labeled branches. Each branch has a label and a continuation type.

```json
{
  "kind": "mu",
  "var": "loop",
  "body": { "kind": "var", "name": "loop" }
}
```

This represents recursive types using explicit binding. The `var` field names the recursion variable. The `body` field contains the recursive structure.

```json
{ "kind": "var", "name": "loop" }
```

This represents a reference to a bound recursion variable.

### LocalTypeR

The `LocalTypeR` represents protocols from a single participant's view. It uses `send` for internal choice and `recv` for external choice.

```json
{ "kind": "end" }
```

This represents local protocol termination.

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

This represents sending a message to the partner. Multiple branches indicate internal choice where the sender selects.

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

This represents receiving a message from the partner. Multiple branches indicate external choice where the sender selects.

The `mu` and `var` constructors follow the same format as `GlobalType`.

### PayloadSort

Payload sorts classify the types of message payloads.

```json
{ "sort": "unit" }
{ "sort": "nat" }
{ "sort": "bool" }
{ "sort": "string" }
{ "sort": { "prod": [{ "sort": "nat" }, { "sort": "bool" }] } }
```

The first four represent atomic sorts. The last represents a product type combining two sorts.

### Label

Labels combine a name with a payload sort.

```json
{
  "name": "request",
  "sort": "unit"
}
```

This label has the name `request` and carries no payload data.

## Rust API

The bridge provides functions for export and import operations.

```rust
use rumpsteak_lean_bridge::{global_to_json, local_to_json, json_to_global, json_to_local};
use rumpsteak_types::{GlobalType, LocalTypeR, Label};

let g = GlobalType::comm(
    "Client",
    "Server",
    vec![(Label::new("hello"), GlobalType::End)],
);
let json = global_to_json(&g);

let json_str = r#"{"kind": "end"}"#;
let json: serde_json::Value = serde_json::from_str(json_str)?;
let g = json_to_global(&json)?;
```

The `global_to_json` function converts a Rust `GlobalType` to JSON. The `json_to_global` function parses JSON into a Rust `GlobalType`. Equivalent functions exist for `LocalTypeR`.

## CLI Tool

The `lean-bridge` CLI tool is available with the `cli` feature.

```bash
lean-bridge sample --sample ping-pong --pretty
lean-bridge sample --sample calculator --pretty
lean-bridge validate --input protocol.json --type global
lean-bridge import --input protocol.json --type local
lean-bridge export --type global --output protocol.json --pretty
```

The `sample` command generates example protocol JSON. The `validate` command checks JSON round-trip correctness. The `import` command parses and displays JSON. The `export` command writes a sample to a file.

To build the CLI:

```bash
cd lean-bridge
cargo build --features cli --release
```

This compiles the CLI binary with release optimizations.

## Validation Workflow

The validation workflow has three steps. First export the Rust protocol. Then run Lean verification. Finally import and compare results.

### Step 1: Export Rust Protocol

```rust
use rumpsteak_lean_bridge::global_to_json;
use rumpsteak_types::GlobalType;

let protocol = GlobalType::comm(
    "Client",
    "Server",
    vec![(Label::new("request"), GlobalType::End)],
);

let json = global_to_json(&protocol);
std::fs::write("protocol.json", serde_json::to_string_pretty(&json)?)?;
```

This creates a JSON file containing the protocol definition. The file can be read by Lean for verification.

### Step 2: Run Lean Verification

```lean
import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.Projection

def protocolJson : String := ...

theorem protocol_well_formed : wellFormed protocol := by
  decide

theorem projection_defined : ∀ r, r ∈ roles protocol → project protocol r ≠ none := by
  ...
```

This Lean code imports the protocol and proves properties about it. The `wellFormed` theorem checks structural validity. The `projection_defined` theorem ensures all roles can be projected.

### Step 3: Import Lean Results

```rust
use rumpsteak_lean_bridge::{json_to_local, Validator};

let lean_output: serde_json::Value = serde_json::from_str(&lean_result)?;
let lean_local = json_to_local(&lean_output)?;

use rumpsteak_theory::project;
let rust_local = project(&protocol, "Client")?;

let validator = Validator::new();
let result = validator.compare_local(&rust_local, &lean_local);
assert!(result.is_match());
```

This imports the Lean projection result and compares it against the Rust projection. The `Validator` checks structural equality between the two types.

## Type Translation Patterns

This section shows common patterns for translating between Rust and JSON.

### Recursive Types

```rust
let lt = LocalTypeR::mu(
    "loop",
    LocalTypeR::send("B", Label::new("ping"), LocalTypeR::var("loop")),
);
```

This Rust code creates a recursive type that sends `ping` messages indefinitely.

```json
{
  "kind": "mu",
  "var": "loop",
  "body": {
    "kind": "send",
    "partner": "B",
    "branches": [
      {
        "label": { "name": "ping", "sort": "unit" },
        "continuation": { "kind": "var", "name": "loop" }
      }
    ]
  }
}
```

The JSON representation uses `mu` for the binder and `var` for references. The structure mirrors the Rust AST exactly.

### Choice with Multiple Branches

```rust
let lt = LocalTypeR::Send {
    partner: "Server".to_string(),
    branches: vec![
        (Label::new("add"), LocalTypeR::End.into()),
        (Label::new("quit"), LocalTypeR::End.into()),
    ],
};
```

This creates an internal choice between `add` and `quit` operations.

```json
{
  "kind": "send",
  "partner": "Server",
  "branches": [
    {
      "label": { "name": "add", "sort": "unit" },
      "continuation": { "kind": "end" }
    },
    {
      "label": { "name": "quit", "sort": "unit" },
      "continuation": { "kind": "end" }
    }
  ]
}
```

The JSON `branches` array contains all choice options. Each branch has a distinct label.

### Product Sorts

```rust
let label = Label::with_sort(
    "data",
    PayloadSort::Prod(
        Box::new(PayloadSort::Nat),
        Box::new(PayloadSort::String),
    ),
);
```

This creates a label carrying a pair of natural number and string.

```json
{
  "name": "data",
  "sort": {
    "prod": [
      { "sort": "nat" },
      { "sort": "string" }
    ]
  }
}
```

Product sorts nest recursively. The `prod` field contains an array of component sorts.

## Merge Semantics Correspondence

The Rust merge implementation matches the Lean formalization in `ProjectionR.lean`. This ensures projection produces correct local types.

Send merge corresponds to `mergeSendSorted` in Lean. Send branches must have identical label sets. A non-participant cannot choose which message to send based on an unseen choice.

Receive merge corresponds to `mergeRecvSorted` in Lean. Receive branches union their label sets. A non-participant can handle any incoming message regardless of which branch was taken.

The `rumpsteak-theory` crate implements these semantics in `merge.rs`. Tests in `rumpsteak-lean-bridge` validate correspondence between Rust and Lean results.

## Error Handling

The bridge provides structured error types for import failures and validation mismatches.

### Import Errors

```rust
use rumpsteak_lean_bridge::ImportError;

match json_to_global(&json) {
    Ok(g) => println!("Parsed: {:?}", g),
    Err(ImportError::UnknownKind(k)) => eprintln!("Unknown type kind: {}", k),
    Err(ImportError::MissingField(f)) => eprintln!("Missing field: {}", f),
    Err(ImportError::InvalidFormat(msg)) => eprintln!("Invalid format: {}", msg),
}
```

The `ImportError` enum distinguishes between unknown type kinds, missing required fields, and format errors. Each variant provides context for debugging.

### Validation Results

```rust
use rumpsteak_lean_bridge::ValidationResult;

match validator.compare_local(&rust, &lean) {
    ValidationResult::Match => println!("Types match"),
    ValidationResult::StructuralMismatch(diff) => {
        eprintln!("Structure differs: {}", diff);
    }
    ValidationResult::LabelMismatch { expected, found } => {
        eprintln!("Label mismatch: expected {}, found {}", expected, found);
    }
}
```

The `ValidationResult` enum reports match success or specific mismatch details. Structural mismatches include a diff description. Label mismatches report both expected and found values.

## Integration with CI

The bridge integrates with continuous integration for automated verification.

### Example GitHub Action

```yaml
name: Lean Verification

on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-action@stable

      - name: Install Lean
        uses: leanprover/lean4-action@v1

      - name: Build lean-bridge CLI
        run: cargo build -p rumpsteak-lean-bridge --features cli --release

      - name: Export protocols
        run: ./target/release/lean-bridge sample --sample calculator --pretty > protocol.json

      - name: Run Lean verification
        working-directory: lean
        run: lake build

      - name: Validate round-trip
        run: ./target/release/lean-bridge validate --input protocol.json --type global
```

This workflow installs both Rust and Lean toolchains. It builds the CLI and exports a sample protocol. It runs Lean verification and validates the round-trip.

## Lean Runner Integration

The `LeanRunner` struct invokes the Lean verification binary from Rust tests.

```rust
use rumpsteak_lean_bridge::LeanRunner;
use serde_json::json;

let runner = LeanRunner::new()?;
let result = runner.validate(&choreography_json, &program_json)?;
assert!(result.success);
```

This invokes the Lean binary with JSON input and parses the validation result. The runner handles temporary file creation and process management.

Tests can gracefully skip when the Lean binary is unavailable.

```rust
use rumpsteak_lean_bridge::skip_without_lean;

#[test]
fn test_lean_validation() {
    skip_without_lean!();
    // Test code that requires Lean...
}
```

The macro checks for the Lean binary at `lean/.lake/build/bin/rumpsteak_runner` and skips the test if not found.

## Extending the Bridge

The bridge supports extension for new type kinds and custom validation.

### Adding New Type Kinds

To add a new type kind, update both export and import functions.

```rust
fn global_to_json(g: &GlobalType) -> Value {
    match g {
        GlobalType::MyNewType { field } => json!({
            "kind": "my_new_type",
            "field": field,
        }),
        // other cases
    }
}
```

The export function maps the new variant to JSON. Include all fields in the JSON object.

```rust
fn json_to_global(json: &Value) -> Result<GlobalType, ImportError> {
    match json["kind"].as_str() {
        Some("my_new_type") => {
            let field = json["field"].as_str().ok_or(ImportError::MissingField("field"))?;
            Ok(GlobalType::MyNewType { field: field.to_string() })
        }
        // other cases
    }
}
```

The import function parses the JSON and constructs the Rust type. Update the Lean definitions to match the new format.

### Custom Validators

Extend the `Validator` struct for custom validation logic.

```rust
impl Validator {
    pub fn validate_with_options(
        &self,
        rust: &LocalTypeR,
        lean: &Value,
        options: ValidationOptions,
    ) -> ValidationResult {
        // custom validation logic
    }
}
```

Custom validators can implement domain-specific comparison rules. The `ValidationOptions` parameter controls comparison behavior.
