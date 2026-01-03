# Crate Architecture

This document describes the crate architecture introduced in v0.7.0. The structure aligns with Lean verification and provides clear separation of concerns.

## Crate Dependency Graph

```mermaid
graph TB
    subgraph Foundation
        types["rumpsteak-types<br/>Core type definitions"]
    end

    subgraph Theory
        theory["rumpsteak-theory<br/>Algorithms: projection, merge, subtyping"]
    end

    subgraph Verification
        lean["rumpsteak-lean-bridge<br/>Lean interop & validation"]
    end

    subgraph Application
        choreo["rumpsteak-aura-choreography<br/>DSL, parsing & code generation"]
        macros["rumpsteak-aura-macros<br/>Proc macros"]
    end

    subgraph Facade
        main["rumpsteak-aura<br/>Main crate, re-exports"]
    end

    types --> theory
    types --> lean
    types --> choreo

    theory --> choreo

    choreo --> macros

    theory --> main
    choreo --> main
    lean --> main
```

This diagram shows the dependency relationships between crates. Arrows indicate dependency direction. The `rumpsteak-types` crate serves as the foundation for all other crates.

## Crate Descriptions

### rumpsteak-types

This crate is located in `rust/types/`. It contains all core type definitions that match Lean exactly. It has no dependencies on other workspace crates.

The crate defines `GlobalType` for global protocol views. It defines `LocalTypeR` for local participant views. It also defines `Label` for message labels with payload sorts, `PayloadSort` for type classification, and `Action` for send and receive actions.

The crate also provides content addressing infrastructure. The `ContentId` type wraps a cryptographic hash. The `Contentable` trait defines canonical serialization. The `Hasher` trait abstracts hash algorithms.

**Feature flags:**

- `dag-cbor` — Enables DAG-CBOR serialization for IPLD/IPFS compatibility. Adds `to_cbor_bytes()`, `from_cbor_bytes()`, and `content_id_cbor_sha256()` methods to `Contentable` types.

```rust
use rumpsteak_types::{GlobalType, LocalTypeR, Label, PayloadSort};

let g = GlobalType::comm(
    "Client",
    "Server",
    vec![(Label::new("request"), GlobalType::End)],
);

let lt = LocalTypeR::send("Server", Label::new("request"), LocalTypeR::End);
```

The first expression creates a global type matching Lean's `GlobalType.comm "Client" "Server" [...]` constructor. The second creates a local type matching Lean's `LocalTypeR.send "Server" [...]` constructor.

### rumpsteak-theory

This crate is located in `rust/theory/`. It implements pure algorithms for session type operations. The crate performs no IO or parsing.

The `projection` module handles `GlobalType` to `LocalTypeR` projection with merging. The `merge` module implements branch merging with distinct semantics for send and receive. Send merge requires identical label sets while receive merge unions labels. This matches Lean's `mergeSendSorted` and `mergeRecvSorted` functions.

The `subtyping/sync` module provides synchronous subtyping. The `subtyping/async` module provides asynchronous subtyping via SISO decomposition. The `well_formedness` module contains validation predicates. The `duality` module computes dual types. The `bounded` module implements bounded recursion strategies.

The `content_id` module provides content addressing for all types. Projection results are memoized by content ID for performance. See [Content Addressing](05_content_addressing.md) for details.

```rust
use rumpsteak_theory::{project, merge, sync_subtype, async_subtype};
use rumpsteak_types::GlobalType;

let global = GlobalType::comm("A", "B", vec![...]);
let local_a = project(&global, "A")?;
let local_b = project(&global, "B")?;

assert!(sync_subtype(&local_a, &local_a_expected));
```

The `project` function computes the local type for a given role. The `sync_subtype` function checks synchronous subtyping between local types.

### rumpsteak-lean-bridge

This crate is located in `rust/lean-bridge/`. It provides bidirectional conversion between Rust types and Lean-compatible JSON. See [Lean-Rust Bridge](15_lean_rust_bridge.md) for detailed documentation.

The `export` module converts Rust types to JSON for Lean. The `import` module converts Lean JSON back to Rust types. The `validate` module provides cross-validation between Rust and Lean.

The `lean-bridge` CLI tool is available with the `cli` feature.

```bash
lean-bridge sample --sample ping-pong --pretty
lean-bridge validate --input protocol.json --type global
lean-bridge import --input protocol.json
```

These commands generate samples, validate round-trips, and import JSON respectively.

### rumpsteak-aura-choreography

This crate is located in `rust/choreography/`. It provides DSL and parsing for choreographic programming. It depends on `rumpsteak-types` and `rumpsteak-theory`.

The `ast/` directory contains extended AST types including `Protocol`, `LocalType`, and `Role`. The `compiler/parser` module handles DSL parsing. The `compiler/projection` module handles choreography to `LocalType` projection. The `compiler/codegen` module handles Rust code generation. The `effects/` directory contains the effect system and handlers. The `extensions/` directory contains the DSL extension system. The `runtime/` directory contains platform abstraction.

The `topology/` directory provides deployment configuration. See [Topology](08_topology.md) for the separation between protocol logic and deployment. The `heap/` directory provides explicit resource management. See [Resource Heap](09_resource_heap.md) for nullifier-based consumption tracking.

### rumpsteak-aura

This crate is located in `rust/src/`. It is the main facade crate that re-exports from all other crates.

The crate supports several feature flags. The `theory` feature includes `rumpsteak-theory` algorithms. The `lean-bridge` feature includes `rumpsteak-lean-bridge`. The `full` feature enables all features.

```rust
use rumpsteak_aura::prelude::*;
```

The prelude provides access to types, theory algorithms, and other commonly used items.

## Data Flow

```
DSL Text                 Choreography AST               GlobalType
-----------► Parser -------------------► Lower -------------------►
 "A -> B"                    (DSL)                    (rumpsteak-types)

                                |
                                | project()
                                v

                            LocalTypeR
                         (rumpsteak-types)
                                |
                +---------------+---------------+
                |                               |
                v                               v
          Session Types                       JSON
          & Effect Programs                  (Lean)
          (choreography)                  (lean-bridge)
                |                               |
                v                               v
            Runtime                           Lean
           Execution                       Validation
```

The flow begins with DSL text parsed into a choreography AST. The AST is lowered to `GlobalType`. Projection computes `LocalTypeR` for each role. From local types, code generation produces session types, effect programs, or JSON for Lean.

## Lean Correspondence

The types crate mirrors Lean definitions exactly. The following table shows the correspondence.

| Lean Type | Rust Type | File |
|-----------|-----------|------|
| `GlobalType.end` | `GlobalType::End` | `rust/types/src/global.rs` |
| `GlobalType.comm p q bs` | `GlobalType::Comm { sender, receiver, branches }` | `rust/types/src/global.rs` |
| `GlobalType.rec t G` | `GlobalType::Mu { var, body }` | `rust/types/src/global.rs` |
| `GlobalType.var t` | `GlobalType::Var(String)` | `rust/types/src/global.rs` |
| `LocalTypeR.end` | `LocalTypeR::End` | `rust/types/src/local.rs` |
| `LocalTypeR.send q bs` | `LocalTypeR::Send { partner, branches }` | `rust/types/src/local.rs` |
| `LocalTypeR.recv p bs` | `LocalTypeR::Recv { partner, branches }` | `rust/types/src/local.rs` |
| `LocalTypeR.rec t T` | `LocalTypeR::Mu { var, body }` | `rust/types/src/local.rs` |
| `LocalTypeR.var t` | `LocalTypeR::Var(String)` | `rust/types/src/local.rs` |
| `PayloadSort.unit` | `PayloadSort::Unit` | `rust/types/src/global.rs` |
| `Label` | `Label { name, sort }` | `rust/types/src/global.rs` |

The Rust variant names match Lean constructor names. Field names are consistent across both implementations.

## Extension Points

The architecture supports extension at several points.

### Adding New Code Generation Targets

Implement generators in `rust/choreography/src/compiler/codegen/` that work with the choreography AST or `LocalType`.

```rust
pub fn generate_my_target(lt: &LocalType) -> MyOutput {
    // implementation
}
```

The function receives a local type and produces output in the target format. Follow existing generators as examples.

### Custom Projection Strategies

Extend projection in `rust/theory/src/projection.rs`.

```rust
pub fn project_with_strategy(
    global: &GlobalType,
    role: &str,
    strategy: ProjectionStrategy,
) -> Result<LocalTypeR, ProjectionError> {
    // implementation
}
```

The strategy parameter controls projection behavior. This enables alternative projection algorithms.

### Lean Integration Extensions

Extend the lean-bridge for custom validation.

```rust
impl Validator {
    pub fn my_custom_validation(
        &self,
        rust_type: &LocalTypeR,
        lean_result: &Value,
    ) -> ValidationResult {
        // implementation
    }
}
```

Custom validation methods can implement domain-specific comparison rules. See [Lean-Rust Bridge](15_lean_rust_bridge.md) for more details.
