# CLAUDE.md

This file provides guidance to Claude Code when working with code in this repository.

## Project Overview

Telltale is a Rust framework for choreographic programming with session types, paired with formal verification in Lean 4. The project enables writing distributed protocols from a global viewpoint with automatic projection to local session types for each participant. Multiparty session types provide compile-time safety guarantees. An effect handler system decouples protocol logic from transport implementation.

The Lean formalization currently covers ~624 core-library files and ~127k lines (see generated metrics in `lean/CODE_MAP.md`) and provides mechanized proofs of preservation, progress, coherence, and harmony for asynchronous buffered multiparty session types.

## VM Parity Policy

For VM policy/data encodings, the project follows:

- spec-first for shape,
- runtime-first for justified execution details.

Lean/Rust mismatches must be documented as justified breaks in `docs/19_rust_lean_parity.md` (Deviation Registry section) before merge.

### Flow Policy Serialization Boundary

`FlowPolicy::predicate` (Rust) / `FlowPolicy.predicate` (Lean) is intentionally runtime-only.
Closure-backed predicates are not serializable and must not be used in artifacts that cross the Lean/Rust bridge.
For serialized configs and parity artifacts, use `FlowPolicy::PredicateExpr` / `FlowPolicy.predicateExpr`.

## Justfile Commands

The `Justfile` is the primary command interface. Run `just --list` to see all available commands.

### Quick Reference

```bash
just ci-dry-run              # Run all CI checks locally
just lint                    # Comprehensive Rust style check
just lint-quick              # Quick format + clippy only
just book                    # Build documentation book
just escape                  # Check Lean for proof holes (sorry, axiom, etc.)
```

### Rust Commands

```bash
# Build and test
cargo build --workspace --all-targets --all-features
cargo test --workspace --all-targets --all-features
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo fmt --all -- --check

# Single package test
cargo test --package telltale-choreography test_name

# WASM
just wasm-check              # Check WASM compilation
just wasm-build              # Build WASM example with wasm-pack
just wasm-test               # Run WASM tests (requires browser)

# Benchmarks
just bench-check             # Check benchmark compilation

# Choreography formatter
just choreo-fmt <files>      # Format .tell files (stdout)
just choreo-fmt-write <files> # Format .tell files (in-place)

# Scaffolding and simulation
just effect-scaffold              # Generate EffectHandler stubs and harness templates
just sim-run <config>             # Run simulator harness config
just sim-run-out <config> <out>   # Run simulator harness with JSON output
```

### Lean Commands

```bash
# Enter Nix shell first
nix develop

# Build Lean project (from repo root)
lake --dir lean build

# Verification pipelines
just telltale-lean-check           # Basic verification (3 roles)
just telltale-lean-check-extended  # Extended scenarios
just telltale-lean-check-failing   # Intentional failure test
just verify-lean-full              # Full Lean build (nightly)
just verify-lean-vm-targets        # Fast CI: VM architecture only

# Check for escape hatches
just escape                        # Report sorry/axiom/unsafe counts
```

### Verification Lanes

```bash
# Protocol verification
just verify-protocols              # VM correspondence + invariants + schema

# CI gates
just verify-track-a                # Naming/API changes preserve behavior
just verify-track-b                # Semantic alignment acceptance

# Cross-platform
just verify-cross-target-matrix    # Threaded + Lean + WASM equivalence
just verify-composition-stress     # Concurrency stress tests
just verify-properties             # Property-based tests

# Golden files
just test-golden                   # Fast equivalence tests (no Lean)
just regenerate-golden             # Regenerate golden files from Lean
just check-golden-drift            # Check if golden files are outdated
```

### Architecture Checks

```bash
just check-arch-rust               # Rust style/pattern checker
just check-arch-lean               # Lean style/pattern checker
just check-aura-borrowed-lints     # Session ingress, time-domain, docs, inventory, macro boundaries
just check-docs-semantic-drift     # Backticked commands, paths, crates, qualified symbols
just check-macro-boundaries        # Focused trybuild boundary suite
just check-parity                  # Consolidated Lean/Rust parity checks
just check-capability-gates        # Byzantine, delegation, envelope, failure, contracts gates
just check-ownership-contracts     # Ownership-contract assertions and delegation/replay
just sync-lean-metrics             # Update Lean metrics in docs
just check-lean-metrics            # Verify metrics are fresh
```

## Rust Workspace Structure

Rust workspace crates are split between the repo root (`telltale`) and the `rust/` directory.

| Crate | Path | Purpose |
|-------|------|---------|
| `telltale` | `rust/src/` | Facade crate with session types (`Send`, `Receive`, `Select`, `Branch`, `End`) and async channel abstractions |
| `telltale-types` | `rust/types/` | Core types (`GlobalType`, `LocalTypeR`, `Label`) matching Lean definitions with content addressing |
| `telltale-macros` | `rust/macros/` | Procedural macros (`choreography!`, `session`, `Role`, `Roles`, `Message`) |
| `telltale-choreography` | `rust/choreography/` | DSL parser, projection, effect handlers, simulation, topology, effect scaffold |
| `telltale-theory` | `rust/theory/` | Session type algorithms (projection, merge, duality, sync/async subtyping, bounded recursion) |
| `telltale-machine` | `rust/machine/` | Bytecode VM execution engine (single source of truth for scheduling) |
| `telltale-simulator` | `rust/simulator/` | VM-backed simulation with deterministic middleware (network, faults, properties) |
| `telltale-lean-bridge` | `rust/lean-bridge/` | Lean interop with JSON export/import, validation, choreography exporter |
| `telltale-transport` | `rust/transport/` | Production transport integration layer for runtime/choreography execution |
| `telltale-lint-checks` | `rust/lint-checks/` | Custom lint checks for architecture and style enforcement |

### Choreography Crate Structure (`rust/choreography/src/`)

- **`ast/`**: AST types (`Choreography`, `Protocol`, `Role`, `MessageType`), validation
- **`bin/`**: Formatter binary (`choreo_fmt`)
- **`compiler/`**: Pest parser (`choreography.pest`), projection, codegen, diagnostics
- **`effects/`**: Effect algebra (`Program`), handlers (`InMemoryHandler`, `TelltaleHandler`), middleware
- **`extensions/`**: Protocol extensions (discovery, timeout)
- **`topology/`**: Deployment configuration, transport abstraction
- **`runtime/`**: Platform abstraction (tokio/WASM), spawn utilities
- **`heap/`**: Resource heap with Merkle proofs
- **`testing/`**: Test infrastructure (clock, envelope, observer, state machine, transport)

## Lean Codebase Structure

The Lean formalization is in the `lean/` directory. See `lean/CODE_MAP.md` for detailed file-by-file documentation.

| Library | Lines | Purpose |
|---------|------:|---------|
| SessionTypes | 9,967 | Global/local type definitions, de Bruijn indices, participation |
| SessionCoTypes | 16,302 | Coinductive theory (EQ2, bisimulation, duality, async subtyping) |
| Choreography | 19,308 | Projection from global to local types, harmony correctness |
| Semantics | 2,359 | Operational semantics, typing, determinism, deadlock freedom |
| Protocol | 40,077 | Async buffered MPST: coherence, preservation, monitoring, deployment |
| Runtime | 28,283 | VM definition, Iris separation logic backend, WP rules, adequacy |
| Classical | 2,193 | Transported theorems (Foster-Lyapunov, mixing times, LDP) |
| ClassicalAnalysis | 1,128 | Real-analysis-backed concrete models used by classical transport |
| Distributed | 7,266 | Distributed assumptions, FLP/CAP theorem families |
| IrisExtraction | 830 | Iris ghost-state/program-logic extraction support modules |

**Key entry points:**
- `lean/lakefile.lean` — Build configuration
- `lean/` — Top-level facade imports for each library
- `lean/CODE_MAP.md` — Complete module documentation

## Test Patterns

Tests use three patterns depending on platform requirements:

| Pattern | Use When |
|---------|----------|
| `#[wasm_bindgen_test(unsupported = test)]` | Sync tests that work on both native and WASM |
| `#[cfg(not(target_arch = "wasm32"))]` + `#[test]` | Tests requiring native-only features (proptest, tokio) |
| `#[cfg(target_arch = "wasm32")]` + `#[wasm_bindgen_test]` | Tests requiring WASM-only APIs |

**Golden file tests:** Compare Rust/Lean outputs without requiring Lean build. Run `just test-golden` for fast CI, `just regenerate-golden` to update from Lean.

**Verification lanes:** CI uses `just verify-track-a` (behavior preservation) and `just verify-track-b` (semantic alignment) as gates.

## Key Concepts

**Session Types**: Protocol states as Rust types. `Send<'q, Q, R, L, S>` encodes sending label L from role Q to R with continuation S.

**Choreography DSL**: Global protocol specification syntax:
```
choreography! {
    protocol Simple = {
        roles Alice, Bob
        Alice -> Bob : Message
    }
}
```

**Effect Handlers**: `ChoreoHandler` (async, typed) abstracts transport. The VM has its own synchronous `EffectHandler` for simulation/runtime integration.

**Coherence**: The per-edge invariant that makes projection well-defined. `EdgeCoherent` checks buffer/type alignment without global re-derivation.

**Consume Function**: Recursive buffer-compatibility check with `consume_append` (send) and `consume_cons` (receive) lemmas.

**Projection**: Transforms global choreographies to local session types (`rust/choreography/src/compiler/projection.rs`, `lean/Choreography/Projection/`).

**VM Execution**: The VM is the single execution engine. Simulation layers are deterministic middleware wrapped around the VM.

**Content Addressing**: Cryptographic identities for protocol artifacts (`rust/types/src/content_id.rs`).

## Development Environment

```bash
nix develop
```

This enters a development shell with:
- Rust toolchain + wasm-pack
- Lean 4 (v4.26.0) + Lake
- mdbook for documentation
- Node.js for WASM tests

## Documentation

The `docs/` directory contains mdbook documentation:

- `docs/04_code_organization.md`: Crate and module structure
- `docs/06_choreographic_dsl.md`: DSL syntax reference
- `docs/09_effect_handlers.md`: Effect system guide
- `docs/12_vm_architecture.md`: Bytecode VM architecture
- `docs/19_rust_lean_parity.md`: Lean/Rust parity policy and deviation registry
- `docs/23_lean_verification.md`: Formal verification pipeline
- `docs/33_protocol_authority_scope.md`: Protocol authority boundary classification
- `docs/34_authority_language_surface.md`: Authority and failure DSL constructs
- `docs/35_protocol_authority_evidence.md`: Evidence and typed outcome semantics

The Lean codebase has its own documentation at `lean/CODE_MAP.md`.

## Local Working Directory

The `work/` directory is **intentionally not tracked in git**.

It contains style guides: `work/style_guide_rust.md`, `work/style_guide_lean.md`, `work/style_guide_docs.md`

These files are for local development tracking and should not be committed.
