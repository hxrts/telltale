# CLAUDE.md

This file provides guidance to Claude Code when working with code in this repository.

## Project Overview

Telltale is a session-typed execution system for protocol-critical concurrent and distributed programs. It is designed as a conservation system over protocol semantics: all semantically meaningful behavior is expressed in terms of six conserved quantities (evidence, authority, identity, commitment, structure, premise), and all other behavior is erased or reduced to those quantities.

The system enables writing distributed protocols from a global viewpoint with automatic projection to local session types for each participant. Multiparty session types provide compile-time safety guarantees. The protocol machine is a deterministic small-step reducer that commits all protocol-visible truth. Typed effect interfaces form the operational vocabulary between the protocol machine and the world.

Protocol-critical capability semantics are first class in the runtime/model
boundary. The canonical taxonomy is:

- admission
- ownership
- evidence
- transition

This taxonomy is intentionally narrow. It covers protocol-critical authority,
finalization, handoff, and reconfiguration semantics. It does not cover general
host application authorization.

The Lean 4 formalization provides mechanized proofs of preservation, progress, coherence, and harmony for asynchronous buffered multiparty session types. See `lean/CODE_MAP.md` for generated metrics.

## Parity Policy

For protocol-machine policy/data encodings, the project follows:

- spec-first for shape
- runtime-first for justified execution details

Lean/Rust mismatches must be documented as justified breaks in `docs/703_rust_lean_parity.md` (Deviation Registry section) before merge.

### Flow Policy Serialization Boundary

`FlowPolicy::predicate` (Rust) / `FlowPolicy.predicate` (Lean) is intentionally runtime-only.
Closure-backed predicates are not serializable and must not be used in artifacts that cross the Lean/Rust bridge.
For serialized configs and parity artifacts, use `FlowPolicy::PredicateExpr` / `FlowPolicy.predicateExpr`.

## justfile Commands

The `justfile` is the primary command interface. Run `just --list` to see all available commands.

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
cargo test --package telltale-runtime test_name

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
just telltale-lean-check                # Basic verification (3 roles)
just telltale-lean-check-extended       # Extended scenarios
just telltale-lean-check-failing        # Intentional failure test
just verify-lean-full                   # Full Lean build (nightly)
just verify-lean-protocol-machine-targets  # Fast CI: protocol-machine architecture only

# Check for escape hatches
just escape                             # Report sorry/axiom/unsafe counts
```

### Verification Lanes

```bash
# Protocol verification
just verify-protocols              # Protocol-machine correspondence + invariants + schema

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
| `telltale-macros` | `rust/macros/` | Procedural macros (`tell!`, `session`, `Role`, `Roles`, `Message`) |
| `telltale-language` | `rust/language/` | DSL parser (Pest grammar, layout preprocessor), AST, projection, codegen |
| `telltale-runtime` | `rust/runtime/` | Effect handlers, formatter binary, topology, heap, testing infrastructure |
| `telltale-theory` | `rust/theory/` | Session type algorithms (projection, merge, duality, sync/async subtyping, bounded recursion) |
| `telltale-machine` | `rust/machine/` | Protocol machine execution engine (single source of truth for scheduling) |
| `telltale-simulator` | `rust/simulator/` | Protocol-machine-backed simulation with deterministic middleware (network, faults, properties) |
| `telltale-bridge` | `rust/bridge/` | Lean interop with JSON export/import, validation, choreography exporter |
| `telltale-transport` | `rust/transport/` | Production transport integration layer for runtime/choreography execution |
| `telltale-lints` | `rust/lints/` | Custom lint checks for architecture and style enforcement |

## Lean Codebase Structure

The Lean formalization is in the `lean/` directory. See `lean/CODE_MAP.md` for generated metrics and detailed file-by-file documentation.

| Library | Purpose |
|---------|---------|
| SessionTypes | Global/local type definitions, de Bruijn indices, participation |
| SessionCoTypes | Coinductive theory (EQ2, bisimulation, duality, async subtyping) |
| Choreography | Projection from global to local types, harmony correctness |
| Semantics | Operational semantics, typing, determinism, deadlock freedom |
| Protocol | Async buffered MPST: coherence, preservation, monitoring, deployment |
| Runtime | Protocol machine, Iris separation logic backend, WP rules, adequacy |
| Classical | Transported theorems (Foster-Lyapunov, mixing times, LDP) |
| ClassicalAnalysis | Real-analysis-backed concrete models used by classical transport |
| Distributed | Distributed assumptions, FLP/CAP theorem families |
| IrisExtraction | Iris ghost-state/program-logic extraction support modules |

Key entry points: `lean/lakefile.lean` (build configuration), `lean/CODE_MAP.md` (complete module documentation).

## Test Patterns

Tests use three patterns depending on platform requirements:

| Pattern | Use When |
|---------|----------|
| `#[wasm_bindgen_test(unsupported = test)]` | Sync tests that work on both native and WASM |
| `#[cfg(not(target_arch = "wasm32"))]` + `#[test]` | Tests requiring native-only features (proptest, tokio) |
| `#[cfg(target_arch = "wasm32")]` + `#[wasm_bindgen_test]` | Tests requiring WASM-only APIs |

Golden file tests compare Rust/Lean outputs without requiring Lean build. Run `just test-golden` for fast CI, `just regenerate-golden` to update from Lean.

Verification lanes: CI uses `just verify-track-a` (behavior preservation) and `just verify-track-b` (semantic alignment) as gates.

## Key Concepts

`tell!` is the canonical DSL entrypoint. `.tell` is the source file extension.

```rust
use telltale::tell;

tell! {
    protocol Simple =
        roles Alice, Bob
        Alice -> Bob : Message
}
```

Session types encode protocol states as Rust types. `Send<'q, Q, R, L, S>` encodes sending label L from role Q to R with continuation S.

The protocol machine (`ProtocolMachine`) is the single execution engine that commits all protocol-visible truth. `ProtocolMachineKernel` owns the step contract. Simulation layers are deterministic middleware wrapped around the protocol machine via `telltale-simulator`.

Effect handlers: `ChoreoHandler` (async, typed) abstracts choreography-layer transport. `EffectHandler` (sync) is the protocol-machine host integration boundary.

Coherence is the per-edge invariant that makes projection well-defined. `EdgeCoherent` checks buffer/type alignment without global re-derivation.

Projection transforms global choreographies to local session types (`rust/language/src/compiler/projection.rs`, `lean/Choreography/Projection/`).

Content addressing assigns cryptographic identities to protocol artifacts (`rust/types/src/content_id.rs`).

Conservation framework: the six conserved properties (evidence, authority, identity, commitment, structure, premise) organize all protocol-critical behavior. See `docs/102_conservation_framework.md`.

Capability model: protocol-critical capability semantics use the four-class
taxonomy above. Finalization is explicit via `ProtocolMachineFinalization`,
`FinalizationPath`, `FinalizationReadClass`, and `FinalizationStage`. See
`docs/601_capability_model.md`.

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

- `docs/105_code_organization.md`: Crate and module structure
- `docs/202_choreographic_dsl.md`: DSL syntax reference
- `docs/301_effect_handlers.md`: Effect system guide
- `docs/401_protocol_machine_architecture.md`: Protocol machine architecture
- `docs/703_rust_lean_parity.md`: Lean/Rust parity policy and deviation registry
- `docs/701_lean_verification.md`: Formal verification pipeline
- `docs/603_protocol_authority_scope.md`: Protocol authority boundary classification
- `docs/604_authority_language_surface.md`: Authority and failure DSL constructs
- `docs/605_protocol_authority_evidence.md`: Evidence and typed outcome semantics
- `docs/102_conservation_framework.md`: Conservation framework and design philosophy

The Lean codebase has its own documentation at `lean/CODE_MAP.md`.

## Local Working Directory

The `work/` directory is not tracked in git.

It contains style guides: `work/style_guide_rust.md`, `work/style_guide_lean.md`, `work/style_guide_docs.md`

These files are for local development tracking and should not be committed.
