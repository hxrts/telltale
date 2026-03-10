# Telltale

This repo contains three related projects. A Rust library for writing composable multiparty session-typed choreographies, an extensible Lean proof system, and a three-paper series describing MPST theoretical contributions.

[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/hxrts/telltale)

## For Reviewers

Run `just artifact-check`. Then inspect `papers/artifact_manifest.json` and [Artifact Reproduction Guide](papers/ARTIFACT.md).

## Project Surfaces

### 1. Rust Library

The Rust project implements the operational model from the paper series. It includes the choreography pipeline, VM runtime behavior, admission checks, and simulation tooling.

- Choreographic DSL with projection and compiler pipeline
- Virtual machine for safe execution of asynchronous buffered protocols
- Runtime theorem-pack and capability-guarded admission interfaces
- Reconfiguration-facing checks for link, delegation, and transition steps
- Simulation and cross-target conformance tooling for Rust VM and Lean reference traces

Main code is in `rust/`. Workspace configuration is in `Cargo.toml`. A typical health check is `cargo test --workspace --all-targets --all-features`.

### 2. Lean Proof System

The Lean project is an active mechanized proof stack. It covers session foundations, semantics, protocol coherence, runtime adequacy, and bridge theorems. Main code is in `lean/`. The toolchain pin is `lean-toolchain`. A typical proof-facing gate is `just verify-protocols`.

### 3. Paper + Artifact Supplement

The paper project contains the three manuscripts and submission-focused reproducibility tooling. PDFs: [Paper 1](https://hxrts.com/telltale/papers/paper1.pdf), [Paper 2](https://hxrts.com/telltale/papers/paper2.pdf), [Paper 3](https://hxrts.com/telltale/papers/paper3.pdf). The reproducibility guide is [Artifact Reproduction Guide](papers/ARTIFACT.md). Citation metadata is in `papers/CITATION.cff`.

## Quick Start

```bash
# Rust library health
cargo test --workspace --all-targets --all-features

# Lean/proof-facing protocol verification lane
just verify-protocols

# Paper supplement reproducibility + paper build + manifest
just artifact-check
```

This command set validates the Rust library, proof-facing protocol checks, and paper supplement workflow.

## Repository Layout

| Path | Purpose |
|---|---|
| `rust/` | Rust library and runtime system |
| `lean/` | Lean proof development and verification stack |
| `papers/` | Paper sources, supplement metadata, citation |
| `scripts/` | Verification/repro automation scripts |
| `docs/` | Extended technical documentation |

## License

Licensed under the MIT [license](LICENSE).
