# Telltale

This repo contains three related projects. A Rust library for writing composable multiparty session-typed choreographies, an extensible Lean proof system, and a three-paper series describing MPST theoretical contributions.

[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/hxrts/telltale)

## For Reviewers

Run `just artifact-check`. Then inspect `papers/artifact_manifest.json` and [Artifact Reproduction Guide](papers/ARTIFACT.md).

## Project Surfaces

### 1. Rust Library

The `rust/` project implements the operational model from the paper series. Protocols are written once with the `tell!` macro and projected to local session types, typed effect interfaces, and authority/evidence constructs for each role.

- Protocol machine for deterministic execution with session type enforcement
- Declared effect boundaries where host logic implements generated Rust traits
- Typed failure, timeout, and cancellation paths with explicit evidence flow
- Native and WASM targets from the same protocol specification
- Simulation, replay, and cross-target conformance tooling against Lean reference traces

### 2. Lean Proof System

The Lean project is an active mechanized proof stack. It covers session foundations, semantics, protocol coherence, runtime adequacy, and bridge theorems. Main code is in `lean/`. The toolchain pin is `lean-toolchain`. A typical proof-facing gate is `just verify-protocols`.

### 3. Papers + Artifact Supplement

The three papers establish a mechanized metatheory for asynchronous buffered multiparty session types. Paper 1 defines an operational coherence invariant enabling compositional preservation proofs. Paper 2 adds quantitative Lyapunov bounds and decidability results. Paper 3 proves a harmony theorem for dynamic reconfiguration. Together they connect choreographic specifications to protocol-machine runtime adherence. All results are mechanized in Lean 4.

The `papers/` directory contains manuscripts and [reproducibility documentation](papers/ARTIFACT.md). PDFs: [Paper 1](https://hxrts.com/telltale/papers/paper1.pdf), [Paper 2](https://hxrts.com/telltale/papers/paper2.pdf), [Paper 3](https://hxrts.com/telltale/papers/paper3.pdf). Citation metadata is in `papers/CITATION.cff`.

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
