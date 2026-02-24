# Telltale

This repo contains three related projects. A functional Rust library for writing composable multiparty session-typed choreographies. It includes a extensible Lean proof system. And a paper + artifact supplement for a three-paper MPST series detailing theoretical contributions.

## For Reviewers

Run `just artifact-check`. Then inspect `paper/artifact_manifest.json` and [Artifact Reproduction Guide](ARTIFACT.md).

## Project Surfaces

### 1) Rust Library

The Rust project implements the operational model from the paper series. It includes the choreography pipeline, VM runtime behavior, admission checks, and simulation tooling.

- Choreographic DSL with projection and compiler pipeline.
- VM execution model for asynchronous buffered protocols.
- Runtime theorem-pack and capability-gated admission interfaces.
- Reconfiguration-facing checks for link, delegation, and transition steps.
- Simulation and cross-target conformance tooling for Rust VM and Lean reference traces.

Main code is in `rust/`. Workspace configuration is in `Cargo.toml`. A typical health check is `cargo test --workspace --all-targets --all-features`.

### 2) Lean Proof System

The Lean project is an active mechanized proof stack. It covers session foundations, semantics, protocol coherence, runtime adequacy, and bridge theorems. Main code is in `lean/`. The toolchain pin is `lean-toolchain`. A typical proof-facing gate is `just verify-protocols`.

### 3) Paper + Artifact Supplement

The paper project contains the three manuscripts and submission-focused reproducibility tooling. The sources are `paper/paper1.tex`, `paper/paper2.tex`, and `paper/paper3.tex`. The reproducibility guide is [Artifact Reproduction Guide](ARTIFACT.md). Citation metadata is in `paper/CITATION.cff`.

## Quick Commands

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
| `paper/` | Paper sources, supplement metadata, citation |
| `scripts/` | Verification/repro automation scripts |
| `docs/` | Extended technical documentation |

## Reproducibility and Submission Metadata

Use [Artifact Reproduction Guide](ARTIFACT.md) for the end-to-end supplement workflow and expected outputs. Set archival DOI metadata in `paper/artifact_metadata.env`. Generated provenance and hash output is written to `paper/artifact_manifest.json`. Citation metadata for the supplement is in `paper/CITATION.cff`.

## Build Environment

Nix is the recommended environment (`flake.nix`) for aligned toolchains and paper build dependencies.

## License

Licensed under the MIT [license](LICENSE).
