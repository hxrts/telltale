# Telltale

This repo contains three related projects. A Rust library for writing composable multiparty session-typed choreographies, an extensible Lean proof system, and a three-paper series describing MPST theoretical contributions.

## For Reviewers

Run `just artifact-check`. Then inspect `papers/artifact_manifest.json` and [Artifact Reproduction Guide](papers/ARTIFACT.md).

## Project Surfaces

### 1. Rust Library

The `rust/` project implements the operational model from the paper series. Protocols are written once with the `tell!` macro and projected to local session types, typed effect interfaces, and authority/evidence constructs for each role. The DSL features the following features:

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

## Formal Verification

Telltale is formally verified for the declared shipped surface documented in
[docs/902_verification_inventory.md](docs/902_verification_inventory.md), under the listed public assumptions and trusted base.

The claim covers the Lean semantics and theorems, the theorem-defined Rust↔Lean core protocol-machine runtime correspondence, the shipped first-party handler and transport contract boundary, and the shipped first-party crate artifacts through the audited artifact-correspondence pipeline. Compiler, macro, and third-party integration paths are excluded unless the verification inventory says otherwise.

## Quick Start

```bash
# Development shell
just develop

# Rust library health
just test-workspace

# Lean/proof-facing protocol verification lane
just verify-protocols

# Paper supplement reproducibility + paper build + manifest
just artifact-check
```

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

## Rust compiler selection

Canonical Rust development and CI select exact Rust 1.99.1 in Nix,
`rust-toolchain` and hosted compiler jobs. Scoped Cargo/Clippy dispatch keeps
Cargo-home plugins from changing that selection. The older manifest MSRV is
a separate compatibility claim; current-toolchain validation does not prove
it. Lean retains its independent `lean-toolchain` pin.

### Shared local Rust compiler cache

The Nix shell exposes sccache with Aura's existing local store
(`~/.cache/aura-sccache`) and one shared 10G budget. Explicit `SCCACHE_DIR` and
`SCCACHE_CACHE_SIZE` settings are preserved. Each checkout retains its own Cargo
target. Shell entry performs no compilation or cache-server startup.
`TELLTALE_NO_SCCACHE=1` opts out at shell entry or per Cargo invocation.

Ordinary builds and canonical acceptance are nonincremental. The dev profile
sets `incremental = false`, and the Nix shell defaults `CARGO_INCREMENTAL=0` for
excluded tooling manifests. Acceptance runs set `CARGO_INCREMENTAL=0`
explicitly. `CARGO_INCREMENTAL=1` is the edit/test opt-in. It bypasses the
selected sccache wrapper for that invocation and preserves unrelated caller
wrappers. Incremental and linker-invoking Rust units are not cache hits.
Matching compiler versions or directories alone do not prove cross-repository
reuse. Measure actual matching-unit hits separately.
