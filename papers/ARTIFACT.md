# Artifact Reproduction

This repository ships a publication supplement for the three-paper MPST series in `papers/`.

## Prerequisites

- Nix environment (`nix develop`) or equivalent local toolchain with:
  - Lean toolchain from `lean/lean-toolchain` (`leanprover/lean4:v4.35.0`); the
    `justfile` exports it as `ELAN_TOOLCHAIN`, so recipes use it regardless of the shell default
  - Rust toolchain from `rust-toolchain` (1.95.0)
  - `just`, `lake`, `pdflatex`, `rg`
- Typical runtime profile:
  - 4+ CPU cores
  - 16 GB RAM
  - ~10 GB free disk

## Lean Dependency Pins

Pinned in `lean/lakefile.lean` and locked in `lean/lake-manifest.json`:

| Dependency | Source | Pin |
|------------|--------|-----|
| Lean | `leanprover/lean4` | `v4.35.0` |
| Mathlib | `leanprover-community/mathlib4` | `56a005855ea17e0b0958f73ec801ae140b0a1679` (Mathlib v4.35.0) |
| Iris | `leanprover-community/iris-lean` (upstream) | `ac6e3745f735496e6db0592b17f78a4f9dbba384` |
| paco-lean | `hxrts/paco-lean` | `v0.2.0` |

Iris now comes from upstream `leanprover-community/iris-lean`, not the earlier `hxrts` fork.
Fetch prebuilt Mathlib oleans with `lake --dir lean exe cache get` before the first build.

## Building the Lean Development

```bash
just verify-lean-full
```

Every Lean build recipe in the `justfile` goes through `tools/run_lean_build.py`
(`python3 tools/run_lean_build.py --label <label> -- lake --dir lean build ...`). If a
sibling `lean-builder` checkout is present (`../lean-builder`, overridable via
`LEAN_BUILDER_BUILD_WRAPPER` / `LEAN_BUILDER_BIN`), the launcher uses its shared
build-budget coordinator and cache. That coordinator is optional. Without it, the launcher
prints a "coordination degraded" notice and runs `lake` under a local lock with
`LEAN_NUM_THREADS` workers (default 3). Running `lake --dir lean build` directly also works.

## One-Command Reproduction

Run:

```bash
just artifact-check
```

This command:

1. Synchronizes paper reproducibility rows (pinned commit, DOI value, Lean stats) via
   `scripts/ops/paper-repro-rows.sh`.
2. Verifies reproducibility rows are up to date.
3. Runs paper-facing checks (`just escape`, `just verify-protocols`).
4. Builds all three paper PDFs (`just paper`).
5. Generates `papers/artifact_manifest.json`.

## Expected Outputs

- PDFs:
  - `papers/build/paper1.pdf`
  - `papers/build/paper2.pdf`
  - `papers/build/paper3.pdf`
- Logs:
  - `artifacts/papers/*.log`
- Manifest:
  - `papers/artifact_manifest.json`

## Supplement Integrity

`papers/artifact_manifest.json` records:

- exact repository commit,
- toolchain versions,
- SHA-256 hashes for generated PDFs,
- SHA-256 hashes for artifact-check logs.

## What the Lean Artifact Establishes

The Lean development contains no axioms and no `sorry`. Several paper-level
results are mechanized only conditionally. The papers state these conditions where the results are claimed (in paper 3, in its mechanization-status
paragraphs):

- Envelope soundness and realizability, exchange normalization, spatial and
  capability monotonicity, the compositional envelope property and recovery-action
  safety are explicit `assumed*` premises (`lean/Runtime/Adequacy/EnvelopeCore/`).
  Envelope maximality is definitional in its mechanized form.
- Protocol-machine adherence is taken from a supplied hypothesis bundle.
  Trace adequacy and message conservation are proved for the real `stepSend` and
  `stepReceive` in FIFO buffer mode. Iris adequacy (`session_vm_wp_invariance`) is
  upstream iris-lean `wp_invariance` with its weakest-precondition premise as a hypothesis.
- `compile_refines` covers linear (single-branch, non-recursive) local types only.
- Projection harmony, subject reduction and deadlock freedom cover
  head-communication steps only.
- Theorem-pack capability bits, inventory flags and release gates are presence
  flags for supplied evidence objects. Rust envelope admission accepts a theorem-pack
  key only when a Lean-produced evidence inventory marks it as supplied.
- Rust/Lean parity is test-based. No Lean statement relates the Lean semantics to Rust behaviour.
