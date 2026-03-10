# Artifact Reproduction Guide

This repository ships a publication supplement for the three-paper MPST series in `papers/`.

## Prerequisites

- Nix environment (`nix develop`) or equivalent local toolchain with:
  - Lean toolchain from `lean-toolchain`
  - Rust toolchain from `rust-toolchain`
  - `just`, `lake`, `pdflatex`
- Typical runtime profile:
  - 4+ CPU cores
  - 16 GB RAM
  - ~10 GB free disk

## One-Command Reproduction

Run:

```bash
just artifact-check
```

This command:

1. Synchronizes paper reproducibility rows (pinned commit, DOI value, Lean stats).
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
