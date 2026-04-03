#!/usr/bin/env bash
# Validate docs/703_rust_lean_parity.md has required sections, then
# delegate to cross-runtime-parity.sh --types for structural checks.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

PARITY_DOC="docs/703_rust_lean_parity.md"

# ── Structural Checks ────────────────────────────────────────────────

if [[ ! -f "${PARITY_DOC}" ]]; then
  echo "[parity-ledger] missing ${PARITY_DOC}" >&2
  exit 1
fi

# Require the deviation registry heading
if ! rg -q "^### Deviation Registry" "${PARITY_DOC}"; then
  echo "[parity-ledger] ${PARITY_DOC} is missing '### Deviation Registry'" >&2
  exit 1
fi

# Require the deviation registry table header
if ! rg -q "^\| ID \| Status \| Owner \| Revisit \| Summary \|" "${PARITY_DOC}"; then
  echo "[parity-ledger] ${PARITY_DOC} is missing the deviation registry table header" >&2
  exit 1
fi

# ── Delegate Type Parity ──────────────────────────────────────────────

./scripts/check/cross-runtime-parity.sh --types
