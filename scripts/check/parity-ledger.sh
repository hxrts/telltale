#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

PARITY_DOC="docs/19_rust_lean_parity.md"

if [[ ! -f "${PARITY_DOC}" ]]; then
  echo "[parity-ledger] missing ${PARITY_DOC}" >&2
  exit 1
fi

if ! rg -q "^### Deviation Registry" "${PARITY_DOC}"; then
  echo "[parity-ledger] ${PARITY_DOC} is missing '### Deviation Registry'" >&2
  exit 1
fi

if ! rg -q "^\| ID \| Status \| Owner \| Revisit \| Summary \|" "${PARITY_DOC}"; then
  echo "[parity-ledger] ${PARITY_DOC} is missing the deviation registry table header" >&2
  exit 1
fi

./scripts/check/parity.sh --types
