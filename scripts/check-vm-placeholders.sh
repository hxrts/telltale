#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE_FILE="${ROOT_DIR}/scripts/baselines/vm_placeholders.allowlist"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

if [[ ! -f "${BASELINE_FILE}" ]]; then
  echo "error: missing baseline file ${BASELINE_FILE}" >&2
  exit 2
fi

PATTERN='(?i)\b(?:TODO|FIXME|TBD|placeholder|stub|unimplemented|WIP)\b'

# Limit to executable VM modules (not proofs).
CURRENT_HITS="$({
  rg -n --pcre2 "${PATTERN}" \
    "${ROOT_DIR}/lean/Runtime/VM/Model" \
    "${ROOT_DIR}/lean/Runtime/VM/Semantics" \
    "${ROOT_DIR}/lean/Runtime/VM/Runtime" \
    "${ROOT_DIR}/lean/Runtime/VM/API.lean" \
    -g '*.lean' || true
} | sed "s#${ROOT_DIR}/##" | sort -u)"

BASELINE_HITS="$(sed '/^\s*#/d;/^\s*$/d' "${BASELINE_FILE}")"
if [[ -n "${BASELINE_HITS}" ]]; then
  echo "error: ${BASELINE_FILE} must be empty in strict-conformance mode." >&2
  echo "Remove allowlisted markers and clear the baseline file." >&2
  exit 1
fi

if [[ -n "${CURRENT_HITS}" ]]; then
  echo "error: found placeholder/todo/stub markers in executable VM modules:" >&2
  printf '%s\n' "${CURRENT_HITS}" >&2
  echo "" >&2
  echo "Remove markers from executable VM modules." >&2
  exit 1
fi

PROOF_IMPORT_HITS="$(
  rg -n --pcre2 '^\s*import\s+Runtime\.Proofs(\.|$)' \
    "${ROOT_DIR}/lean/Runtime/VM/Model" \
    "${ROOT_DIR}/lean/Runtime/VM/Semantics" \
    "${ROOT_DIR}/lean/Runtime/VM/Runtime" \
    "${ROOT_DIR}/lean/Runtime/VM/API.lean" \
    -g '*.lean' || true
)"

if [[ -n "${PROOF_IMPORT_HITS}" ]]; then
  echo "error: executable Lean VM modules must not import proof-layer Runtime.Proofs modules:" >&2
  printf '%s\n' "${PROOF_IMPORT_HITS}" | sed "s#${ROOT_DIR}/##" >&2
  exit 1
fi

echo "VM placeholder/stub check passed with zero executable markers."
