#!/usr/bin/env bash
# Audit distributed theorem packs for proof-completion blockers.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ALLOWLIST_FILE="${ROOT_DIR}/scripts/lean/distributed-proof-audit-allowlist.txt"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

SCOPES=(
  "${ROOT_DIR}/lean/Distributed"
  "${ROOT_DIR}/lean/Runtime/Proofs/Adapters/Distributed"
  "${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Artifacts.lean"
  "${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Build.lean"
)

existing_scopes=()
for scope in "${SCOPES[@]}"; do
  if [[ -e "$scope" ]]; then
    existing_scopes+=("$scope")
  fi
done

if [[ "${#existing_scopes[@]}" -eq 0 ]]; then
  echo "error: no distributed proof audit scopes exist" >&2
  exit 2
fi

status=0

filter_allowlisted() {
  local input="$1"
  local filtered="$input"

  if [[ -f "$ALLOWLIST_FILE" ]]; then
    while IFS= read -r allow_pattern; do
      [[ -z "$allow_pattern" || "$allow_pattern" =~ ^[[:space:]]*# ]] && continue
      filtered="$(printf '%s\n' "$filtered" | rg --invert-match --pcre2 "$allow_pattern" || true)"
    done < "$ALLOWLIST_FILE"
  fi

  printf '%s\n' "$filtered"
}

run_check() {
  local label="$1"
  local pattern="$2"
  local output

  if output="$(rg --line-number --color never --pcre2 "$pattern" "${existing_scopes[@]}" | sed "s#${ROOT_DIR}/##" || true)" &&
      output="$(filter_allowlisted "$output")" &&
      [[ -n "$output" ]]; then
    echo "FAIL ${label}" >&2
    echo "$output" >&2
    echo >&2
    status=1
  else
    echo "OK   ${label}"
  fi
}

run_check \
  "no Lean escape hatches in distributed proof scopes" \
  '^[[:space:]]*(sorry|admit)\b|^[[:space:]]*axiom[[:space:]]+'

run_check \
  "no Prop := True placeholder contracts" \
  '\bProp[[:space:]]*:=[[:space:]]*True\b'

run_check \
  "no direct := True placeholder implementations" \
  ':=[[:space:]]*True\b'

run_check \
  "no implication-to-True vacuous guarantees" \
  '(->|→)[[:space:]]*True\b'

run_check \
  "no theorem-shaped witness record fields" \
  "^[[:space:]]*[A-Za-z0-9_']*(Witness|witness)[[:space:]]*:"

run_check \
  "no always-passing family validators" \
  'passed[[:space:]]*:=[[:space:]]*true'

if [[ "$status" -ne 0 ]]; then
  echo "distributed proof audit failed" >&2
  exit "$status"
fi

echo "distributed proof audit passed"
