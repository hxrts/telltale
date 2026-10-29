#!/usr/bin/env bash
# Audit classical theorem packs for proof-completion blockers.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ALLOWLIST_FILE="${ROOT_DIR}/scripts/lean/classical-proof-audit-allowlist.txt"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

SCOPES=(
  "${ROOT_DIR}/lean/Classical"
  "${ROOT_DIR}/lean/Protocol/Classical"
  "${ROOT_DIR}/lean/Runtime/Proofs/Adapters/Classical.lean"
  "${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Artifacts.lean"
  "${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Build.lean"
  "${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Profiles.lean"
  "${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/Inventory.lean"
  "${ROOT_DIR}/lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean"
)

existing_scopes=()
for scope in "${SCOPES[@]}"; do
  if [[ -e "$scope" ]]; then
    existing_scopes+=("$scope")
  fi
done

if [[ "${#existing_scopes[@]}" -eq 0 ]]; then
  echo "error: no classical proof audit scopes exist" >&2
  exit 2
fi

status=0
EXCLUDE_GLOBS=('--glob' '!**/lean/Distributed/**' '--glob' '!**/Adapters/Distributed/**')

# Vacuity and escape-hatch checks scan all of lean/ (except `.lake` and the
# Distributed trees owned by check-distributed-proof-audit.sh).
WIDE_SCOPE=("${ROOT_DIR}/lean")

# Vacuity checks run in multiline mode (`rg -U`), so `\s` spans newlines and a
# body split across lines (`def P : Prop :=\n  True`) is still caught.
# `True(?![.\w'])` avoids matching `True.intro` and identifiers like `True'`.
run_vacuity_checks() {
  run_check \
    "no Prop := True placeholder contracts" \
    '\bProp\s*:=\s*True(?![.\w'"'"'])' "$@"

  run_check \
    "no direct := True placeholder implementations" \
    ':=\s*True(?![.\w'"'"'])' "$@"

  run_check \
    "no := ∀ …, True quantified-True bodies" \
    ':=\s*(∀|\bforall\b)(?:(?!:=)[^\n]|\n(?!\s*\n)){0,300}?,\s*True(?![.\w'"'"'])' "$@"

  run_check \
    "no fun _ => True defaults" \
    '\bfun\b[^=\n]*(=>|↦)\s*True(?![.\w'"'"'])' "$@"

  run_check \
    "no implication-to-True vacuous guarantees" \
    '(->|→)\s*True(?![.\w'"'"'])' "$@"
}

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
  shift 2
  local targets=("$@")
  local output

  if [[ "${#targets[@]}" -eq 0 ]]; then
    targets=("${existing_scopes[@]}")
  fi

  if output="$(rg --multiline --line-number --color never --pcre2 \
        --glob '*.lean' --glob '!.lake/**' ${EXCLUDE_GLOBS[@]+"${EXCLUDE_GLOBS[@]}"} \
        "$pattern" "${targets[@]}" | sed "s#${ROOT_DIR}/##" || true)" &&
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
  "no Lean escape hatches in lean/ (excluding Distributed)" \
  '^[ \t]*(sorry|admit)\b|^[ \t]*axiom[[:space:]]+|^[ \t]*opaque[[:space:]]+|^[ \t]*partial[[:space:]]+def[[:space:]]+' \
  "${WIDE_SCOPE[@]}"

run_vacuity_checks "${WIDE_SCOPE[@]}"

run_check \
  "no theorem-shaped final-result profile fields" \
  "^[[:space:]]*[A-Za-z0-9_']*(Conclusion|Guarantee|Theorem|Finality|Termination|Safety)[[:space:]]*:"

run_check \
  "no always-passing family validators" \
  'passed[[:space:]]*:=[[:space:]]*true'

if [[ "$status" -ne 0 ]]; then
  echo "classical proof audit failed" >&2
  exit "$status"
fi

echo "classical proof audit passed"
