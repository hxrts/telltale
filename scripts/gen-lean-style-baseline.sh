#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"
OUT_FILE="${ROOT_DIR}/work/lean_style_baseline.md"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

EXCLUDE_REGEX='/(Examples|Tests)/|MutualTest|LocalTypeDBExamples\.lean'

FILES=()
while IFS= read -r f; do
  [[ -z "$f" ]] && continue
  FILES+=("$f")
done < <(find "$LEAN_DIR" -type f -name '*.lean' -not -path '*/.lake/*' -not -path '*/target/*' | sort | rg -v "$EXCLUDE_REGEX" || true)
TOTAL_FILES="${#FILES[@]}"

CRITERIA=(
  "problem_headers"
  "section_headers"
  "public_docstrings"
  "file_length"
  "code_block_length"
  "import_discipline"
  "namespace_usage"
  "expose_blocks"
)

LABELS=(
  "Problem/Solution headers"
  "Section headers (##)"
  "Public docstrings (/--)"
  "File length <= 500 lines"
  "Max nonblank run <= 50 lines (proxy)"
  "No broad barrel imports in internals"
  "Namespace declared"
  "Has ## Expose block"
)

PASS_COUNTS=()
FAIL_COUNTS=()
for ((i=0; i<${#CRITERIA[@]}; i++)); do
  PASS_COUNTS+=(0)
  FAIL_COUNTS+=(0)
done

TMP_DIR="$(mktemp -d)"
cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT

for crit in "${CRITERIA[@]}"; do
  : > "${TMP_DIR}/${crit}.fails"
done

max_nonblank_run() {
  local file="$1"
  awk 'NF { run += 1; if (run > max) max = run; next } { run = 0 } END { print max + 0 }' "$file"
}

record_result() {
  local idx="$1"
  local ok="$2"
  local rel="$3"
  local crit="${CRITERIA[$idx]}"
  if [[ "$ok" == "1" ]]; then
    PASS_COUNTS[$idx]=$((PASS_COUNTS[$idx] + 1))
  else
    FAIL_COUNTS[$idx]=$((FAIL_COUNTS[$idx] + 1))
    echo "$rel" >> "${TMP_DIR}/${crit}.fails"
  fi
}

for file in "${FILES[@]}"; do
  rel="${file#${ROOT_DIR}/}"
  lines="$(wc -l < "$file" | tr -d ' ')"
  max_run="$(max_nonblank_run "$file")"

  ok=0
  if rg -q "The Problem\." "$file" && rg -q "Solution Structure\." "$file"; then ok=1; fi
  record_result 0 "$ok" "$rel"

  ok=0
  if rg -q '/-![[:space:]]*##[[:space:]]+' "$file"; then ok=1; fi
  record_result 1 "$ok" "$rel"

  ok=0
  if rg -q '/--' "$file"; then ok=1; fi
  record_result 2 "$ok" "$rel"

  ok=0
  if (( lines <= 500 )); then ok=1; fi
  record_result 3 "$ok" "$rel"

  ok=0
  if (( max_run <= 50 )); then ok=1; fi
  record_result 4 "$ok" "$rel"

  ok=1
  if rg -q '^[[:space:]]*import (SessionTypes|SessionCoTypes|Choreography|Semantics|Protocol|Runtime|Classical|Distributed)$' "$file"; then ok=0; fi
  record_result 5 "$ok" "$rel"

  ok=0
  if rg -q '^[[:space:]]*namespace[[:space:]]+' "$file"; then ok=1; fi
  record_result 6 "$ok" "$rel"

  ok=0
  if rg -q '/-![[:space:]]*##[[:space:]]+Expose' "$file"; then ok=1; fi
  record_result 7 "$ok" "$rel"
done

{
  echo "# Lean Style Baseline"
  echo ""
  echo "Generated: $(date +%F)"
  echo "Scope: production Lean modules (examples/tests/debug modules excluded)"
  echo "Modules scanned: ${TOTAL_FILES}"
  echo ""
  echo "## Checklist Summary"
  echo ""
  echo "| Criterion | Pass | Fail |"
  echo "| --- | ---: | ---: |"
  for ((i=0; i<${#CRITERIA[@]}; i++)); do
    echo "| ${LABELS[$i]} | ${PASS_COUNTS[$i]} | ${FAIL_COUNTS[$i]} |"
  done

  echo ""
  echo "## Failing Modules (By Criterion)"
  for ((i=0; i<${#CRITERIA[@]}; i++)); do
    crit="${CRITERIA[$i]}"
    echo ""
    echo "### ${LABELS[$i]}"
    if (( FAIL_COUNTS[$i] == 0 )); then
      echo "- none"
      continue
    fi

    echo "- fail count: ${FAIL_COUNTS[$i]}"
    echo ""
    sed 's/^/- `/' "${TMP_DIR}/${crit}.fails" | sed 's/$/`/'
  done
} > "$OUT_FILE"

echo "Wrote ${OUT_FILE}"
