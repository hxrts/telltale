#!/usr/bin/env bash
# Update lean/CODE_MAP.md with current file/line counts per library.
# Pass --check to verify freshness without writing.
set -euo pipefail

# ── Paths & Arguments ──────────────────────────────────────────────────
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"
CODE_MAP_FILE="${ROOT_DIR}/lean/CODE_MAP.md"

CHECK_MODE=0
if [[ "${1:-}" == "--check" ]]; then
  CHECK_MODE=1
  shift
fi
if [[ $# -ne 0 ]]; then
  echo "usage: $0 [--check]" >&2
  exit 2
fi

EXCLUDE_REGEX='/(Examples|Tests)/|MutualTest|LocalTypeDBExamples\.lean'

# ── Library Definitions ────────────────────────────────────────────────
LIB_NAMES=(
  "SessionTypes"
  "SessionCoTypes"
  "Choreography"
  "Semantics"
  "Classical"
  "ClassicalAnalysis"
  "Distributed"
  "Protocol"
  "Runtime"
  "IrisExtraction"
)

LIB_ROOTS=(
  "SessionTypes"
  "SessionCoTypes"
  "Choreography"
  "Semantics"
  "Classical"
  "ClassicalAnalysisInstance"
  "Distributed"
  "Protocol"
  "Runtime"
  "IrisExtractionInstance"
)

LIB_FOCUS=(
  "Global/local type definitions, de Bruijn, participation"
  "Coinductive EQ2, bisimulation, duality, async subtyping"
  "Projection, harmony, blindness, embedding, erasure"
  "Operational semantics, determinism, deadlock freedom"
  "Transported theorems (queueing, large deviations, mixing)"
  "Real analysis concrete models for classical transport"
  "Distributed assumptions, validation, FLP/CAP theorem packaging"
  "Async buffered MPST, coherence, preservation, monitoring"
  "Protocol machine, Iris backend via iris-lean, resource algebras, WP"
  "Iris ghost state and program logic extraction"
)

# ── Helpers ───────────────────────────────────────────────────────────

# Replace content between begin/end markers in a file
replace_block() {
  local file="$1"
  local begin_marker="$2"
  local end_marker="$3"
  local payload="$4"

  local begin_line end_line
  begin_line="$(grep -nF "$begin_marker" "$file" | head -n1 | cut -d: -f1 || true)"
  end_line="$(grep -nF "$end_marker" "$file" | head -n1 | cut -d: -f1 || true)"

  if [[ -z "$begin_line" || -z "$end_line" ]]; then
    echo "error: markers not found in $file" >&2
    exit 1
  fi
  if (( end_line <= begin_line )); then
    echo "error: invalid marker order in $file" >&2
    exit 1
  fi

  local tmp_file
  local tmp_root="${TMPDIR:-/tmp}"
  if [[ ! -d "$tmp_root" ]]; then
    tmp_root="/tmp"
  fi
  tmp_file="$(TMPDIR="$tmp_root" mktemp)"

  {
    sed -n "1,${begin_line}p" "$file"
    printf '%s\n' "$payload"
    sed -n "${end_line},\$p" "$file"
  } > "$tmp_file"

  mv "$tmp_file" "$file"
}

# Count regex matches across a set of files
count_pattern_in_files() {
  local pattern="$1"
  shift
  if [[ "$#" -eq 0 ]]; then
    echo 0
    return
  fi
  local count=0
  local file
  for file in "$@"; do
    [[ -z "$file" ]] && continue
    count=$((count + $(grep -E -c "$pattern" "$file" || true)))
  done
  echo "$count"
}

# Collect all .lean files belonging to a library (root + subtree)
collect_lib_files() {
  local lib_root="$1"
  local root_module="$2"

  {
    if [[ -d "${LEAN_DIR}/${lib_root}" ]]; then
      find "${LEAN_DIR}/${lib_root}" -type f -name '*.lean' -not -path '*/.lake/*' -not -path '*/target/*'
    fi
    if [[ -f "${LEAN_DIR}/${root_module}.lean" ]]; then
      printf '%s\n' "${LEAN_DIR}/${root_module}.lean"
    fi
    # Also collect *API.lean for Instance modules (e.g., ClassicalAnalysisAPI.lean)
    local api_base="${lib_root%Instance}"
    if [[ "$api_base" != "$lib_root" && -f "${LEAN_DIR}/${api_base}API.lean" ]]; then
      printf '%s\n' "${LEAN_DIR}/${api_base}API.lean"
    fi
  } | sort -u | grep -Ev "$EXCLUDE_REGEX" || true
}

# Format a number with comma separators
add_commas() {
  local n="$1"
  local sign=""
  if [[ "$n" == -* ]]; then
    sign="-"
    n="${n#-}"
  fi
  local out=""
  while [[ ${#n} -gt 3 ]]; do
    out=",${n: -3}${out}"
    n="${n:0:${#n}-3}"
  done
  echo "${sign}${n}${out}"
}

# ── Gather Per-Library Stats ───────────────────────────────────────────
FILE_COUNTS=()
LINE_COUNTS=()
AXIOM_COUNTS=()
SORRY_COUNTS=()

TOTAL_FILES=0
TOTAL_LINES=0
TOTAL_AXIOMS=0
TOTAL_SORRY=0

for ((i=0; i<${#LIB_NAMES[@]}; i++)); do
  lib_name="${LIB_NAMES[$i]}"
  lib_root="${LIB_ROOTS[$i]}"

  files=()
  while IFS= read -r f; do
    [[ -z "$f" ]] && continue
    files+=("$f")
  done < <(collect_lib_files "$lib_root" "$lib_name")

  file_count=0
  line_count=0
  if [[ "${#files[@]}" -gt 0 ]]; then
    for f in "${files[@]}"; do
      [[ -z "$f" ]] && continue
      file_count=$((file_count + 1))
      line_count=$((line_count + $(wc -l < "$f" | tr -d ' ')))
    done
    axiom_count="$(count_pattern_in_files '^[[:space:]]*axiom\b' "${files[@]}")"
    sorry_count="$(count_pattern_in_files '\bsorry\b' "${files[@]}")"
  else
    axiom_count=0
    sorry_count=0
  fi

  FILE_COUNTS+=("$file_count")
  LINE_COUNTS+=("$line_count")
  AXIOM_COUNTS+=("$axiom_count")
  SORRY_COUNTS+=("$sorry_count")

  TOTAL_FILES=$((TOTAL_FILES + file_count))
  TOTAL_LINES=$((TOTAL_LINES + line_count))
  TOTAL_AXIOMS=$((TOTAL_AXIOMS + axiom_count))
  TOTAL_SORRY=$((TOTAL_SORRY + sorry_count))
done

# ── Write Metrics to CODE_MAP.md ───────────────────────────────────────
TODAY="$(date +%F)"

before_code_map_hash="$(shasum -a 256 "$CODE_MAP_FILE" | awk '{print $1}')"

CODE_MAP_METRICS="**Last Updated:** ${TODAY}"

overview_table="| Library        | Files | Lines   | Focus                                                      |"
overview_table+=$'\n'"|----------------|------:|--------:|------------------------------------------------------------|"

for ((i=0; i<${#LIB_NAMES[@]}; i++)); do
  printf -v row "| %-14s | %5s | %7s | %-58s |" \
    "${LIB_NAMES[$i]}" \
    "$(add_commas "${FILE_COUNTS[$i]}")" \
    "$(add_commas "${LINE_COUNTS[$i]}")" \
    "${LIB_FOCUS[$i]}"
  overview_table+=$'\n'"${row}"
done

printf -v total_row "| **Total**      | **%s** | **%s** | %-58s |" \
  "$(add_commas "$TOTAL_FILES")" \
  "$(add_commas "$TOTAL_LINES")" \
  ""
overview_table+=$'\n'"${total_row}"

replace_block "$CODE_MAP_FILE" "<!-- GENERATED_METRICS:BEGIN -->" "<!-- GENERATED_METRICS:END -->" "$CODE_MAP_METRICS"
replace_block "$CODE_MAP_FILE" "<!-- GENERATED_OVERVIEW_TABLE:BEGIN -->" "<!-- GENERATED_OVERVIEW_TABLE:END -->" "$overview_table"

# ── Check Mode ─────────────────────────────────────────────────────────
if (( CHECK_MODE == 1 )); then
  after_code_map_hash="$(shasum -a 256 "$CODE_MAP_FILE" | awk '{print $1}')"
  if [[ "$before_code_map_hash" != "$after_code_map_hash" ]]; then
    echo "Lean metrics are stale. Run: ./scripts/ops/sync-lean-metrics.sh" >&2
    exit 1
  fi
  echo "Lean metrics are up to date."
  exit 0
fi

echo "Updated generated metrics in:"
echo "  - lean/CODE_MAP.md"
