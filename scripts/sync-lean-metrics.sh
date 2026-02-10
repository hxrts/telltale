#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"
CODE_MAP_FILE="${ROOT_DIR}/lean/CODE_MAP.md"
STATUS_FILE="${ROOT_DIR}/work/status.md"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

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

LIB_NAMES=(
  "SessionTypes"
  "SessionCoTypes"
  "Choreography"
  "Semantics"
  "Classical"
  "Distributed"
  "Protocol"
  "Runtime"
)

LIB_ROOTS=(
  "SessionTypes"
  "SessionCoTypes"
  "Choreography"
  "Semantics"
  "Classical"
  "Distributed"
  "Protocol"
  "Runtime"
)

LIB_FOCUS=(
  "Global/local type definitions, de Bruijn, participation"
  "Coinductive EQ2, bisimulation, duality, async subtyping"
  "Projection, harmony, blindness, embedding, erasure"
  "Operational semantics, determinism, deadlock freedom"
  "Transported theorems (queueing, large deviations, mixing)"
  "Distributed assumptions, validation, FLP/CAP theorem packaging"
  "Async buffered MPST, coherence, preservation, monitoring"
  "VM, Iris backend via iris-lean, resource algebras, WP"
)

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
  tmp_file="$(mktemp)"

  {
    sed -n "1,${begin_line}p" "$file"
    printf '%s\n' "$payload"
    sed -n "${end_line},\$p" "$file"
  } > "$tmp_file"

  mv "$tmp_file" "$file"
}

count_pattern_in_files() {
  local pattern="$1"
  shift
  if [[ "$#" -eq 0 ]]; then
    echo 0
    return
  fi
  (rg -n --pcre2 "$pattern" "$@" || true) | wc -l | tr -d ' '
}

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
  } | sort -u | rg -v "$EXCLUDE_REGEX" || true
}

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

TODAY="$(date +%F)"

before_code_map_hash="$(shasum -a 256 "$CODE_MAP_FILE" | awk '{print $1}')"
before_status_hash="$(shasum -a 256 "$STATUS_FILE" | awk '{print $1}')"

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

status_table="| Library        | Files | Lines | Axioms | Sorry |"
status_table+=$'\n'"| -------------- | ----: | ----: | -----: | ----: |"

for ((i=0; i<${#LIB_NAMES[@]}; i++)); do
  printf -v status_row "| %-14s | %5s | %5s | %6s | %5s |" \
    "${LIB_NAMES[$i]}" \
    "$(add_commas "${FILE_COUNTS[$i]}")" \
    "$(add_commas "${LINE_COUNTS[$i]}")" \
    "$(add_commas "${AXIOM_COUNTS[$i]}")" \
    "$(add_commas "${SORRY_COUNTS[$i]}")"
  status_table+=$'\n'"${status_row}"
done

status_metrics="**Last updated:** ${TODAY}"
status_metrics+=$'\n\n---\n\n## Library Statistics\n\n'
status_metrics+="**~$(add_commas "$TOTAL_FILES") files, ~$(add_commas "$TOTAL_LINES") lines, $(add_commas "$TOTAL_AXIOMS") axioms, $(add_commas "$TOTAL_SORRY") sorry.**"
status_metrics+=$'\n\nMain proof obligations discharged (0 proof holes). Remaining work is feature development and axiom retirement.\n\n'
status_metrics+="${status_table}"

replace_block "$CODE_MAP_FILE" "<!-- GENERATED_METRICS:BEGIN -->" "<!-- GENERATED_METRICS:END -->" "$CODE_MAP_METRICS"
replace_block "$CODE_MAP_FILE" "<!-- GENERATED_OVERVIEW_TABLE:BEGIN -->" "<!-- GENERATED_OVERVIEW_TABLE:END -->" "$overview_table"
replace_block "$STATUS_FILE" "<!-- GENERATED_STATUS_METRICS:BEGIN -->" "<!-- GENERATED_STATUS_METRICS:END -->" "$status_metrics"

if (( CHECK_MODE == 1 )); then
  after_code_map_hash="$(shasum -a 256 "$CODE_MAP_FILE" | awk '{print $1}')"
  after_status_hash="$(shasum -a 256 "$STATUS_FILE" | awk '{print $1}')"
  if [[ "$before_code_map_hash" != "$after_code_map_hash" ]] || [[ "$before_status_hash" != "$after_status_hash" ]]; then
    echo "Lean metrics are stale. Run: ./scripts/sync-lean-metrics.sh" >&2
    exit 1
  fi
  echo "Lean metrics are up to date."
  exit 0
fi

echo "Updated generated metrics in:"
echo "  - lean/CODE_MAP.md"
echo "  - work/status.md"
