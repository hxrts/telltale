#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="${ROOT_DIR}/lean"

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

STRICT=0
if [[ "${1:-}" == "--strict" ]]; then
  STRICT=1
  shift
fi
if [[ $# -ne 0 ]]; then
  echo "usage: $0 [--strict]" >&2
  exit 2
fi

RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

errors=0
warnings=0
summary_lines=""

print_section() {
  echo ""
  echo -e "${BLUE}== $1 ==${NC}"
}

print_hits() {
  local severity="$1"
  local title="$2"
  local matches="$3"
  local recommendation="$4"
  local count=0

  if [[ -n "${matches}" ]]; then
    count="$(printf '%s\n' "${matches}" | sed '/^$/d' | wc -l | tr -d ' ')"
  fi

  if [[ "${count}" == "0" ]]; then
    echo -e "${GREEN}OK${NC}  ${title}"
    summary_lines+=$'OK\t'"${title}"$'\t0\n'
    return
  fi

  if [[ "${severity}" == "error" ]]; then
    errors=$((errors + count))
    echo -e "${RED}VIOLATION${NC}  ${title} (${count})"
    summary_lines+=$'ERROR\t'"${title}"$'\t'"${count}"$'\n'
  else
    warnings=$((warnings + count))
    echo -e "${YELLOW}WARNING${NC}  ${title} (${count})"
    summary_lines+=$'WARN\t'"${title}"$'\t'"${count}"$'\n'
  fi

  if [[ -n "${recommendation}" ]]; then
    echo "Recommended action: ${recommendation}"
  fi

  printf '%s\n' "${matches}" | sed -n '1,30p'
  if [[ "${count}" -gt 30 ]]; then
    echo "... (${count} total, truncated to 30)"
  fi
}

scan_rg() {
  local pattern="$1"
  rg -n --pcre2 "${pattern}" "${LEAN_DIR}" \
    -g '*.lean' \
    -g '!.lake/**' \
    -g '!**/.lake/**' \
    -g '!target/**' \
    -g '!**/target/**' || true
}

collect_file_metric_hits() {
  local mode="$1"
  local threshold="$2"
  local out=""

  while IFS= read -r file; do
    local line_count
    line_count="$(wc -l < "${file}" | tr -d ' ')"
    if (( line_count <= threshold )); then
      continue
    fi

    # Exclude obvious test/example/debug modules from style checks.
    if [[ "${file}" =~ /Tests/ ]] || [[ "${file}" =~ /Examples/ ]] || [[ "${file}" =~ MutualTest ]]; then
      continue
    fi

    case "${mode}" in
      file_length)
        out+="${file}:${line_count}: exceeds style guide file-length threshold (${threshold})"$'\n'
        ;;
      problem_header)
        if ! rg -q "The Problem\." "${file}" || ! rg -q "Solution Structure\." "${file}"; then
          out+="${file}:${line_count}: missing \"The Problem.\" / \"Solution Structure.\" prose block"$'\n'
        fi
        ;;
      section_headers)
        if ! rg -q "/-![[:space:]]*##[[:space:]]+" "${file}"; then
          out+="${file}:${line_count}: missing section headers (/-! ## ... -/)"$'\n'
        fi
        ;;
      module_doc)
        if ! rg -q "/-![[:space:]]*#[[:space:]]+" "${file}"; then
          out+="${file}:${line_count}: missing module doc block (/-! # ... -/)"$'\n'
        fi
        ;;
      *)
        echo "internal error: unknown mode ${mode}" >&2
        exit 2
        ;;
    esac
  done < <(find "${LEAN_DIR}" -type f -name '*.lean' -not -path '*/.lake/*' -not -path '*/target/*' | sort)

  printf '%s\n' "${out}" | sed '/^$/d' || true
}

# Find code blocks (between section headers) exceeding a line threshold.
# Counts non-comment, non-blank lines only.
collect_long_code_blocks() {
  local threshold="$1"
  local out=""

  while IFS= read -r file; do
    # Exclude obvious test/example/debug modules from style checks.
    if [[ "${file}" =~ /Tests/ ]] || [[ "${file}" =~ /Examples/ ]] || [[ "${file}" =~ MutualTest ]]; then
      continue
    fi

    # Use awk to find code blocks > threshold lines (excluding comments/blanks)
    local hits
    hits="$(awk -v threshold="${threshold}" -v filename="${file}" '
      BEGIN {
        in_block_comment = 0
        block_start = 1
        code_lines = 0
      }

      # Section header: /-! ## ... (single or multi-line)
      # Check FIRST before block comment handling since section headers are block comments
      /\/-![[:space:]]*##/ {
        if (code_lines > threshold) {
          print filename ":" block_start ": code block has " code_lines " non-comment lines (threshold: " threshold ")"
        }
        block_start = NR + 1
        code_lines = 0
        # If section header spans multiple lines, enter block comment mode
        if (!/-\/$/) {
          in_block_comment = 1
        }
        next
      }

      # Handle block comments: /- ... -/ (includes /-! doc comments)
      # Start of block comment (not closed on same line)
      /\/-/ && !/-\// {
        in_block_comment = 1
        next
      }
      # Single-line block comment - skip entirely
      /\/-.*-\// { next }
      # End of block comment
      /-\// {
        in_block_comment = 0
        next
      }
      # Inside block comment - skip
      in_block_comment { next }

      # Skip blank lines
      /^[[:space:]]*$/ { next }

      # Skip single-line comments
      /^[[:space:]]*--/ { next }

      # Count as code line
      { code_lines++ }

      END {
        if (code_lines > threshold) {
          print filename ":" block_start ": code block has " code_lines " non-comment lines (threshold: " threshold ")"
        }
      }
    ' "${file}")"

    if [[ -n "${hits}" ]]; then
      out+="${hits}"$'\n'
    fi
  done < <(find "${LEAN_DIR}" -type f -name '*.lean' -not -path '*/.lake/*' -not -path '*/target/*' | sort)

  printf '%s\n' "${out}" | sed '/^$/d' || true
}

print_section "Lean Escape Hatches"

sorry_hits="$(scan_rg '\bsorry\b')"
print_hits "error" "No sorry proofs" "${sorry_hits}" \
  "Replace sorry with complete proofs."

axiom_hits="$(scan_rg '^[[:space:]]*axiom\b')"
print_hits "error" "No bare axiom declarations" "${axiom_hits}" \
  "Remove axioms or move temporary assumptions behind explicit, documented shim boundaries."

print_section "Lean Style-Guide Conformance (First-Pass Heuristics)"

placeholder_hits="$(scan_rg '\bProp\s*:=\s*True\b')"
print_hits "error" "No Prop := True placeholder contracts in production paths" "${placeholder_hits}" \
  "Replace placeholder contracts with real predicates/theorems or move them to explicitly excluded experimental paths."

root_import_hits="$(rg -n --pcre2 '^(import .*\b(MutualTest|LocalTypeDBExamples|Examples|Tests)\b)' \
  "${LEAN_DIR}/SessionTypes.lean" "${LEAN_DIR}/Choreography.lean" "${LEAN_DIR}/Protocol.lean" "${LEAN_DIR}/Runtime.lean" 2>/dev/null || true)"
print_hits "error" "Root facades avoid debug/example/test imports" "${root_import_hits}" \
  "Keep root facade imports restricted to production API modules."

legacy_projection_import_hits="$(
  rg -n --pcre2 '^import[[:space:]]+Choreography\.Projection\.(Trans|Projectb|ProjectProps|Embed|EmbedProps|Erasure|Regression)\b' \
    "${LEAN_DIR}" -g '*.lean' -g '!.lake/**' -g '!**/.lake/**' -g '!target/**' -g '!**/target/**' |
    rg -v '/Choreography/Projection/' |
    rg -v '/Runtime/Tests/' || true
)"
print_hits "error" "No deprecated legacy projection imports in production modules" "${legacy_projection_import_hits}" \
  "Import canonical Choreography.Projection.Project (or dedicated non-legacy modules) from production files."

legacy_theorempack_import_hits="$(
  rg -n --pcre2 '^import[[:space:]]+Runtime\.Proofs\.TheoremPack$' \
    "${LEAN_DIR}" -g '*.lean' -g '!.lake/**' -g '!**/.lake/**' -g '!target/**' -g '!**/target/**' |
    rg -v '/Runtime/Proofs/Examples/' |
    rg -v '/Runtime/Proofs/TheoremPack/Artifacts\.lean:' || true
)"
print_hits "error" "No direct Runtime.Proofs.TheoremPack imports outside migration shims/examples" "${legacy_theorempack_import_hits}" \
  "Use Runtime.Proofs.TheoremPack.API (or builder/artifact layers) instead of importing the monolithic theorem-pack module."

long_file_hits="$(collect_file_metric_hits file_length 500)"
print_hits "warning" "Files stay within style-guide length target (<= 500 lines)" "${long_file_hits}" \
  "Split oversized files into coherent, content-indicative units with barrel re-exports."

problem_header_hits="$(collect_file_metric_hits problem_header 120)"
print_hits "warning" "Non-trivial files include Problem/Solution prose headers" "${problem_header_hits}" \
  "Add a prose block with \"The Problem.\" and \"Solution Structure.\" after imports."

section_header_hits="$(collect_file_metric_hits section_headers 120)"
print_hits "warning" "Non-trivial files include section headers" "${section_header_hits}" \
  "Add /-! ## ... -/ section headers to organize long files."

long_code_block_hits="$(collect_long_code_blocks 50)"
print_hits "warning" "Code blocks stay within 50 non-comment lines" "${long_code_block_hits}" \
  "Add /-! ## ... -/ section headers to break up long code blocks."

module_doc_hits="$(collect_file_metric_hits module_doc 120)"
print_hits "warning" "Non-trivial files include module docs" "${module_doc_hits}" \
  "Add a top module doc /-! # ... -/ after imports."

echo ""
print_section "Summary"

echo "Errors:   ${errors}"
echo "Warnings: ${warnings}"
if (( STRICT == 1 )); then
  echo "Mode:     strict"
else
  echo "Mode:     default"
fi
echo ""
printf "%-8s %-7s %s\n" "Severity" "Count" "Check"
printf "%-8s %-7s %s\n" "--------" "-----" "-----"
printf '%s' "${summary_lines}" | awk -F '\t' '{ printf "%-8s %-7s %s\n", $1, $3, $2 }'
echo ""

if (( errors > 0 )); then
  echo -e "${RED}Lean architecture/style check failed:${NC} ${errors} error(s), ${warnings} warning(s)."
  exit 1
fi

if (( STRICT == 1 && warnings > 0 )); then
  echo -e "${YELLOW}Lean architecture/style check strict-failed:${NC} ${warnings} warning(s)."
  exit 1
fi

if (( warnings > 0 )); then
  echo -e "${YELLOW}Lean architecture/style check passed with warnings:${NC} ${warnings} warning(s)."
else
  echo -e "${GREEN}Lean architecture/style check passed.${NC}"
fi
