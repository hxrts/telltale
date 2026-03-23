#!/usr/bin/env bash
# Verify that docs/32_verification_inventory.md metrics match actual values
# derived from CODE_MAP.md, justfile recipe counts, and macro UI fixture counts.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

errors=()

# ── Helpers ───────────────────────────────────────────────────────────

# Extract the documented value for a named metric from the inventory doc.
# Usage: metric_value "Metric name"
metric_value() {
  local name="$1"
  local row
  row=$(grep -E "^\|[[:space:]]*${name}[[:space:]]*\|" docs/32_verification_inventory.md) || true
  if [[ -z "$row" ]]; then
    echo "missing metric row in docs/32_verification_inventory.md: ${name}" >&2
    exit 1
  fi
  # Extract the numeric value column (second pipe-delimited field), strip commas
  echo "$row" | sed 's/|/|/g' | awk -F'|' '{gsub(/[^0-9]/, "", $3); print $3}'
}

# Count non-comment, non-blank indented lines in a justfile recipe body.
# Usage: recipe_command_count "recipe-name"
recipe_command_count() {
  local recipe="$1"
  local in_recipe=0
  local count=0
  while IFS= read -r line; do
    if [[ "$in_recipe" -eq 1 ]]; then
      # Recipe body lines start with space or tab
      if [[ "$line" =~ ^[[:space:]] ]]; then
        local stripped
        stripped="${line#"${line%%[![:space:]]*}"}"
        # Skip blank and comment lines
        if [[ -n "$stripped" && ! "$stripped" =~ ^# ]]; then
          count=$((count + 1))
        fi
        continue
      else
        break
      fi
    fi
    # Match recipe header: name followed by colon or whitespace
    if [[ "$line" =~ ^${recipe}(:|[[:space:]]) ]]; then
      in_recipe=1
    fi
  done < justfile
  if [[ "$in_recipe" -eq 0 ]]; then
    echo "missing just recipe: ${recipe}" >&2
    exit 1
  fi
  echo "$count"
}

# Compare a documented value against an actual value.
# Usage: check_metric "Metric name" actual_value
check_metric() {
  local name="$1"
  local actual="$2"
  local documented
  documented=$(metric_value "$name")
  if [[ "$documented" -ne "$actual" ]]; then
    errors+=("docs/32_verification_inventory.md: metric \`${name}\` documents ${documented} but actual is ${actual}")
  fi
}

# ── Lean CODE_MAP.md Total Metrics ────────────────────────────────────

total_row=$(grep -E '^\|[[:space:]]+\*\*Total\*\*[[:space:]]+\|[[:space:]]+\*\*[0-9,]+\*\*[[:space:]]+\|[[:space:]]+\*\*[0-9,]+\*\*' lean/CODE_MAP.md | head -1) || true
if [[ -z "$total_row" ]]; then
  echo "failed to parse lean/CODE_MAP.md total metrics" >&2
  exit 1
fi

# Extract files count (second bold value) and lines count (third bold value)
actual_files=$(echo "$total_row" | sed 's/[*,]//g' | awk -F'|' '{gsub(/[^0-9]/, "", $3); print $3}')
actual_lines=$(echo "$total_row" | sed 's/[*,]//g' | awk -F'|' '{gsub(/[^0-9]/, "", $4); print $4}')

check_metric "Lean core-library files" "$actual_files"
check_metric "Lean core-library lines" "$actual_lines"

# ── Justfile Recipe Command Counts ────────────────────────────────────

actual_ownership=$(recipe_command_count "check-ownership-contracts")
actual_aura=$(recipe_command_count "check-aura-borrowed-lints")

check_metric "Ownership contract gate commands" "$actual_ownership"
check_metric "Aura-derived boundary checks" "$actual_aura"

# ── Macro UI Fixture Counts ───────────────────────────────────────────

macro_ui_file="rust/macros/tests/macro_ui.rs"

actual_pass=$(grep -c '\bt\.pass(' "$macro_ui_file" || echo 0)
actual_fail=$(grep -c '\bt\.compile_fail(' "$macro_ui_file" || echo 0)

check_metric "Macro UI pass fixtures" "$actual_pass"
check_metric "Macro UI compile-fail fixtures" "$actual_fail"

# ── Report ────────────────────────────────────────────────────────────

if [[ ${#errors[@]} -gt 0 ]]; then
  for err in "${errors[@]}"; do
    echo "$err" >&2
  done
  exit 1
fi

echo "verification inventory check passed"
