#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

require_pattern() {
  local file="$1"
  local pattern="$2"
  local message="$3"
  if ! rg -Fq "${pattern}" "${file}"; then
    echo "error: ${message}" >&2
    exit 1
  fi
}

forbid_pattern() {
  local file="$1"
  local pattern="$2"
  local message="$3"
  if rg -Fq "${pattern}" "${file}"; then
    echo "error: ${message}" >&2
    exit 1
  fi
}

require_recipe_pattern() {
  local recipe="$1"
  local pattern="$2"
  local message="$3"
  python3 - "$recipe" "$pattern" "$message" <<'PY'
from pathlib import Path
import sys

recipe, pattern, message = sys.argv[1:]
text = Path("justfile").read_text().splitlines()
current = None
body: list[str] = []
recipes: dict[str, str] = {}

for line in text:
    if line and not line.startswith((" ", "\t")) and ":" in line:
        if current is not None:
            recipes[current] = "\n".join(body)
        current = line.split(":", 1)[0].split()[0]
        body = []
        continue
    if current is not None and line.startswith((" ", "\t")):
        body.append(line)
if current is not None:
    recipes[current] = "\n".join(body)

recipe_body = recipes.get(recipe, "")
if pattern not in recipe_body:
    raise SystemExit(f"error: {message}")
PY
}

forbid_recipe_pattern() {
  local recipe="$1"
  local pattern="$2"
  local message="$3"
  python3 - "$recipe" "$pattern" "$message" <<'PY'
from pathlib import Path
import sys

recipe, pattern, message = sys.argv[1:]
text = Path("justfile").read_text().splitlines()
current = None
body: list[str] = []
recipes: dict[str, str] = {}

for line in text:
    if line and not line.startswith((" ", "\t")) and ":" in line:
        if current is not None:
            recipes[current] = "\n".join(body)
        current = line.split(":", 1)[0].split()[0]
        body = []
        continue
    if current is not None and line.startswith((" ", "\t")):
        body.append(line)
if current is not None:
    recipes[current] = "\n".join(body)

recipe_body = recipes.get(recipe, "")
if pattern in recipe_body:
    raise SystemExit(f"error: {message}")
PY
}

require_pattern justfile "check-pr-critical:" "missing justfile recipe check-pr-critical"
require_pattern justfile "check-deep-assurance:" "missing justfile recipe check-deep-assurance"
require_recipe_pattern ci-dry-run "just check-pr-critical" "ci-dry-run must call just check-pr-critical"
require_recipe_pattern ci-dry-run "just check-deep-assurance" "ci-dry-run full lane must call just check-deep-assurance"
forbid_recipe_pattern check-focused-assurance "just check-scale-budgets" "check-focused-assurance must not own check-scale-budgets directly anymore"

require_pattern .github/workflows/check.yml "run: just check-pr-critical" "check.yml must use the canonical PR-critical lane"
require_pattern .github/workflows/verify.yml "just check-pr-critical | tee artifacts/check-pr-critical.log" "verify.yml fast/scheduled lanes must use the canonical PR-critical lane"
require_pattern .github/workflows/verify.yml "just check-deep-assurance | tee artifacts/check-deep-assurance.log" "verify.yml scheduled lane must use the canonical deep-assurance lane"

for legacy in \
  "Run fast structural verification lane" \
  "Run focused assurance lane" \
  "Run packaged artifact assurance lane" \
  "Run cross-target matrix lane" \
  "Run Track B gate" \
  "Run property-based lane" \
  "Run composition stress lane"
do
  forbid_pattern .github/workflows/verify.yml "${legacy}" "verify.yml still duplicates legacy assurance step '${legacy}'"
done

echo "ci-assurance-lanes: ok"
