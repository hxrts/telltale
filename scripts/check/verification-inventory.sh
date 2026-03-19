#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

python3 <<'PY'
from __future__ import annotations

import re
import sys
from pathlib import Path

root = Path.cwd()
doc_path = root / "docs/32_verification_inventory.md"
code_map = (root / "lean/CODE_MAP.md").read_text(encoding="utf-8")
justfile = (root / "justfile").read_text(encoding="utf-8")
macro_ui = (root / "rust/macros/tests/macro_ui.rs").read_text(encoding="utf-8")
doc_text = doc_path.read_text(encoding="utf-8")

total_match = re.search(
    r"\|\s+\*\*Total\*\*\s+\|\s+\*\*(?P<files>[0-9,]+)\*\*\s+\|\s+\*\*(?P<lines>[0-9,]+)\*\*",
    code_map,
)
if not total_match:
    raise SystemExit("failed to parse lean/CODE_MAP.md total metrics")

def metric_value(name: str) -> int:
    pattern = re.compile(rf"\|\s*{re.escape(name)}\s*\|\s*([0-9,]+)\s*\|")
    match = pattern.search(doc_text)
    if not match:
        raise SystemExit(f"missing metric row in docs/32_verification_inventory.md: {name}")
    return int(match.group(1).replace(",", ""))

def recipe_command_count(recipe: str) -> int:
    lines = justfile.splitlines()
    count = 0
    in_recipe = False
    for line in lines:
        if in_recipe:
            if line.startswith(" ") or line.startswith("\t"):
                stripped = line.strip()
                if stripped and not stripped.startswith("#"):
                    count += 1
                continue
            break
        if re.match(rf"^{re.escape(recipe)}(?::|\s)", line):
            in_recipe = True
    if not in_recipe:
        raise SystemExit(f"missing just recipe: {recipe}")
    return count

actual = {
    "Lean core-library files": int(total_match.group("files").replace(",", "")),
    "Lean core-library lines": int(total_match.group("lines").replace(",", "")),
    "Ownership contract gate commands": recipe_command_count("check-ownership-contracts"),
    "Aura-derived boundary checks": recipe_command_count("check-aura-borrowed-lints"),
    "Macro UI pass fixtures": len(re.findall(r'\bt\.pass\(', macro_ui)),
    "Macro UI compile-fail fixtures": len(re.findall(r'\bt\.compile_fail\(', macro_ui)),
}

errors = []
for name, expected in actual.items():
    documented = metric_value(name)
    if documented != expected:
        errors.append(
            f"docs/32_verification_inventory.md: metric `{name}` documents {documented} but actual is {expected}"
        )

if errors:
    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(1)

print("verification inventory check passed")
PY
