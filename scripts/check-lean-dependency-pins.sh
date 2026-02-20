#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PINS_FILE="${ROOT_DIR}/lean/dependency_pins.json"

if [[ ! -f "${PINS_FILE}" ]]; then
  echo "error: missing dependency pins file: ${PINS_FILE}" >&2
  exit 2
fi

python3 - "${PINS_FILE}" <<'PY'
import json
import subprocess
import sys
from pathlib import Path

pins_path = Path(sys.argv[1])
pins = json.loads(pins_path.read_text())
deps = pins.get("dependencies", [])
if not isinstance(deps, list) or not deps:
    raise SystemExit("error: dependency_pins.json must define non-empty dependencies")

errors: list[str] = []

for dep in deps:
    name = dep.get("name")
    path = dep.get("path")
    expected = dep.get("revision")
    if not isinstance(name, str) or not isinstance(path, str) or not isinstance(expected, str):
        errors.append(f"invalid dependency pin entry: {dep}")
        continue
    repo = Path(path)
    if not repo.exists():
        errors.append(f"{name}: missing checkout at {path}")
        continue
    try:
        actual = (
            subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True)
            .strip()
        )
    except subprocess.CalledProcessError as err:
        errors.append(f"{name}: failed to read git revision ({err})")
        continue
    if actual != expected:
        errors.append(f"{name}: expected {expected}, found {actual}")
    else:
        print(f"OK   {name} pinned at {actual}")

if errors:
    for error in errors:
        print(f"FAIL {error}")
    raise SystemExit(1)
PY
