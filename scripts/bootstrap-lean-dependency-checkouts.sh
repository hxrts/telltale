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

repo_by_name = {
    "mathlib4": "https://github.com/leanprover-community/mathlib4.git",
    "iris-lean": "https://github.com/hxrts/iris-lean.git",
}

def run(cmd: list[str], cwd: Path | None = None) -> str:
    return subprocess.check_output(cmd, cwd=str(cwd) if cwd else None, text=True).strip()

for dep in deps:
    name = dep.get("name")
    path = dep.get("path")
    revision = dep.get("revision")
    if not isinstance(name, str) or not isinstance(path, str) or not isinstance(revision, str):
        raise SystemExit(f"error: invalid dependency pin entry: {dep}")

    repo = repo_by_name.get(name)
    if repo is None:
        raise SystemExit(f"error: missing repository mapping for dependency '{name}'")

    checkout = Path(path)
    checkout.parent.mkdir(parents=True, exist_ok=True)

    if (checkout / ".git").exists():
        print(f"sync {name}: fetching pinned revision {revision}")
    else:
        print(f"clone {name}: {repo} -> {checkout}")
        run(["git", "clone", "--filter=blob:none", repo, str(checkout)])

    run(["git", "fetch", "--depth=1", "origin", revision], cwd=checkout)
    run(["git", "checkout", "--detach", revision], cwd=checkout)
    actual = run(["git", "rev-parse", "HEAD"], cwd=checkout)
    if actual != revision:
        raise SystemExit(f"error: {name} pinned checkout mismatch: expected {revision}, got {actual}")
    print(f"OK   {name} pinned at {actual}")
PY
