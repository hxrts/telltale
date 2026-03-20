#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

python3 <<'PY'
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

root = Path.cwd()
workflow_dir = root / ".github" / "workflows"
pattern = re.compile(r"^\s*uses:\s*([^\s#]+)\s*$")
refs: dict[str, set[str]] = {}

for workflow_path in sorted(workflow_dir.glob("*.yml")):
    for lineno, line in enumerate(workflow_path.read_text(encoding="utf-8").splitlines(), start=1):
        match = pattern.match(line)
        if not match:
            continue
        spec = match.group(1)
        if spec.startswith("./") or spec.startswith("docker://"):
            continue
        if "@" not in spec:
            print(
                f"{workflow_path.relative_to(root)}:{lineno}: malformed action reference without @ref: {spec}",
                file=sys.stderr,
            )
            sys.exit(1)
        refs.setdefault(spec, set()).add(f"{workflow_path.relative_to(root)}:{lineno}")

errors: list[str] = []
for spec, locations in sorted(refs.items()):
    repo, ref = spec.rsplit("@", 1)
    cmd = ["git", "ls-remote", "--exit-code", f"https://github.com/{repo}.git", ref]
    result = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if result.returncode != 0:
        joined_locations = ", ".join(sorted(locations))
        errors.append(f"{joined_locations}: unresolved GitHub Action reference {spec}")

if errors:
    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(1)

print(f"workflow action check passed ({len(refs)} remote action reference(s) resolved)")
PY
