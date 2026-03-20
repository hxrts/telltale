#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

python3 <<'PY'
from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

root = Path.cwd()
workflow_dir_env = os.environ.get("WORKFLOW_ACTIONS_DIR")
workflow_dir = Path(workflow_dir_env) if workflow_dir_env else root / ".github" / "workflows"
pattern = re.compile(r"^\s*(?:-\s*)?uses:\s*([^\s#]+)\s*$")
refs: dict[str, set[str]] = {}


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)

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
                f"{display_path(workflow_path)}:{lineno}: malformed action reference without @ref: {spec}",
                file=sys.stderr,
            )
            sys.exit(1)
        refs.setdefault(spec, set()).add(f"{display_path(workflow_path)}:{lineno}")

errors: list[str] = []
for spec, locations in sorted(refs.items()):
    repo, ref = spec.rsplit("@", 1)
    repo_ok = subprocess.run(
        ["gh", "api", f"repos/{repo}"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    ).returncode == 0
    if not repo_ok:
        joined_locations = ", ".join(sorted(locations))
        errors.append(f"{joined_locations}: unresolved GitHub Action reference {spec}")
        continue
    ref_ok = False
    for api_path in (
        f"repos/{repo}/git/ref/tags/{ref}",
        f"repos/{repo}/git/ref/heads/{ref}",
        f"repos/{repo}/commits/{ref}",
    ):
        if subprocess.run(
            ["gh", "api", api_path],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode == 0:
            ref_ok = True
            break
    if not ref_ok:
        joined_locations = ", ".join(sorted(locations))
        errors.append(f"{joined_locations}: unresolved GitHub Action reference {spec}")

if errors:
    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(1)

print(f"workflow action check passed ({len(refs)} remote action reference(s) resolved)")
PY
