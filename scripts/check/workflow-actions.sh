#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

python3 <<'PY'
from __future__ import annotations

import os
import re
import sys
import urllib.error
import urllib.request
import json
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


def api_ok(path: str) -> bool:
    request = urllib.request.Request(
        f"https://api.github.com/{path}",
        headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": "telltale-workflow-actions-check",
        },
    )
    try:
        with urllib.request.urlopen(request) as response:
            return 200 <= response.status < 300
    except urllib.error.HTTPError:
        return False
    except urllib.error.URLError:
        return False


def matching_ref_exists(repo: str, kind: str, ref: str) -> bool:
    request = urllib.request.Request(
        f"https://api.github.com/repos/{repo}/git/matching-refs/{kind}/{ref}",
        headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": "telltale-workflow-actions-check",
        },
    )
    try:
        with urllib.request.urlopen(request) as response:
            if not (200 <= response.status < 300):
                return False
            payload = json.load(response)
    except (urllib.error.HTTPError, urllib.error.URLError, json.JSONDecodeError):
        return False
    expected = f"refs/{kind}/{ref}"
    return any(entry.get("ref") == expected for entry in payload)


for spec, locations in sorted(refs.items()):
    repo, ref = spec.rsplit("@", 1)
    repo_ok = api_ok(f"repos/{repo}")
    if not repo_ok:
        joined_locations = ", ".join(sorted(locations))
        errors.append(f"{joined_locations}: unresolved GitHub Action reference {spec}")
        continue
    ref_ok = (
        matching_ref_exists(repo, "tags", ref)
        or matching_ref_exists(repo, "heads", ref)
        or api_ok(f"repos/{repo}/commits/{ref}")
    )
    if not ref_ok:
        joined_locations = ", ".join(sorted(locations))
        errors.append(f"{joined_locations}: unresolved GitHub Action reference {spec}")

if errors:
    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(1)

print(f"workflow action check passed ({len(refs)} remote action reference(s) resolved)")
PY
