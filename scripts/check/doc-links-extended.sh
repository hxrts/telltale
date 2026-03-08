#!/usr/bin/env bash
set -euo pipefail

if ! command -v rg >/dev/null 2>&1; then
  echo "error: ripgrep (rg) is required" >&2
  exit 2
fi

if ! command -v git >/dev/null 2>&1; then
  echo "error: git is required" >&2
  exit 2
fi

SCAN_WORK=false
if [[ "${1:-}" == "--work" ]]; then
  SCAN_WORK=true
elif [[ "${1:-}" != "" ]]; then
  echo "usage: $0 [--work]"
  echo "  --work   include work/ references in scan"
  exit 2
fi

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

SCAN_ROOTS=(
  "docs"
  "rust"
  "lean"
  "scripts"
  ".github"
)

if [[ "$SCAN_WORK" == true ]]; then
  SCAN_ROOTS+=("work")
fi

ROOT_FILES=(
  "README.md"
  "CLAUDE.md"
)

export INCLUDE_WORK="$SCAN_WORK"

python3 - <<'PY'
import os
import re
import subprocess
from pathlib import Path

root = Path(".").resolve()
docs_root = root / "docs"
if not docs_root.is_dir():
    print("error: docs directory not found at docs/")
    raise SystemExit(2)

scan_roots = [
    "docs",
    "rust",
    "lean",
    "scripts",
    ".github",
]
if os.environ.get("INCLUDE_WORK", "false") == "true":
    scan_roots.append("work")

root_files = ["README.md", "CLAUDE.md"]

markdown_re = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
bare_re = re.compile(r"(?<![A-Za-z0-9_./-])((?:\./\.?/)*docs/[A-Za-z0-9._/-]+)")

checked = 0
seen = set()
missing = []
outside = []


def sanitize(target: str) -> str:
    target = target.strip().strip("<>\"'")
    if not target:
        return ""

    if target.startswith("[") and target.endswith("]"):
        inner = target[1:-1]
        if "docs/" in inner:
            target = inner

    target = target.split(" ", 1)[0]
    target = target.split("?", 1)[0]
    target = target.split("#", 1)[0]

    while target and target[-1] in ".,:;)":
        target = target[:-1]

    return target


def is_external(target: str) -> bool:
    lower = target.lower()
    return lower.startswith(("http://", "https://", "mailto:", "#"))


def check_target(source: Path, line_no: int, raw_target: str):
    global checked
    if not raw_target:
        return

    candidate = sanitize(raw_target)
    if not candidate:
        return
    if is_external(candidate):
        return
    if "docs/" not in candidate and not candidate.startswith("/docs/"):
        return

    key = (str(source.relative_to(root)), line_no, candidate)
    if key in seen:
        return
    seen.add(key)

    if candidate.startswith("/docs/"):
        resolved = (root / candidate[1:]).resolve()
    elif candidate.startswith("docs/"):
        resolved = (root / candidate).resolve()
    else:
        resolved = (source.parent / candidate).resolve()

    try:
        rel = resolved.relative_to(root)
    except ValueError:
        outside.append(f"{source}:{line_no}: docs reference escapes repo root: {candidate}")
        return

    if not str(rel).startswith("docs/"):
        outside.append(f"{source}:{line_no}: docs reference outside docs/: {candidate}")
        return

    if not resolved.exists():
        missing.append(f"{source}:{line_no}: missing docs target: {candidate} -> {rel}")
        return

    if resolved.is_dir():
        checked += 1
        return

    checked += 1


for scan_root in scan_roots:
    abs_root = root / scan_root
    if not abs_root.exists():
        continue

    files = subprocess.run(
        ["rg", "-l", "-0", "docs/|\\.\\./", str(scan_root)],
        text=False,
        check=False,
        capture_output=True,
    ).stdout

    for raw in files.split(b"\0"):
        if not raw:
            continue
        source = (root / raw.decode()).resolve()
        if not source.is_file():
            continue

        rel = source.relative_to(root)
        parts = set(rel.parts)
        if "work" in parts and "archive" in parts:
            continue

        try:
            lines = source.read_text(encoding="utf-8", errors="ignore").splitlines()
        except OSError:
            continue

        for line_no, line in enumerate(lines, start=1):
            if "docs/" not in line and "/docs/" not in line:
                continue
            for m in markdown_re.finditer(line):
                check_target(source, line_no, m.group(1))
            for m in bare_re.finditer(line):
                check_target(source, line_no, m.group(1))

for rel_name in root_files:
    source = root / rel_name
    if not source.is_file():
        continue

    lines = source.read_text(encoding="utf-8", errors="ignore").splitlines()
    for line_no, line in enumerate(lines, start=1):
        if "docs/" not in line and "/docs/" not in line:
            continue
        for m in markdown_re.finditer(line):
            check_target(source, line_no, m.group(1))
        for m in bare_re.finditer(line):
            check_target(source, line_no, m.group(1))

if outside:
    print("docs link check failed: references outside docs root")
    for entry in outside:
        print(f"  - {entry}")

if missing:
    print("docs link check failed: missing targets")
    for entry in missing:
        print(f"  - {entry}")

if outside or missing:
    print(f"docs link check found {len(outside) + len(missing)} issue(s)")
    raise SystemExit(1)

print(f"docs link check passed ({checked} unique docs reference(s) checked)")
PY
