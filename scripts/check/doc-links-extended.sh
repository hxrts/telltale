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

if [[ "${1:-}" != "" ]]; then
  echo "usage: $0"
  exit 2
fi

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

ROOT_FILES=(
  "README.md"
  "CLAUDE.md"
)

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

root_files = ["README.md", "CLAUDE.md"]

markdown_re = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
bare_re = re.compile(r"(?<![A-Za-z0-9_./-])((?:\./\.?/)*docs/[A-Za-z0-9._/-]+)")

checked = 0
seen = set()
missing = []
outside = []
work_links = []


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


def check_work_link(source: Path, line_no: int, raw_target: str):
    """Flag markdown links that point to the work/ directory."""
    if not raw_target:
        return
    candidate = sanitize(raw_target)
    if not candidate:
        return
    if is_external(candidate):
        return
    if candidate.startswith("work/") or "/work/" in candidate:
        rel = source.relative_to(root) if source.is_absolute() else source
        work_links.append(f"{rel}:{line_no}: link to work/ directory: {candidate}")


# -------------------------------------------------------------------
# Scan all directories for docs/ link targets
# -------------------------------------------------------------------

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
                pass
            else:
                for m in markdown_re.finditer(line):
                    check_target(source, line_no, m.group(1))
                for m in bare_re.finditer(line):
                    check_target(source, line_no, m.group(1))

            # Check for work/ links in markdown files
            if str(rel).endswith(".md"):
                for m in markdown_re.finditer(line):
                    check_work_link(source, line_no, m.group(1))

for rel_name in root_files:
    source = root / rel_name
    if not source.is_file():
        continue

    lines = source.read_text(encoding="utf-8", errors="ignore").splitlines()
    for line_no, line in enumerate(lines, start=1):
        if "docs/" not in line and "/docs/" not in line:
            pass
        else:
            for m in markdown_re.finditer(line):
                check_target(source, line_no, m.group(1))
            for m in bare_re.finditer(line):
                check_target(source, line_no, m.group(1))

        for m in markdown_re.finditer(line):
            check_work_link(source, line_no, m.group(1))

# -------------------------------------------------------------------
# SUMMARY.md completeness: every docs/*.md must appear in SUMMARY.md
# -------------------------------------------------------------------

summary_errors = []
summary_path = docs_root / "SUMMARY.md"
if summary_path.is_file():
    summary_text = summary_path.read_text(encoding="utf-8")
    summary_targets: set[str] = set()
    for m in markdown_re.finditer(summary_text):
        target = m.group(1).split("#", 1)[0].split("?", 1)[0].strip()
        if target:
            summary_targets.add(target)

    for md in sorted(docs_root.glob("*.md")):
        name = md.name
        if name == "SUMMARY.md":
            continue
        if name not in summary_targets:
            summary_errors.append(f"docs/SUMMARY.md: missing link to {name}")

# -------------------------------------------------------------------
# Report
# -------------------------------------------------------------------

has_errors = False

if outside:
    has_errors = True
    print("docs link check failed: references outside docs root")
    for entry in outside:
        print(f"  - {entry}")

if missing:
    has_errors = True
    print("docs link check failed: missing targets")
    for entry in missing:
        print(f"  - {entry}")

if work_links:
    has_errors = True
    print("docs link check failed: links to work/ directory")
    for entry in work_links:
        print(f"  - {entry}")

if summary_errors:
    has_errors = True
    print("docs link check failed: SUMMARY.md incomplete")
    for entry in summary_errors:
        print(f"  - {entry}")
    print("hint: run `just summary` to regenerate SUMMARY.md")

if has_errors:
    total = len(outside) + len(missing) + len(work_links) + len(summary_errors)
    print(f"docs link check found {total} issue(s)")
    raise SystemExit(1)

print(f"docs link check passed ({checked} unique docs reference(s) checked)")
PY
