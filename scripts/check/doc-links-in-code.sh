#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

python3 - "${ROOT_DIR}" <<'PY'
from pathlib import Path
import re
import sys

root = Path(sys.argv[1]).resolve()
scan_roots = [root / "rust", root / "lean"]
skip_dirs = {
    ".git",
    ".lake",
    "target",
    "build",
    "artifacts",
    "book",
    ".direnv",
    "node_modules",
    "dist",
}

markdown_target_re = re.compile(r"\[[^\]]+\]\(([^)\s]+)\)")
bare_docs_re = re.compile(r"(?<![A-Za-z0-9_./-])((?:\.\./)*docs/[A-Za-z0-9._/-]+)")

errors: list[str] = []
seen: set[tuple[Path, int, str]] = set()
checked = 0


def should_skip(path: Path) -> bool:
    return any(part in skip_dirs for part in path.parts)


for scan_root in scan_roots:
    if not scan_root.exists():
        continue

    for path in scan_root.rglob("*"):
        if not path.is_file() or should_skip(path):
            continue

        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue

        if "docs/" not in text:
            continue

        for line_no, line in enumerate(text.splitlines(), start=1):
            if "docs/" not in line:
                continue

            raw_targets: list[str] = []
            for target in markdown_target_re.findall(line):
                if "docs/" in target:
                    if "://" in target:
                        continue
                    raw_targets.append(target)
            raw_targets.extend(bare_docs_re.findall(line))

            for raw_target in raw_targets:
                candidate = raw_target.strip().strip("<>").strip("\"'")
                if "docs/" not in candidate:
                    continue

                candidate = candidate.split("#", 1)[0].split("?", 1)[0].rstrip(".,:;")
                if not candidate:
                    continue

                key = (path, line_no, candidate)
                if key in seen:
                    continue
                seen.add(key)
                checked += 1

                if candidate.startswith("docs/"):
                    target_path = (root / candidate).resolve()
                else:
                    target_path = (path.parent / candidate).resolve()

                try:
                    target_rel = target_path.relative_to(root)
                except ValueError:
                    errors.append(
                        f"{path.relative_to(root)}:{line_no}: docs reference escapes repository root: {raw_target}"
                    )
                    continue

                if not target_path.exists() or not target_path.is_file():
                    errors.append(
                        f"{path.relative_to(root)}:{line_no}: missing docs target: {raw_target} -> {target_rel}"
                    )

if errors:
    print("docs link check failed:\n")
    for entry in errors:
        print(f"- {entry}")
    sys.exit(1)

print(f"docs link check passed ({checked} docs references checked in rust/ and lean/)")
PY
