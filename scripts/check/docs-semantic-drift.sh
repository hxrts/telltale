#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

python3 <<'PY'
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

root = Path.cwd()
doc_files = [
    path
    for path in [root / "CLAUDE.md", *sorted((root / "docs").rglob("*.md"))]
    if path.exists()
]

metadata = json.loads(
    subprocess.check_output(
        ["cargo", "metadata", "--no-deps", "--format-version", "1"],
        cwd=root,
        text=True,
    )
)
workspace_packages = {pkg["name"] for pkg in metadata["packages"]}
workspace_crate_tokens = workspace_packages | {name.replace("-", "_") for name in workspace_packages}
just_recipes = set(
    subprocess.check_output(["just", "--summary"], cwd=root, text=True).split()
)

repo_identifiers: set[str] = set()
identifier_pattern = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")

for base in (root / "src", root / "rust", root / "lean"):
    if not base.exists():
        continue
    glob = "*.lean" if base.name == "lean" else "*.rs"
    for file in base.rglob(glob):
        try:
            text = file.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        repo_identifiers.update(identifier_pattern.findall(text))

path_prefixes = (
    "docs/",
    "rust/",
    "lean/",
    "scripts/",
    "papers/",
    ".github/",
    "src/",
)
path_literals = {
    "CLAUDE.md",
    "Cargo.toml",
    "justfile",
    "lean/CODE_MAP.md",
}
external_prefixes = {
    "std",
    "core",
    "alloc",
    "serde",
    "serde_json",
    "tokio",
    "rayon",
    "uuid",
    "rand",
    "bincode",
    "thiserror",
    "clap",
    "tempfile",
    "proc_macro2",
}


def line_for(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def looks_like_path(snippet: str) -> bool:
    return snippet in path_literals or snippet.startswith(path_prefixes)


def normalized_symbol_tail(snippet: str) -> str | None:
    last = snippet.split("::")[-1]
    match = re.match(r"([A-Za-z_][A-Za-z0-9_]*)", last)
    return match.group(1) if match else None


errors: list[str] = []
code_span = re.compile(r"`([^`\n]+)`")

for file in doc_files:
    text = file.read_text(encoding="utf-8")
    for match in code_span.finditer(text):
        snippet = match.group(1).strip()
        line = line_for(text, match.start())

        if snippet.startswith("just "):
            parts = snippet.split()
            if len(parts) >= 2 and not parts[1].startswith("-") and parts[1] not in just_recipes:
                errors.append(
                    f"{file.relative_to(root)}:{line}: unknown just recipe `{parts[1]}`"
                )
            continue

        if looks_like_path(snippet):
            if (
                "*" in snippet
                or "/.lake/build/" in snippet
            ):
                continue
            if not (root / snippet).exists():
                errors.append(
                    f"{file.relative_to(root)}:{line}: missing referenced path `{snippet}`"
                )
            continue

        if snippet in workspace_crate_tokens:
            continue
        if re.fullmatch(r"(telltale(-[a-z0-9]+)?|effect-scaffold)", snippet):
            errors.append(
                f"{file.relative_to(root)}:{line}: unknown workspace crate `{snippet}`"
            )
            continue

        if "::" in snippet:
            if re.search(r"[\s{}(),]", snippet):
                continue
            head = snippet.split("::", 1)[0]
            if head in external_prefixes:
                continue
            symbol = normalized_symbol_tail(snippet)
            if symbol and symbol not in repo_identifiers:
                errors.append(
                    f"{file.relative_to(root)}:{line}: unresolved repo-local symbol tail `{snippet}`"
                )

if errors:
    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(1)

print("docs semantic drift check passed")
PY
