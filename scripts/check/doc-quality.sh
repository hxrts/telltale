#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

python3 - "${ROOT_DIR}" <<'PY'
import re
import subprocess
import sys
from pathlib import Path

root = Path(sys.argv[1])
docs_dir = root / "docs"

# Include root docs and nested docs folders, but exclude mdbook output.
doc_files = sorted(
    p
    for p in docs_dir.rglob("*.md")
    if "book" not in p.parts and p.name != "SUMMARY.md"
)

if not doc_files:
    print("no docs found")
    sys.exit(1)

# Cache titles for link-text consistency checks.
titles: dict[Path, str] = {}
for path in doc_files:
    title = ""
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("# "):
            title = line[2:].strip()
            break
    if title:
        titles[path.resolve()] = title

just_list = subprocess.check_output(["just", "--list"], text=True, cwd=root)
recipes = set()
for line in just_list.splitlines():
    line = line.strip()
    if not line or line.startswith("Available recipes"):
        continue
    recipe = line.split()[0]
    if recipe.endswith(":"):
        recipe = recipe[:-1]
    recipes.add(recipe)

link_re = re.compile(r"\[([^\]]+)\]\(([^)]+\.md(?:#[^)]+)?)\)")
just_re = re.compile(r"\bjust\s+([A-Za-z0-9_-]+)")
script_re = re.compile(r"\bscripts/([A-Za-z0-9_.-]+\.sh)\b")
word_re = re.compile(r"[A-Za-z0-9_]+")

errors: list[str] = []

for path in doc_files:
    lines = path.read_text(encoding="utf-8").splitlines()
    rel = path.relative_to(root)

    # Check link titles and link targets.
    text = "\n".join(lines)
    for text_label, raw_target in link_re.findall(text):
        target_no_anchor = raw_target.split("#", 1)[0]
        target_path = (path.parent / target_no_anchor).resolve()
        if not target_path.exists():
            errors.append(f"{rel}: missing linked file {raw_target}")
            continue
        if target_path in titles:
            expected = titles[target_path]
            if text_label != expected:
                errors.append(
                    f"{rel}: link text '{text_label}' does not match title '{expected}' for {raw_target}"
                )

    # Check command references and script references.
    for recipe in just_re.findall(text):
        if recipe not in recipes:
            errors.append(f"{rel}: unknown just recipe '{recipe}'")
    for script_name in script_re.findall(text):
        script_path = root / "scripts" / script_name
        if not script_path.exists():
            errors.append(f"{rel}: missing script reference scripts/{script_name}")

    # Style and code-block checks outside fenced code.
    in_code = False
    pending_explainer = False
    prose_words = 0
    code_words = 0

    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code = not in_code
            if not in_code:
                pending_explainer = True
            continue

        if in_code:
            code_words += len(word_re.findall(line))
            continue

        prose_words += len(word_re.findall(line))

        if "—" in line:
            errors.append(f"{rel}:{idx}: em dash is not allowed")
        if ";" in line:
            errors.append(f"{rel}:{idx}: semicolon is not allowed")

        if pending_explainer:
            if not stripped:
                continue
            if stripped.startswith("#") or stripped.startswith("```"):
                errors.append(
                    f"{rel}:{idx}: code block must be followed by an explanatory paragraph"
                )
            elif stripped.startswith(("-", "*", "1.", "2.", "3.")):
                errors.append(
                    f"{rel}:{idx}: explanatory text after code block must be prose, not a list"
                )
            pending_explainer = False

    if in_code:
        errors.append(f"{rel}: unclosed fenced code block")

    if prose_words <= code_words:
        errors.append(
            f"{rel}: prose word count ({prose_words}) must exceed code word count ({code_words})"
        )

if errors:
    print("doc quality check failed:\n")
    for err in errors:
        print(f"- {err}")
    sys.exit(1)

print("doc quality check passed")
PY
