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

# Well-known types and identifiers that should not trigger drift warnings.
# Standard library types, Lean builtins, example role names, common enum
# variants, and environment variable names are excluded.
skip_identifiers = {
    # Standard Rust types and traits
    "String", "Vec", "Option", "Result", "Box", "Arc", "Rc", "Mutex",
    "HashMap", "HashSet", "BTreeMap", "BTreeSet", "PathBuf", "Path",
    "Ok", "Err", "Some", "None", "Self", "Sized", "Send", "Sync",
    "Clone", "Copy", "Debug", "Display", "Default", "Drop", "Eq", "Ord",
    "Hash", "Iterator", "Future", "Pin", "From", "Into", "AsRef", "Deref",
    "PartialEq", "PartialOrd", "Serialize", "Deserialize", "Error",
    "Read", "Write", "PhantomData", "Infallible",
    # Standard Lean types
    "Nat", "Int", "Bool", "Prop", "Type", "List", "Array", "Char", "Float",
    "Unit", "Decidable", "Repr", "Inhabited", "Subtype", "Sigma", "Prod",
    "Sum", "Or", "And", "Iff", "Not", "True", "False", "HEq", "BEq",
    "Monoid", "Group", "Ring", "Field", "Finset",
    # Markdown / formatting artifacts
    "README", "SUMMARY", "TODO", "FIXME", "NOTE", "WARNING", "IMPORTANT",
    # Common abbreviations
    "API", "CLI", "CI", "CD", "PR", "OS", "IO", "UUID", "HTTP", "HTTPS",
    "URL", "JSON", "CBOR", "TOML", "YAML", "WASM", "BFT", "CRDT",
    # Example role names from choreography docs
    "Alice", "Bob", "Chef", "SousChef", "Baker", "Seller", "Client",
    "Server", "Worker", "Coordinator",
    # DSL keywords and built-in value constructors
    "Done", "Loop", "Parallel", "Maybe", "Just", "Nothing",
    "Hello", "HelloAck", "Goodbye", "Ping", "Pong", "Ack",
    "Commit", "Abort", "Cancel", "Retry",
    # Common enum variant names
    "Active", "Closed", "Draining", "Aborted", "Faulted",
    "Admitted", "Blocked", "Failure", "Full",
}

# Known deprecated identifiers. Backtick references to these in docs are
# flagged as stale. Each key maps to a short reason.
deprecated_identifiers: dict[str, str] = {
    # Add entries here as identifiers are removed or renamed, e.g.:
    # "OldTypeName": "removed in v6.0, replaced by NewTypeName",
}

pascal_case_re = re.compile(r"^[A-Z][A-Za-z0-9_]+$")


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

        # Check for deprecated identifiers
        if snippet in deprecated_identifiers:
            reason = deprecated_identifiers[snippet]
            errors.append(
                f"{file.relative_to(root)}:{line}: deprecated identifier `{snippet}` ({reason})"
            )
            continue

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
            continue

        # PascalCase identifier check: verify backticked type/trait/enum names
        # exist somewhere in the Rust or Lean source.
        if pascal_case_re.match(snippet):
            if snippet in skip_identifiers:
                continue
            # Skip single-letter type parameters
            if len(snippet) <= 1:
                continue
            # Skip ALL_CAPS constants (environment variables, etc.)
            if re.fullmatch(r"[A-Z][A-Z0-9_]+", snippet):
                continue
            if snippet not in repo_identifiers:
                errors.append(
                    f"{file.relative_to(root)}:{line}: unresolved type or identifier `{snippet}`"
                )

if errors:
    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(1)

print("docs semantic drift check passed")
PY
