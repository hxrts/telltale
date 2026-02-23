#!/usr/bin/env python3
"""Normalize Lean theorem/lemma declaration casing (scoped).

Rules:
- theorem/lemma tails must be snake_case

Notes:
- Only declaration tail (after last '.') is rewritten.
- Dry run by default.
- Use --apply to write changes.
- Use --scope to restrict discovery (e.g. lean/Runtime).
- Rewrites are applied over --rewrite-root (default: same as --scope).
- Use --exclude to skip subtrees for both discovery and rewrite.
- Use --exclude-scope and --exclude-rewrite for fine-grained control.
- Import lines are never rewritten.
- Replacements are applied only in Lean code regions (not comments/strings).
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

NAME_CHARS = r"A-Za-z0-9_.'`?!"
TOKEN_CHARS = r"A-Za-z0-9_'?!"
DECORATION_CHARS = "'?!"

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|local|scoped|noncomputable|unsafe|partial|mutual)\s+)*"
    r"(?P<kind>theorem|lemma)\s+"
    rf"(?P<name>[{NAME_CHARS}]+)"
)
IMPORT_LINE_RE = re.compile(r"^\s*import\s+")
EXCLUDED_DIRS = {".lake", ".git", "build"}


@dataclass(frozen=True)
class DeclRename:
    file: Path
    line: int
    kind: str
    old: str
    new: str


def parse_excludes(values: Sequence[str]) -> Set[Path]:
    out: Set[Path] = set()
    for raw in values:
        for part in raw.split(","):
            p = part.strip().strip("/")
            if not p:
                continue
            out.add(Path(p))
    return out


def is_excluded(rel: Path, excluded_paths: Set[Path]) -> bool:
    for ex in excluded_paths:
        ex_parts = ex.parts
        if len(ex_parts) <= len(rel.parts) and rel.parts[: len(ex_parts)] == ex_parts:
            return True
    return False


def iter_lean_files(root: Path, excluded_paths: Set[Path]) -> Iterable[Path]:
    for file in sorted(root.rglob("*.lean")):
        rel = file.relative_to(root)
        if any(part in EXCLUDED_DIRS for part in rel.parts):
            continue
        if is_excluded(rel, excluded_paths):
            continue
        yield file


def split_tail(name: str) -> Tuple[str, str]:
    if "." in name:
        head, tail = name.rsplit(".", 1)
        return head + ".", tail
    return "", name


def split_decorations(s: str) -> Tuple[str, str]:
    i = len(s)
    while i > 0 and s[i - 1] in DECORATION_CHARS:
        i -= 1
    return s[:i], s[i:]


def to_snake(base: str) -> str:
    s = base.replace("`", "")
    s = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", s)
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", s)
    s = s.replace("-", "_")
    s = re.sub(r"__+", "_", s)
    s = s.strip("_").lower()
    return s


def is_snake_tail(tail: str) -> bool:
    base, dec = split_decorations(tail)
    if not base:
        return False
    if not re.fullmatch(r"[a-z][a-z0-9_]*", base):
        return False
    return all(ch in DECORATION_CHARS for ch in dec)


def conformant(kind: str, tail: str) -> bool:
    if kind in {"theorem", "lemma"}:
        return is_snake_tail(tail)
    return True


def proposed_tail(kind: str, tail: str) -> str:
    base, dec = split_decorations(tail)
    if kind in {"theorem", "lemma"}:
        return to_snake(base) + dec
    return tail


def discover_decl_renames(scope_root: Path, excluded_paths: Set[Path]) -> Tuple[List[DeclRename], Set[str]]:
    renames: List[DeclRename] = []
    declared_names: Set[str] = set()

    for file in iter_lean_files(scope_root, excluded_paths):
        text = file.read_text(encoding="utf-8")
        for idx, line in enumerate(text.splitlines(), start=1):
            m = DECL_RE.match(line)
            if not m:
                continue
            kind = m.group("kind")
            old = m.group("name")
            declared_names.add(old)
            prefix, tail = split_tail(old)
            if conformant(kind, tail):
                continue
            new_tail = proposed_tail(kind, tail)
            new = prefix + new_tail
            if new != old:
                renames.append(DeclRename(file=file, line=idx, kind=kind, old=old, new=new))

    return renames, declared_names


def resolve_renames(renames: List[DeclRename], declared_names: Set[str]) -> Tuple[List[DeclRename], List[str]]:
    old_to_decl: Dict[str, DeclRename] = {}
    for r in renames:
        prev = old_to_decl.get(r.old)
        if prev is None:
            old_to_decl[r.old] = r
        elif prev.new != r.new:
            continue

    by_new: Dict[str, List[DeclRename]] = {}
    for r in old_to_decl.values():
        by_new.setdefault(r.new, []).append(r)

    selected: List[DeclRename] = []
    skipped: List[str] = []

    for new, group in sorted(by_new.items()):
        if len(group) > 1:
            olds = ", ".join(sorted(r.old for r in group))
            skipped.append(f"collision: {new} <= {olds}")
            continue

        r = group[0]
        selected.append(r)

    selected.sort(key=lambda r: (str(r.file), r.line, r.old))
    return selected, skipped


def build_patterns(old_to_new: Dict[str, str]) -> List[Tuple[str, str, re.Pattern[str]]]:
    patterns: List[Tuple[str, str, re.Pattern[str]]] = []
    for old in sorted(old_to_new.keys(), key=len, reverse=True):
        new = old_to_new[old]
        pat = re.compile(rf"(?<![{TOKEN_CHARS}]){re.escape(old)}(?![{TOKEN_CHARS}])")
        patterns.append((old, new, pat))
    return patterns


def rewrite_code_chunk(
    chunk: str, patterns: List[Tuple[str, str, re.Pattern[str]]]
) -> Tuple[str, int]:
    out = chunk
    replaced = 0
    for old, new, pat in patterns:
        if old not in out:
            continue
        out, n = pat.subn(new, out)
        replaced += n
    return out, replaced


def rewrite_line_preserving_comments_and_strings(
    line: str, patterns: List[Tuple[str, str, re.Pattern[str]]], block_depth: int
) -> Tuple[str, int, int]:
    # Fast path: only when comment/string state cannot change on this line.
    if block_depth == 0 and "/-" not in line and "--" not in line and "\"" not in line:
        if not any(old in line for old, _, _ in patterns):
            return line, 0, block_depth

    out: List[str] = []
    replaced = 0
    n = len(line)
    i = 0
    code_start = 0

    while i < n:
        if block_depth > 0:
            if line.startswith("/-", i):
                block_depth += 1
                i += 2
                continue
            if line.startswith("-/", i):
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if line.startswith("--", i):
            code_chunk, nrep = rewrite_code_chunk(line[code_start:i], patterns)
            replaced += nrep
            out.append(code_chunk)
            out.append(line[i:])
            return "".join(out), replaced, block_depth

        if line.startswith("/-", i):
            code_chunk, nrep = rewrite_code_chunk(line[code_start:i], patterns)
            replaced += nrep
            out.append(code_chunk)

            comment_start = i
            block_depth = 1
            i += 2
            while i < n and block_depth > 0:
                if line.startswith("/-", i):
                    block_depth += 1
                    i += 2
                elif line.startswith("-/", i):
                    block_depth -= 1
                    i += 2
                else:
                    i += 1

            out.append(line[comment_start:i])
            code_start = i
            continue

        if line[i] == '"':
            code_chunk, nrep = rewrite_code_chunk(line[code_start:i], patterns)
            replaced += nrep
            out.append(code_chunk)

            str_start = i
            i += 1
            while i < n:
                if line[i] == "\\":
                    i += 2
                elif line[i] == '"':
                    i += 1
                    break
                else:
                    i += 1

            out.append(line[str_start:i])
            code_start = i
            continue

        i += 1

    # Tail of line: code segment if not inside a block comment, otherwise comment.
    tail = line[code_start:n]
    if block_depth == 0:
        code_chunk, nrep = rewrite_code_chunk(tail, patterns)
        replaced += nrep
        out.append(code_chunk)
    else:
        out.append(tail)

    return "".join(out), replaced, block_depth


def apply_renames(
    rewrite_root: Path, renames: List[DeclRename], excluded_paths: Set[Path]
) -> Tuple[int, int]:
    old_to_new: Dict[str, str] = {r.old: r.new for r in renames}
    patterns = build_patterns(old_to_new)

    changed_files = 0
    total_replacements = 0

    for file in iter_lean_files(rewrite_root, excluded_paths):
        original = file.read_text(encoding="utf-8")
        lines = original.splitlines(keepends=True)
        out_lines: List[str] = []
        file_count = 0
        block_depth = 0

        for line in lines:
            if IMPORT_LINE_RE.match(line):
                out_lines.append(line)
                continue

            new_line, n, block_depth = rewrite_line_preserving_comments_and_strings(
                line, patterns, block_depth
            )
            file_count += n
            out_lines.append(new_line)

        updated = "".join(out_lines)
        if updated != original:
            file.write_text(updated, encoding="utf-8")
            changed_files += 1
            total_replacements += file_count

    return changed_files, total_replacements


def main() -> int:
    parser = argparse.ArgumentParser(description="Normalize Lean theorem/lemma casing")
    parser.add_argument("--scope", default="lean", help="Discovery scope root (default: lean)")
    parser.add_argument(
        "--rewrite-root",
        default=None,
        help="Rewrite root for references (default: same as --scope)",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        help=(
            "Exclude path prefix for both discovery and rewrite roots. "
            "Repeatable; supports comma-separated values."
        ),
    )
    parser.add_argument(
        "--exclude-scope",
        action="append",
        default=[],
        help=(
            "Exclude path prefix only for discovery scope. "
            "Repeatable; supports comma-separated values."
        ),
    )
    parser.add_argument(
        "--exclude-rewrite",
        action="append",
        default=[],
        help=(
            "Exclude path prefix only for rewrite root. "
            "Repeatable; supports comma-separated values."
        ),
    )
    parser.add_argument("--apply", action="store_true", help="Write changes")
    parser.add_argument("--dry-run", action="store_true", help="Force dry-run mode")
    parser.add_argument("--show", type=int, default=80, help="Number of planned renames to show")
    parser.add_argument("--all", action="store_true", help="Show all planned renames")
    args = parser.parse_args()

    scope_root = Path(args.scope).resolve()
    rewrite_root = Path(args.rewrite_root).resolve() if args.rewrite_root else scope_root
    common_excluded = parse_excludes(args.exclude)
    scope_excluded = common_excluded | parse_excludes(args.exclude_scope)
    rewrite_excluded = common_excluded | parse_excludes(args.exclude_rewrite)

    if not scope_root.exists():
        print(f"error: scope not found: {scope_root}", file=sys.stderr)
        return 2
    if not rewrite_root.exists():
        print(f"error: rewrite root not found: {rewrite_root}", file=sys.stderr)
        return 2

    discovered, declared = discover_decl_renames(scope_root, scope_excluded)
    renames, skipped = resolve_renames(discovered, declared)

    if not discovered:
        print("No non-conformant declaration names found.")
        return 0

    print(f"Found {len(discovered)} non-conformant declaration name(s) in scope.")
    print(f"Planned safe rename set: {len(renames)}")
    if skipped:
        print(f"Skipped due to collisions: {len(skipped)}")

    if args.dry_run or not args.apply:
        limit = len(renames) if args.all else min(args.show, len(renames))
        for r in renames[:limit]:
            rel = r.file.relative_to(Path.cwd()) if r.file.is_relative_to(Path.cwd()) else r.file
            print(f"{rel}:{r.line}: {r.kind} {r.old} -> {r.new}")
        if limit < len(renames):
            print(f"... and {len(renames) - limit} more (use --all to show all)")
        if skipped:
            print("Skipped samples:")
            for msg in skipped[: min(20, len(skipped))]:
                print(f"  {msg}")
            if len(skipped) > 20:
                print(f"  ... and {len(skipped) - 20} more skipped mappings")
        print("Dry run only. Re-run with --apply to write changes.")
        return 0

    changed_files, total_replacements = apply_renames(rewrite_root, renames, rewrite_excluded)
    print(f"Applied renames in {changed_files} file(s); {total_replacements} token replacement(s).")
    if skipped:
        print(f"Skipped {len(skipped)} ambiguous/conflicting rename(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
