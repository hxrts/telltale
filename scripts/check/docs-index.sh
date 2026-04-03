#!/usr/bin/env bash
# Validate the Document Index table in docs/101_introduction.md:
#   1. Every docs/*.md file (except 101_introduction.md and SUMMARY.md) has an entry
#   2. No entries point to non-existent files
#   3. Link text matches each file's H1 title
set -uo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

INDEX_FILE="docs/101_introduction.md"

if [[ ! -f "$INDEX_FILE" ]]; then
  echo "error: $INDEX_FILE not found" >&2
  exit 2
fi

# ── Extract index entries ────────────────────────────────────────────
# Parse rows like: | [Title](filename.md) | Type | Status |
declare -A index_titles=()   # filename -> link text
declare -A index_lines=()    # filename -> line number

line_no=0
in_table=0
while IFS= read -r line; do
  line_no=$((line_no + 1))

  # Detect the Document Index heading
  if [[ "$line" == "## Document Index" ]]; then
    in_table=1
    continue
  fi

  # Stop at the next heading
  if [[ $in_table -eq 1 && "$line" == "## "* && "$line" != "## Document Index" ]]; then
    break
  fi

  # Skip header and separator rows
  if [[ $in_table -eq 1 ]]; then
    # Skip table header row
    [[ "$line" =~ ^\|[[:space:]]*Document[[:space:]]*\| ]] && continue
    # Skip separator row
    [[ "$line" =~ ^\|[-[:space:]\|]+\|$ ]] && continue

    # Parse data rows
    if [[ "$line" == '|'* ]]; then
      # Extract [Link Text](filename.md) from first cell
      local_re='\[([^]]+)\]\(([^)]+)\)'
      if [[ "$line" =~ $local_re ]]; then
        link_text="${BASH_REMATCH[1]}"
        filename="${BASH_REMATCH[2]}"
        # Strip anchors and query strings
        filename="${filename%%#*}"
        filename="${filename%%\?*}"
        index_titles[$filename]="$link_text"
        index_lines[$filename]="$line_no"
      fi
    fi
  fi
done < "$INDEX_FILE"

if [[ ${#index_titles[@]} -eq 0 ]]; then
  echo "error: no Document Index entries found in $INDEX_FILE" >&2
  exit 2
fi

# ── Build expected file list ─────────────────────────────────────────
# All docs/*.md except 101_introduction.md and SUMMARY.md
expected_files=()
for md in docs/*.md; do
  [[ -f "$md" ]] || continue
  bn="$(basename "$md")"
  case "$bn" in
    101_introduction.md|SUMMARY.md) continue ;;
  esac
  expected_files+=("$bn")
done

# ── Check completeness, existence, and titles ────────────────────────
errors=()

# Files missing from index
for bn in "${expected_files[@]}"; do
  if [[ -z "${index_titles[$bn]+x}" ]]; then
    errors+=("$INDEX_FILE: missing index entry for $bn")
  fi
done

# Index entries pointing to non-existent files or with wrong titles
for filename in "${!index_titles[@]}"; do
  link_text="${index_titles[$filename]}"
  ln="${index_lines[$filename]}"

  target="docs/$filename"
  if [[ ! -f "$target" ]]; then
    errors+=("$INDEX_FILE:$ln: index entry points to non-existent file: $filename")
    continue
  fi

  # Check title match
  actual_title="$(sed -n 's/^# //p' "$target" | head -n 1)"
  if [[ -n "$actual_title" && "$link_text" != "$actual_title" ]]; then
    errors+=("$INDEX_FILE:$ln: link text '$link_text' does not match H1 title '$actual_title' in $filename")
  fi

  # Check file is expected (not self-referencing or SUMMARY)
  case "$filename" in
    101_introduction.md)
      errors+=("$INDEX_FILE:$ln: index should not contain self-reference to 101_introduction.md")
      ;;
    SUMMARY.md)
      errors+=("$INDEX_FILE:$ln: index should not contain SUMMARY.md")
      ;;
  esac
done

# Index entries for files not in docs/ (extra entries)
for filename in "${!index_titles[@]}"; do
  found=0
  for bn in "${expected_files[@]}"; do
    if [[ "$bn" == "$filename" ]]; then
      found=1
      break
    fi
  done
  # Already caught by non-existent check above, skip
done

# ── Report ───────────────────────────────────────────────────────────
if [[ ${#errors[@]} -gt 0 ]]; then
  echo "docs index check failed: ${#errors[@]} issue(s)"
  for entry in "${errors[@]}"; do
    echo "  - $entry"
  done
  exit 1
fi

echo "docs index check passed (${#index_titles[@]} entries verified)"
