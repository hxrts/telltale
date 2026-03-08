#!/usr/bin/env bash
set -eu

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

DOCS_DIR="$ROOT_DIR/docs"

DOC_FILES="$(mktemp)"
ERRORS_FILE="$(mktemp)"
JUST_RECIPES_FILE="$(mktemp)"
trap 'rm -f "$DOC_FILES" "$ERRORS_FILE" "$JUST_RECIPES_FILE"' EXIT

find "$DOCS_DIR" -type f -name "*.md" ! -path "*/book/*" ! -name "SUMMARY.md" | sort > "$DOC_FILES"

if [ ! -s "$DOC_FILES" ]; then
  echo "no docs found"
  exit 1
fi

while IFS= read -r line; do
  line="$(printf '%s' "$line" | sed -e 's/\r$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"
  if [ -z "$line" ] || [ "${line#Available recipes*}" != "$line" ]; then
    continue
  fi
  recipe="${line%% *}"
  recipe="${recipe%:}"
  if [ -n "$recipe" ]; then
    echo "$recipe" >> "$JUST_RECIPES_FILE"
  fi
done < <(just --list)

add_error() {
  printf '%s\n' "$1" >> "$ERRORS_FILE"
}

while IFS= read -r doc_file; do
  rel_file="${doc_file#$ROOT_DIR/}"

  while IFS='|' read -r label target; do
    target_file="${target%%#*}"
    target_path="$(realpath -m "$(dirname "$doc_file")/$target_file")"
    if [ ! -f "$target_path" ]; then
      add_error "$rel_file: missing linked file $target"
      continue
    fi

    expected="$(sed -n 's/^# //p' "$target_path" | head -n 1)"
    if [ -n "$expected" ] && [ "$label" != "$expected" ]; then
      add_error "$rel_file: link text '$label' does not match title '$expected' for $target"
    fi
  done < <(perl -ne 'while (/\[([^\]]+)\]\(([^)]+\.md(?:#[^)]+)?)\)/g) { print "$1|$2\n"; }' "$doc_file")

  while IFS= read -r recipe; do
    if [ -z "$recipe" ]; then
      continue
    fi
    if ! grep -Fxq -- "$recipe" "$JUST_RECIPES_FILE"; then
      add_error "$rel_file: unknown just recipe '$recipe'"
    fi
  done < <(perl -ne 'while (/\bjust\s+([A-Za-z0-9_-]+)/g) { print "$1\n"; }' "$doc_file")

  while IFS= read -r script_name; do
    if [ ! -f "$ROOT_DIR/scripts/$script_name" ]; then
      add_error "$rel_file: missing script reference scripts/$script_name"
    fi
  done < <(perl -ne 'while (/\bscripts\/([A-Za-z0-9_.-]+\.sh)\b/g) { print "$1\n"; }' "$doc_file")

  in_code=0
  pending_explainer=0
  prose_words=0
  code_words=0
  line_no=0

  while IFS= read -r line; do
    line_no=$((line_no + 1))
    trimmed="$(printf '%s' "$line" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"

    case "$trimmed" in
      '```'*)
        if [ "$in_code" -eq 0 ]; then
          in_code=1
        else
          in_code=0
          pending_explainer=1
        fi
        continue
        ;;
    esac

    if [ "$in_code" -eq 1 ]; then
      line_words="$(grep -oE '[A-Za-z0-9_]+' <<<"$line" | wc -l | tr -d ' ' || true)"
      code_words=$((code_words + line_words))
      continue
    fi

    line_words="$(grep -oE '[A-Za-z0-9_]+' <<<"$line" | wc -l | tr -d ' ' || true)"
    prose_words=$((prose_words + line_words))

    if [ "${trimmed#*—}" != "$trimmed" ]; then
      add_error "$rel_file:$line_no: em dash is not allowed"
    fi
    if [ "${trimmed#*;}" != "$trimmed" ]; then
      add_error "$rel_file:$line_no: semicolon is not allowed"
    fi

    if [ "$pending_explainer" -eq 1 ]; then
      if [ -z "$trimmed" ]; then
        continue
      else
        case "$trimmed" in
          \#*|'```'*)
            add_error "$rel_file:$line_no: code block must be followed by an explanatory paragraph"
            ;;
        esac

        if printf '%s' "$trimmed" | grep -Eq '^[[:space:]]*[-*+][[:space:]]+' \
          || printf '%s' "$trimmed" | grep -Eq '^[[:space:]]*[0-9]+\.[[:space:]]+' \
          || printf '%s' "$trimmed" | grep -Eq '^[[:space:]]*[0-9]+\)[[:space:]]+'; then
            add_error "$rel_file:$line_no: explanatory text after code block must be prose, not a list"
        fi
      fi
      pending_explainer=0
    fi
  done < "$doc_file"

  if [ "$in_code" -eq 1 ]; then
    add_error "$rel_file: unclosed fenced code block"
  fi

  if [ "$prose_words" -le "$code_words" ]; then
    add_error "$rel_file: prose word count ($prose_words) must exceed code word count ($code_words)"
  fi
done < "$DOC_FILES"

if [ -s "$ERRORS_FILE" ]; then
  echo "doc quality check failed:"
  while IFS= read -r err; do
    echo "- $err"
  done < "$ERRORS_FILE"
  exit 1
fi

echo "doc quality check passed"
