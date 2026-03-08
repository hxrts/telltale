#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

DOCS_DIR="$ROOT_DIR/docs"

mapfile -t DOC_FILES < <(
  find "$DOCS_DIR" -type f -name "*.md" ! -path "*/book/*" ! -name "SUMMARY.md" | sort
)

if (( ${#DOC_FILES[@]} == 0 )); then
  echo "no docs found"
  exit 1
fi

declare -A DOC_TITLES
for doc_file in "${DOC_FILES[@]}"; do
  title="$(sed -n 's/^# //p' "$doc_file" | head -n 1)"
  if [[ -n "$title" ]]; then
    DOC_TITLES["$(realpath "$doc_file")"]="$title"
  fi
done

declare -A JUST_RECIPES
while IFS= read -r line; do
  line="${line%%$'\r'}"
  line="$(sed -e 's/^[[:space:]]*//' <<<"$line")"
  if [[ -z "$line" || "$line" == Available\ recipes* ]]; then
    continue
  fi
  recipe="${line%% *}"
  recipe="${recipe%:}"
  if [[ -n "$recipe" ]]; then
    JUST_RECIPES["$recipe"]=1
  fi
done < <(just --list)

errors=()
for doc_file in "${DOC_FILES[@]}"; do
  rel_file="${doc_file#$ROOT_DIR/}"

  while IFS='|' read -r label target; do
    target_file="${target%%#*}"
    target_path="$(realpath -m "$(dirname "$doc_file")/$target_file")"
    if [[ ! -f "$target_path" ]]; then
      errors+=("$rel_file: missing linked file $target")
      continue
    fi

    title="${DOC_TITLES[$target_path]+_}"
    if [[ -n "$title" ]]; then
      expected="${DOC_TITLES[$target_path]}"
      if [[ "$label" != "$expected" ]]; then
        errors+=("$rel_file: link text '$label' does not match title '$expected' for $target")
      fi
    fi
  done < <(perl -ne 'while (/\[([^\]]+)\]\(([^)]+\.md(?:#[^)]+)?)\)/g) { print "$1|$2\n"; }' "$doc_file")

  while IFS= read -r recipe; do
    if [[ -z "${JUST_RECIPES[$recipe]+x}" ]]; then
      errors+=("$rel_file: unknown just recipe '$recipe'")
    fi
  done < <(perl -ne 'while (/\bjust\s+([A-Za-z0-9_-]+)/g) { print "$1\n"; }' "$doc_file")

  while IFS= read -r script_name; do
    if [[ ! -f "$ROOT_DIR/scripts/$script_name" ]]; then
      errors+=("$rel_file: missing script reference scripts/$script_name")
    fi
  done < <(perl -ne 'while (/\bscripts\/([A-Za-z0-9_.-]+\.sh)\b/g) { print "$1\n"; }' "$doc_file")

  in_code=0
  pending_explainer=0
  prose_words=0
  code_words=0
  line_no=0

  while IFS= read -r line; do
    (( line_no += 1 ))

    trimmed="$(printf '%s' "$line" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"

    if [[ "$trimmed" == '```'* ]]; then
      if (( in_code == 0 )); then
        in_code=1
      else
        in_code=0
        pending_explainer=1
      fi
      continue
    fi

    if (( in_code == 1 )); then
      line_words="$(grep -oE '[A-Za-z0-9_]+' <<<"$line" | wc -l | tr -d ' ' || true)"
      (( code_words += line_words ))
      continue
    fi

    line_words="$(grep -oE '[A-Za-z0-9_]+' <<<"$line" | wc -l | tr -d ' ' || true)"
    (( prose_words += line_words ))

    if [[ "$line" == *"—"* ]]; then
      errors+=("$rel_file:$line_no: em dash is not allowed")
    fi
    if [[ "$line" == *";"* ]]; then
      errors+=("$rel_file:$line_no: semicolon is not allowed")
    fi

    if (( pending_explainer == 1 )); then
      if [[ -z "$trimmed" ]]; then
        continue
      fi

      if [[ "$trimmed" == '#'*
        || "$trimmed" == '```'* ]]; then
        errors+=("$rel_file:$line_no: code block must be followed by an explanatory paragraph")
      elif [[ "$trimmed" == -* || "$trimmed" == '*'* ]]; then
        errors+=("$rel_file:$line_no: explanatory text after code block must be prose, not a list")
      elif [[ "$trimmed" =~ ^[0-9]+\.[[:space:]]* ]]; then
        errors+=("$rel_file:$line_no: explanatory text after code block must be prose, not a list")
      fi
      pending_explainer=0
    fi
  done < "$doc_file"

  if (( in_code == 1 )); then
    errors+=("$rel_file: unclosed fenced code block")
  fi

  if (( prose_words <= code_words )); then
    errors+=("$rel_file: prose word count ($prose_words) must exceed code word count ($code_words)")
  fi
done

if (( ${#errors[@]} > 0 )); then
  echo "doc quality check failed:"
  for err in "${errors[@]}"; do
    echo "- $err"
  done
  exit 1
fi

echo "doc quality check passed"
