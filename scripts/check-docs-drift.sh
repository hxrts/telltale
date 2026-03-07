#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

DOC_FILES=(
  "docs/01_introduction.md"
  "docs/02_getting_started.md"
  "docs/03_architecture.md"
  "docs/04_code_organization.md"
)

VERSION_CHECK_PATHS=(
  "docs"
  "rust/transport/README.md"
)

tmp_metadata="$(mktemp)"
tmp_workspace_crates="$(mktemp)"
tmp_workspace_versions="$(mktemp)"
tmp_doc_features="$(mktemp)"
tmp_doc_features_filtered="$(mktemp)"
tmp_actual_features="$(mktemp)"
tmp_missing_in_docs="$(mktemp)"
tmp_extra_in_docs="$(mktemp)"
tmp_doc_version_hits="$(mktemp)"
trap 'rm -f "$tmp_metadata" "$tmp_workspace_crates" "$tmp_workspace_versions" "$tmp_doc_features" "$tmp_doc_features_filtered" "$tmp_actual_features" "$tmp_missing_in_docs" "$tmp_extra_in_docs" "$tmp_doc_version_hits"' EXIT

cargo metadata --no-deps --format-version 1 >"$tmp_metadata"

jq -r '
  . as $m
  | $m.workspace_members[] as $wid
  | $m.packages[]
  | select(.id == $wid)
  | .name
' "$tmp_metadata" | sort -u >"$tmp_workspace_crates"

jq -r '
  . as $m
  | $m.workspace_members[] as $wid
  | $m.packages[]
  | select(.id == $wid)
  | [.name, .version]
  | @tsv
' "$tmp_metadata" | sort -u >"$tmp_workspace_versions"

status=0

while IFS= read -r referenced_crate; do
  if [[ -z "$referenced_crate" ]]; then
    continue
  fi
  if ! grep -Fxq "$referenced_crate" "$tmp_workspace_crates" && [[ "$referenced_crate" != "telltale-transport" ]]; then
    echo "error: docs reference unknown crate '$referenced_crate'" >&2
    status=1
  fi
done < <(
  grep -hroE '`(telltale(-[a-z0-9]+)?|effect-scaffold)`' "${DOC_FILES[@]}" \
    | tr -d '`' \
    | sort -u
)

awk '
  BEGIN {
    crate = ""
    in_table = 0
  }
  {
    if ($0 ~ /^#### / && $0 ~ /`/) {
      split($0, heading_parts, /`/)
      crate = heading_parts[2]
      in_table = 0
      next
    }
    if (crate != "" && $0 ~ /^\| Feature \| Default \| Description \|/) {
      in_table = 1
      next
    }
    if (in_table && $0 ~ /^\|[-[:space:]]+\|[-[:space:]]+\|[-[:space:]]+\|$/) {
      next
    }
    if (in_table && $0 ~ /^\|/) {
      line = $0
      gsub(/^\|[[:space:]]*/, "", line)
      split(line, parts, /\|/)
      feature = parts[1]
      gsub(/[[:space:]]/, "", feature)
      gsub(/`/, "", feature)
      if (feature != "") {
        print crate "\t" feature
      }
      next
    }
    if (in_table && $0 !~ /^\|/) {
      in_table = 0
    }
  }
' docs/02_getting_started.md | sort -u >"$tmp_doc_features"

target_crates=(
  "telltale"
  "telltale-theory"
  "telltale-choreography"
  "telltale-lean-bridge"
)

for crate in "${target_crates[@]}"; do
  while IFS= read -r feature; do
    if [[ "$feature" == "default" || "$feature" == _* ]]; then
      continue
    fi
    printf '%s\t%s\n' "$crate" "$feature"
  done < <(
    jq -r --arg crate "$crate" '
      .packages[]
      | select(.name == $crate)
      | .features
      | to_entries[]
      | select(.key != "default")
      | select((.key | startswith("_")) | not)
      | select((.value | length != 1) or (.value[0] != ("dep:" + .key)))
      | .key
    ' "$tmp_metadata" | sort -u
  )
done | sort -u >"$tmp_actual_features"

awk -F $'\t' '
  $1 == "telltale" ||
  $1 == "telltale-theory" ||
  $1 == "telltale-choreography" ||
  $1 == "telltale-lean-bridge"
' "$tmp_doc_features" | sort -u >"$tmp_doc_features_filtered"

comm -23 "$tmp_actual_features" "$tmp_doc_features_filtered" >"$tmp_missing_in_docs" || true
comm -13 "$tmp_actual_features" "$tmp_doc_features_filtered" >"$tmp_extra_in_docs" || true

if [[ -s "$tmp_missing_in_docs" ]]; then
  echo "error: missing documented features in docs/02_getting_started.md:" >&2
  sed 's/^/  - /' "$tmp_missing_in_docs" >&2
  status=1
fi

if [[ -s "$tmp_extra_in_docs" ]]; then
  echo "error: stale features documented in docs/02_getting_started.md:" >&2
  sed 's/^/  - /' "$tmp_extra_in_docs" >&2
  status=1
fi

rg -n '^\s*(telltale(-[a-z0-9]+)?|effect-scaffold)\s*=\s*("[^"]+"|\{[^}]*version\s*=\s*"[^"]+")' "${VERSION_CHECK_PATHS[@]}" \
  >"$tmp_doc_version_hits" || true

while IFS= read -r hit; do
  file="${hit%%:*}"
  rest="${hit#*:}"
  line_no="${rest%%:*}"
  line="${rest#*:}"

  crate="$(sed -E 's/^[[:space:]]*([a-z0-9-]+)[[:space:]]*=.*/\1/' <<<"$line")"
  declared_version="$(sed -nE 's/^[[:space:]]*[a-z0-9-]+[[:space:]]*=[[:space:]]*"([^"]+)".*/\1/p' <<<"$line")"
  if [[ -z "$declared_version" ]]; then
    declared_version="$(sed -nE 's/.*version[[:space:]]*=[[:space:]]*"([^"]+)".*/\1/p' <<<"$line")"
  fi
  expected_version="$(awk -F $'\t' -v crate="$crate" '$1 == crate { print $2; exit }' "$tmp_workspace_versions")"

  if [[ -z "$expected_version" ]]; then
    continue
  fi

  if [[ "$declared_version" != "$expected_version" ]]; then
    echo "error: $file:$line_no has $crate version $declared_version (expected $expected_version)" >&2
    status=1
  fi
done <"$tmp_doc_version_hits"

if [[ "$status" -eq 0 ]]; then
  echo "docs drift check passed"
fi

exit "$status"
