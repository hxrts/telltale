#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

DOC_FILES=(
  "docs/00_introduction.md"
  "docs/01_getting_started.md"
  "docs/02_architecture.md"
  "docs/03_crate_organization.md"
)

tmp_metadata="$(mktemp)"
tmp_doc_features="$(mktemp)"
tmp_doc_features_filtered="$(mktemp)"
tmp_actual_features="$(mktemp)"
tmp_missing_in_docs="$(mktemp)"
tmp_extra_in_docs="$(mktemp)"
trap 'rm -f "$tmp_metadata" "$tmp_doc_features" "$tmp_doc_features_filtered" "$tmp_actual_features" "$tmp_missing_in_docs" "$tmp_extra_in_docs"' EXIT

cargo metadata --no-deps --format-version 1 >"$tmp_metadata"

declare -A workspace_crates=()
while IFS= read -r crate; do
  workspace_crates["$crate"]=1
done < <(
  jq -r '
    . as $m
    | $m.workspace_members[] as $wid
    | $m.packages[]
    | select(.id == $wid)
    | .name
  ' "$tmp_metadata" | sort -u
)

declare -A allowed_external_crates=(
  ["telltale-transport"]=1
)

status=0

while IFS= read -r referenced_crate; do
  if [[ -z "$referenced_crate" ]]; then
    continue
  fi
  if [[ -z "${workspace_crates[$referenced_crate]+x}" && -z "${allowed_external_crates[$referenced_crate]+x}" ]]; then
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
    if (match($0, /^#### .*`([^`]+)`/, m)) {
      crate = m[1]
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
' docs/01_getting_started.md | sort -u >"$tmp_doc_features"

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
  echo "error: missing documented features in docs/01_getting_started.md:" >&2
  sed 's/^/  - /' "$tmp_missing_in_docs" >&2
  status=1
fi

if [[ -s "$tmp_extra_in_docs" ]]; then
  echo "error: stale features documented in docs/01_getting_started.md:" >&2
  sed 's/^/  - /' "$tmp_extra_in_docs" >&2
  status=1
fi

if [[ "$status" -eq 0 ]]; then
  echo "docs drift check passed"
fi

exit "$status"
