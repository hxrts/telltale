#!/usr/bin/env bash
# Detect stale backtick references in docs: unknown just recipes, missing file
# paths, unresolved symbols, feature table mismatches, and version drift.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

# ── Temp Directory ────────────────────────────────────────────────────
TMPDIR_DRIFT="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_DRIFT"' EXIT

ERRORS_FILE="$TMPDIR_DRIFT/errors"
touch "$ERRORS_FILE"

# ── Collect Doc Files ─────────────────────────────────────────────────
DOC_FILES=()
[[ -f CLAUDE.md ]] && DOC_FILES+=(CLAUDE.md)
while IFS= read -r f; do
    DOC_FILES+=("$f")
done < <(find docs -name '*.md' -type f 2>/dev/null | sort)

# ── Cargo Metadata ────────────────────────────────────────────────────
CARGO_META="$TMPDIR_DRIFT/cargo_meta.json"
cargo metadata --no-deps --format-version 1 > "$CARGO_META"

# Workspace package names
jq -r '.packages[].name' "$CARGO_META" | sort -u > "$TMPDIR_DRIFT/pkg_names"
# Also underscore variants
sed 's/-/_/g' "$TMPDIR_DRIFT/pkg_names" > "$TMPDIR_DRIFT/pkg_names_underscore"
cat "$TMPDIR_DRIFT/pkg_names" "$TMPDIR_DRIFT/pkg_names_underscore" | sort -u > "$TMPDIR_DRIFT/crate_tokens"

# Package versions: name<TAB>version
jq -r '.packages[] | "\(.name)\t\(.version)"' "$CARGO_META" > "$TMPDIR_DRIFT/pkg_versions"

# ── Just Recipes ──────────────────────────────────────────────────────
just --summary | tr ' ' '\n' | sort -u > "$TMPDIR_DRIFT/just_recipes"

# ── Build Identifier Set ──────────────────────────────────────────────
{
    for base_dir in src rust; do
        [[ -d "$base_dir" ]] && find "$base_dir" -name '*.rs' -type f -exec grep -ohP '\b[A-Za-z_][A-Za-z0-9_]*\b' {} + || true
    done
    [[ -d lean ]] && find lean -name '*.lean' -type f -exec grep -ohP '\b[A-Za-z_][A-Za-z0-9_]*\b' {} + || true
} | sort -u > "$TMPDIR_DRIFT/repo_identifiers"

# ── Skip Identifiers ──────────────────────────────────────────────────
# Well-known types, traits, keywords that should not trigger warnings.
cat > "$TMPDIR_DRIFT/skip_identifiers" <<'SKIP'
String
Vec
Option
Result
Box
Arc
Rc
Mutex
HashMap
HashSet
BTreeMap
BTreeSet
PathBuf
Path
Ok
Err
Some
None
Self
Sized
Send
Sync
Clone
Copy
Debug
Display
Default
Drop
Eq
Ord
Hash
Iterator
Future
Pin
From
Into
AsRef
Deref
PartialEq
PartialOrd
Serialize
Deserialize
Error
Read
Write
PhantomData
Infallible
Nat
Int
Bool
Prop
Type
List
Array
Char
Float
Unit
Decidable
Repr
Inhabited
Subtype
Sigma
Prod
Sum
Or
And
Iff
Not
True
False
HEq
BEq
Monoid
Group
Ring
Field
Finset
README
SUMMARY
TODO
FIXME
NOTE
WARNING
IMPORTANT
API
CLI
CI
CD
PR
OS
IO
UUID
HTTP
HTTPS
URL
JSON
CBOR
TOML
YAML
WASM
BFT
CRDT
Alice
Bob
Chef
SousChef
Baker
Seller
Client
Server
Worker
Coordinator
Done
Loop
Parallel
Maybe
Just
Nothing
Hello
HelloAck
Goodbye
Ping
Pong
Ack
Commit
Abort
Cancel
Retry
Active
Closed
Draining
Aborted
Faulted
Admitted
Blocked
Failure
Full
SKIP
sort -u "$TMPDIR_DRIFT/skip_identifiers" -o "$TMPDIR_DRIFT/skip_identifiers"

# ── External Prefixes ─────────────────────────────────────────────────
# Qualified paths starting with these are from external crates.
cat > "$TMPDIR_DRIFT/external_prefixes" <<'EXT'
std
core
alloc
serde
serde_json
tokio
rayon
uuid
rand
bincode
thiserror
clap
tempfile
proc_macro2
EXT

# ── Deprecated Identifiers ────────────────────────────────────────────
# name<TAB>reason. Add entries as identifiers are removed or renamed.
cat > "$TMPDIR_DRIFT/deprecated_identifiers" <<'DEP'
DEP

# ── Helpers ───────────────────────────────────────────────────────────

# Check if value is in a sorted file.
in_set() {
    grep -qFx "$1" "$2" 2>/dev/null
}

# Check if snippet looks like a file path.
looks_like_path() {
    local s="$1"
    case "$s" in
        CLAUDE.md|Cargo.toml|justfile|lean/CODE_MAP.md) return 0 ;;
        docs/*|rust/*|lean/*|scripts/*|papers/*|.github/*|src/*) return 0 ;;
        *) return 1 ;;
    esac
}

# Extract the last segment from a qualified path (after final ::).
normalized_symbol_tail() {
    local snippet="$1"
    # Get the last segment after ::
    local last="${snippet##*::}"
    # Extract leading identifier
    if [[ "$last" =~ ^([A-Za-z_][A-Za-z0-9_]*) ]]; then
        echo "${BASH_REMATCH[1]}"
    fi
}

# ── Scan Backtick Code Spans ──────────────────────────────────────────
for doc_file in "${DOC_FILES[@]}"; do
    line_no=0
    while IFS= read -r line; do
        line_no=$((line_no + 1))

        # Extract all backtick code spans from this line.
        # We parse character-by-character to handle multiple spans per line.
        rest="$line"
        while [[ "$rest" == *'`'* ]]; do
            # Skip to first backtick
            rest="${rest#*\`}"
            # If no closing backtick, break
            if [[ "$rest" != *'`'* ]]; then
                break
            fi
            # Extract content up to closing backtick
            snippet="${rest%%\`*}"
            rest="${rest#*\`}"

            # Skip empty or multiline-looking spans
            [[ -z "$snippet" ]] && continue

            # Trim whitespace
            snippet="${snippet#"${snippet%%[![:space:]]*}"}"
            snippet="${snippet%"${snippet##*[![:space:]]}"}"
            [[ -z "$snippet" ]] && continue

            # ── Check deprecated identifiers ────────────────────
            if [[ -s "$TMPDIR_DRIFT/deprecated_identifiers" ]]; then
                dep_reason=""
                while IFS=$'\t' read -r dep_name dep_msg; do
                    if [[ "$snippet" == "$dep_name" ]]; then
                        dep_reason="$dep_msg"
                        break
                    fi
                done < "$TMPDIR_DRIFT/deprecated_identifiers"
                if [[ -n "$dep_reason" ]]; then
                    echo "$doc_file:$line_no: deprecated identifier \`$snippet\` ($dep_reason)" >> "$ERRORS_FILE"
                    continue
                fi
            fi

            # ── just recipe check ───────────────────────────────
            if [[ "$snippet" == "just "* ]]; then
                # Split on space, get second word
                read -ra parts <<< "$snippet"
                if [[ ${#parts[@]} -ge 2 && "${parts[1]}" != -* ]]; then
                    if ! in_set "${parts[1]}" "$TMPDIR_DRIFT/just_recipes"; then
                        echo "$doc_file:$line_no: unknown just recipe \`${parts[1]}\`" >> "$ERRORS_FILE"
                    fi
                fi
                continue
            fi

            # ── File path check ─────────────────────────────────
            if looks_like_path "$snippet"; then
                # Skip globs and .lake/build paths
                if [[ "$snippet" == *'*'* || "$snippet" == *'/.lake/build/'* ]]; then
                    continue
                fi
                if [[ ! -e "$ROOT_DIR/$snippet" ]]; then
                    echo "$doc_file:$line_no: missing referenced path \`$snippet\`" >> "$ERRORS_FILE"
                fi
                continue
            fi

            # ── Workspace crate token check ─────────────────────
            if in_set "$snippet" "$TMPDIR_DRIFT/crate_tokens"; then
                continue
            fi
            # Check if it matches the crate name pattern but is unknown
            if [[ "$snippet" =~ ^(telltale(-[a-z0-9]+)?|effect-scaffold)$ ]]; then
                echo "$doc_file:$line_no: unknown workspace crate \`$snippet\`" >> "$ERRORS_FILE"
                continue
            fi

            # ── Qualified symbol check (contains ::) ────────────
            if [[ "$snippet" == *'::'* ]]; then
                # Skip if contains spaces, braces, parens, commas
                if [[ "$snippet" =~ [[:space:]\{\}\(\),] ]]; then
                    continue
                fi
                # Get the head (before first ::)
                head="${snippet%%::*}"
                if in_set "$head" "$TMPDIR_DRIFT/external_prefixes"; then
                    continue
                fi
                symbol="$(normalized_symbol_tail "$snippet")"
                if [[ -n "$symbol" ]] && ! in_set "$symbol" "$TMPDIR_DRIFT/repo_identifiers"; then
                    echo "$doc_file:$line_no: unresolved repo-local symbol tail \`$snippet\`" >> "$ERRORS_FILE"
                fi
                continue
            fi

            # ── PascalCase identifier check ─────────────────────
            if [[ "$snippet" =~ ^[A-Z][A-Za-z0-9_]+$ ]]; then
                # Skip if in the well-known skip set
                if in_set "$snippet" "$TMPDIR_DRIFT/skip_identifiers"; then
                    continue
                fi
                # Skip single-character (already excluded by regex requiring 2+ chars)
                # Skip ALL_CAPS constants
                if [[ "$snippet" =~ ^[A-Z][A-Z0-9_]+$ ]]; then
                    continue
                fi
                if ! in_set "$snippet" "$TMPDIR_DRIFT/repo_identifiers"; then
                    echo "$doc_file:$line_no: unresolved type or identifier \`$snippet\`" >> "$ERRORS_FILE"
                fi
            fi

        done
    done < "$doc_file"
done

# ── Feature Table Accuracy ────────────────────────────────────────────
# Compare documented features against actual Cargo features.

GETTING_STARTED="docs/02_getting_started.md"
if [[ -f "$GETTING_STARTED" ]]; then
    TARGET_CRATES="telltale
telltale-theory
telltale-choreography
telltale-lean-bridge"

    # Build actual features per target crate (excluding default, _-prefixed,
    # and pure optional-dep features).
    while IFS= read -r crate_name; do
        jq -r --arg cn "$crate_name" '
            .packages[]
            | select(.name == $cn)
            | .features
            | to_entries[]
            | select(
                .key != "default"
                and (.key | startswith("_") | not)
                and (
                    # Exclude features whose sole dep is dep:<feature_name>
                    (.value | length) != 1
                    or .value[0] != ("dep:" + .key)
                )
            )
            | .key
        ' "$CARGO_META" | sort -u > "$TMPDIR_DRIFT/actual_features_${crate_name}"
    done <<< "$TARGET_CRATES"

    # Parse documented features from feature tables in the markdown
    current_crate=""
    in_table=0

    while IFS= read -r gs_line; do
        # Detect heading like #### `telltale`
        if [[ "$gs_line" == '#### '* && "$gs_line" == *'`'* ]]; then
            # Extract text between first pair of backticks
            candidate="${gs_line#*\`}"
            candidate="${candidate%%\`*}"
            candidate="${candidate#"${candidate%%[![:space:]]*}"}"
            candidate="${candidate%"${candidate##*[![:space:]]}"}"
            if echo "$TARGET_CRATES" | grep -qFx "$candidate"; then
                current_crate="$candidate"
            else
                current_crate=""
            fi
            in_table=0
            continue
        fi

        # Detect feature table header
        if [[ -n "$current_crate" ]] && [[ "$gs_line" =~ ^\|[[:space:]]*Feature[[:space:]]*\|[[:space:]]*Default[[:space:]]*\|[[:space:]]*Description[[:space:]]*\| ]]; then
            in_table=1
            continue
        fi

        # Skip separator row
        if [[ $in_table -eq 1 ]] && [[ "$gs_line" =~ ^\|[-[:space:]]+\|[-[:space:]]+\|[-[:space:]]+\|$ ]]; then
            continue
        fi

        # Parse feature row
        if [[ $in_table -eq 1 ]] && [[ "$gs_line" == '|'* ]]; then
            # Extract first cell content
            IFS='|' read -ra cells <<< "$gs_line"
            if [[ ${#cells[@]} -ge 2 ]]; then
                feature="${cells[1]}"
                # Trim whitespace and backticks
                feature="${feature#"${feature%%[![:space:]]*}"}"
                feature="${feature%"${feature##*[![:space:]]}"}"
                feature="${feature#\`}"
                feature="${feature%\`}"
                feature="${feature#"${feature%%[![:space:]]*}"}"
                feature="${feature%"${feature##*[![:space:]]}"}"
                if [[ -n "$feature" ]]; then
                    echo "$feature"
                fi
            fi
            continue
        fi

        # End of table
        if [[ $in_table -eq 1 ]] && [[ "$gs_line" != '|'* ]]; then
            in_table=0
        fi
    done < "$GETTING_STARTED" > "$TMPDIR_DRIFT/doc_features_raw"

    # We need per-crate documented features. Re-parse with crate tracking.
    while IFS= read -r crate_name; do
        : > "$TMPDIR_DRIFT/doc_features_${crate_name}"
    done <<< "$TARGET_CRATES"

    current_crate=""
    in_table=0

    while IFS= read -r gs_line; do
        if [[ "$gs_line" == '#### '* && "$gs_line" == *'`'* ]]; then
            candidate="${gs_line#*\`}"
            candidate="${candidate%%\`*}"
            candidate="${candidate#"${candidate%%[![:space:]]*}"}"
            candidate="${candidate%"${candidate##*[![:space:]]}"}"
            if echo "$TARGET_CRATES" | grep -qFx "$candidate"; then
                current_crate="$candidate"
            else
                current_crate=""
            fi
            in_table=0
            continue
        fi

        if [[ -n "$current_crate" ]] && [[ "$gs_line" =~ ^\|[[:space:]]*Feature[[:space:]]*\|[[:space:]]*Default[[:space:]]*\|[[:space:]]*Description[[:space:]]*\| ]]; then
            in_table=1
            continue
        fi

        if [[ $in_table -eq 1 ]] && [[ "$gs_line" =~ ^\|[-[:space:]]+\|[-[:space:]]+\|[-[:space:]]+\|$ ]]; then
            continue
        fi

        if [[ $in_table -eq 1 ]] && [[ "$gs_line" == '|'* ]]; then
            IFS='|' read -ra cells <<< "$gs_line"
            if [[ ${#cells[@]} -ge 2 ]]; then
                feature="${cells[1]}"
                feature="${feature#"${feature%%[![:space:]]*}"}"
                feature="${feature%"${feature##*[![:space:]]}"}"
                feature="${feature#\`}"
                feature="${feature%\`}"
                feature="${feature#"${feature%%[![:space:]]*}"}"
                feature="${feature%"${feature##*[![:space:]]}"}"
                if [[ -n "$feature" && -n "$current_crate" ]]; then
                    echo "$feature" >> "$TMPDIR_DRIFT/doc_features_${current_crate}"
                fi
            fi
            continue
        fi

        if [[ $in_table -eq 1 ]] && [[ "$gs_line" != '|'* ]]; then
            in_table=0
        fi
    done < "$GETTING_STARTED"

    # Compare actual vs documented features per crate
    while IFS= read -r crate_name; do
        actual_file="$TMPDIR_DRIFT/actual_features_${crate_name}"
        doc_file_feat="$TMPDIR_DRIFT/doc_features_${crate_name}"

        [[ -f "$actual_file" ]] || continue
        sort -u "$doc_file_feat" -o "$doc_file_feat" 2>/dev/null || true

        # Missing in docs (in actual but not in docs)
        while IFS= read -r feat; do
            if ! in_set "$feat" "$doc_file_feat"; then
                echo "docs/02_getting_started.md: feature \`$feat\` exists in \`$crate_name\` but is not documented in feature table" >> "$ERRORS_FILE"
            fi
        done < "$actual_file"

        # Extra in docs (in docs but not in actual)
        if [[ -s "$doc_file_feat" ]]; then
            while IFS= read -r feat; do
                if ! in_set "$feat" "$actual_file"; then
                    echo "docs/02_getting_started.md: feature \`$feat\` is documented for \`$crate_name\` but does not exist in Cargo.toml" >> "$ERRORS_FILE"
                fi
            done < "$doc_file_feat"
        fi
    done <<< "$TARGET_CRATES"
fi

# ── Crate Version Accuracy ────────────────────────────────────────────
# Compare version strings in docs against actual workspace versions.

VERSION_CHECK_FILES=()
while IFS= read -r f; do
    VERSION_CHECK_FILES+=("$f")
done < <(find docs -name '*.md' -type f 2>/dev/null | sort)
[[ -f rust/transport/README.md ]] && VERSION_CHECK_FILES+=(rust/transport/README.md)

for vpath in "${VERSION_CHECK_FILES[@]}"; do
    line_no=0
    while IFS= read -r vline; do
        line_no=$((line_no + 1))

        # Match: crate_name = "version"
        crate_name=""
        declared_version=""

        if [[ "$vline" =~ ^[[:space:]]*(telltale(-[a-z0-9]+)?|effect-scaffold)[[:space:]]*=[[:space:]]*\"([^\"]+)\" ]]; then
            crate_name="${BASH_REMATCH[1]}"
            declared_version="${BASH_REMATCH[3]}"
        # Match: crate_name = { version = "version" ... }
        elif [[ "$vline" =~ ^[[:space:]]*(telltale(-[a-z0-9]+)?|effect-scaffold)[[:space:]]*=[[:space:]]*\{.*version[[:space:]]*=[[:space:]]*\"([^\"]+)\" ]]; then
            crate_name="${BASH_REMATCH[1]}"
            declared_version="${BASH_REMATCH[3]}"
        fi

        if [[ -n "$crate_name" && -n "$declared_version" ]]; then
            expected_version=""
            while IFS=$'\t' read -r pkg_name pkg_ver; do
                if [[ "$pkg_name" == "$crate_name" ]]; then
                    expected_version="$pkg_ver"
                    break
                fi
            done < "$TMPDIR_DRIFT/pkg_versions"

            if [[ -n "$expected_version" && "$declared_version" != "$expected_version" ]]; then
                echo "$vpath:$line_no: \`$crate_name\` version \`$declared_version\` does not match workspace version \`$expected_version\`" >> "$ERRORS_FILE"
            fi
        fi
    done < "$vpath"
done

# ── Report ────────────────────────────────────────────────────────────
if [[ -s "$ERRORS_FILE" ]]; then
    cat "$ERRORS_FILE" >&2
    exit 1
fi

echo "docs semantic drift check passed"
