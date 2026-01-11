# Justfile

# Max parallel threads for Lake/Lean builds
lean_threads := "3"

# Default task
default: book

# Run the same checks as GitHub CI
ci-dry-run:
    cargo fmt --all -- --check
    # Use RUSTFLAGS to catch rustc warnings (not just clippy lints) as errors
    RUSTFLAGS="-D warnings" cargo clippy --workspace --all-targets --all-features -- -D warnings
    cargo test --workspace --all-targets --all-features
    just book
    # WASM compilation checks
    just wasm-check
    # Golden file equivalence tests (fast, no Lean required)
    just test-golden
    # Lean runner disabled - rumpsteak_runner target removed in V2 refactor
    # TODO: Re-enable once V2 runner is implemented
    # just rumpsteak-lean-check
    # just rumpsteak-lean-check-extended
    # just rumpsteak-lean-check-failing

# Rust style guide lint check (comprehensive)
lint:
    ./scripts/lint-check.sh

# Rust style guide lint check (quick - format + clippy only)
lint-quick:
    ./scripts/lint-check.sh --quick

# Check WASM compilation for choreography and core crates
wasm-check:
    cargo check --package rumpsteak-aura-choreography --target wasm32-unknown-unknown --features wasm
    cargo check --package rumpsteak-aura --target wasm32-unknown-unknown --features wasm

# Build WASM example with wasm-pack
wasm-build:
    cd examples/wasm-ping-pong && wasm-pack build --target web

# Run WASM tests (requires Chrome/Firefox)
wasm-test:
    cd examples/wasm-ping-pong && wasm-pack test --headless --chrome

# Format choreography DSL files (prints to stdout unless --write is used)
choreo-fmt *FILES:
    cargo run -p rumpsteak-aura-choreography --bin choreo-fmt -- {{FILES}}

choreo-fmt-write *FILES:
    cargo run -p rumpsteak-aura-choreography --bin choreo-fmt -- --write {{FILES}}

# Install git hooks for pre-commit checks
install-hooks:
    git config core.hooksPath .githooks
    @echo "Git hooks installed. Pre-commit checks will run automatically."

# Generate docs/SUMMARY.md from Markdown files in docs/ and subfolders
summary:
    #!/usr/bin/env bash
    set -euo pipefail

    docs="docs"
    build_dir="$docs/book"
    out="$docs/SUMMARY.md"

    echo "# Summary" > "$out"
    echo "" >> "$out"

    # Find all .md files under docs/, excluding SUMMARY.md itself and the build output
    while IFS= read -r f; do
        rel="${f#$docs/}"

        # Skip SUMMARY.md
        [ "$rel" = "SUMMARY.md" ] && continue

        # Skip files under the build output directory
        case "$f" in "$build_dir"/*) continue ;; esac

        # Derive the title from the first H1; fallback to filename
        title="$(grep -m1 '^# ' "$f" | sed 's/^# *//')"
        if [ -z "$title" ]; then
            base="$(basename "${f%.*}")"
            title="$(printf '%s\n' "$base" \
                | tr '._-' '   ' \
                | awk '{for(i=1;i<=NF;i++){ $i=toupper(substr($i,1,1)) substr($i,2) }}1')"
        fi

        # Indent two spaces per directory depth
        depth="$(awk -F'/' '{print NF-1}' <<<"$rel")"
        indent="$(printf '%*s' $((depth*2)) '')"

        echo "${indent}- [$title](${rel})" >> "$out"
    done < <(find "$docs" -type f -name '*.md' -not -name 'SUMMARY.md' -not -path "$build_dir/*" | LC_ALL=C sort)

    echo "Wrote $out"

# Build the book after regenerating the summary
book: summary
    mdbook-mermaid install .
    mv mermaid.min.js mermaid-init.js docs/ 2>/dev/null || true
    mdbook build
    rm -f docs/mermaid-init.js docs/mermaid.min.js

# Serve locally with live reload
serve: summary
    #!/usr/bin/env bash
    # Trap SIGINT (Ctrl+C) for graceful shutdown
    trap 'echo -e "\nShutting down mdbook server..."; exit 0' INT

    # Install mermaid assets
    mdbook-mermaid install .
    mv mermaid.min.js mermaid-init.js docs/ 2>/dev/null || true

    # Try to serve on the default port, fallback to next available port if in use
    for port in 3000 3001 3002 3003 3004 3005; do
        if ! lsof -Pi :$port -sTCP:LISTEN -t >/dev/null 2>&1; then
            echo "Starting mdbook server on http://localhost:$port"
            echo "Press Ctrl+C to stop the server"
            mdbook serve --port $port --open
            exit 0
        fi
    done
    # If we get here, all ports are in use, just show the error
    echo "Error: All ports 3000-3005 are already in use" >&2
    exit 1

# Test Lean installation
lean-test:
    @echo "Testing Lean installation..."
    @lean --version
    @lake --version

# Initialize Lean project if not already initialized
lean-init:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ ! -f lean/lakefile.lean ]; then
        echo "Initializing Lean project..."
        cd lean && lake init rumpsteak_lean math
        echo "Lean project initialized!"
    else
        echo "Lean project already initialized"
    fi

rumpsteak-lean-check: lean-init
    # Export rust choreography data, build the Lean runner, and verify three roles with logs
    mkdir -p lean/artifacts
    cargo run -p rumpsteak-lean-bridge --features exporter --bin lean-bridge-exporter -- --input lean/choreo/lean-sample.choreo --role Chef --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-chef.json
    cargo run -p rumpsteak-lean-bridge --features exporter --bin lean-bridge-exporter -- --input lean/choreo/lean-sample.choreo --role SousChef --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-sous.json
    cargo run -p rumpsteak-lean-bridge --features exporter --bin lean-bridge-exporter -- --input lean/choreo/lean-sample.choreo --role Baker --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-baker.json
    LEAN_NUM_THREADS={{lean_threads}} lake --dir lean build rumpsteak_runner
    ./lean/.lake/build/bin/rumpsteak_runner --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-chef.json --log lean/artifacts/runner-chef.log --json-log lean/artifacts/runner-chef.json
    ./lean/.lake/build/bin/rumpsteak_runner --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-sous.json --log lean/artifacts/runner-sous.log --json-log lean/artifacts/runner-sous.json
    ./lean/.lake/build/bin/rumpsteak_runner --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-baker.json --log lean/artifacts/runner-baker.log --json-log lean/artifacts/runner-baker.json

rumpsteak-lean-check-extended: lean-init
    # Extended scenario with looped service and dessert fan-out
    mkdir -p lean/artifacts
    cargo run -p rumpsteak-lean-bridge --features exporter --bin lean-bridge-exporter -- --input lean/choreo/lean-extended.choreo --role Chef --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-chef.json
    cargo run -p rumpsteak-lean-bridge --features exporter --bin lean-bridge-exporter -- --input lean/choreo/lean-extended.choreo --role SousChef --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-sous.json
    cargo run -p rumpsteak-lean-bridge --features exporter --bin lean-bridge-exporter -- --input lean/choreo/lean-extended.choreo --role Baker --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-baker.json
    LEAN_NUM_THREADS={{lean_threads}} lake --dir lean build rumpsteak_runner
    ./lean/.lake/build/bin/rumpsteak_runner --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-chef.json --log lean/artifacts/runner-extended-chef.log --json-log lean/artifacts/runner-extended-chef.json
    ./lean/.lake/build/bin/rumpsteak_runner --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-sous.json --log lean/artifacts/runner-extended-sous.log --json-log lean/artifacts/runner-extended-sous.json
    ./lean/.lake/build/bin/rumpsteak_runner --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-baker.json --log lean/artifacts/runner-extended-baker.log --json-log lean/artifacts/runner-extended-baker.json

# Regenerate golden files from Lean (requires Lean build)
regenerate-golden: lean-init
    LEAN_NUM_THREADS={{lean_threads}} lake --dir lean build rumpsteak_runner
    cargo run -p rumpsteak-lean-bridge --bin golden --features golden -- regenerate

# Check for golden file drift (fails if golden files are outdated)
check-golden-drift: lean-init
    LEAN_NUM_THREADS={{lean_threads}} lake --dir lean build rumpsteak_runner
    cargo run -p rumpsteak-lean-bridge --bin golden --features golden -- check

# List all golden test cases
list-golden:
    cargo run -p rumpsteak-lean-bridge --bin golden --features golden -- list

# Run golden file equivalence tests (fast, no Lean required)
test-golden:
    cargo test -p rumpsteak-lean-bridge --test golden_equivalence_tests

# Run live Lean equivalence tests (requires Lean build)
test-live-equivalence: lean-init
    LEAN_NUM_THREADS={{lean_threads}} lake --dir lean build rumpsteak_runner
    cargo test -p rumpsteak-lean-bridge --test live_equivalence_tests

# Intentional failure fixture: labels mismatch.
rumpsteak-lean-check-failing: lean-init
    mkdir -p lean/artifacts
    cargo run -p rumpsteak-lean-bridge --features exporter --bin lean-bridge-exporter -- --input lean/choreo/lean-failing.choreo --role Chef --choreography-out lean/artifacts/lean-failing-choreography.json --program-out lean/artifacts/lean-failing-program-chef.json
    # Corrupt the exported program to introduce a label mismatch
    perl -0pi -e 's/"label": "Pong"/"label": "WrongLabel"/' lean/artifacts/lean-failing-program-chef.json
    LEAN_NUM_THREADS={{lean_threads}} lake --dir lean build rumpsteak_runner
    ! ./lean/.lake/build/bin/rumpsteak_runner --choreography lean/artifacts/lean-failing-choreography.json --program lean/artifacts/lean-failing-program-chef.json --log lean/artifacts/runner-failing-chef.log --json-log lean/artifacts/runner-failing-chef.json
