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
    just check-arch
    just check-arch-lean
    just check-failure-capabilities
    just check-envelope-conformance
    just check-vm-placeholders
    just check-parity-ledger
    just check-lean-metrics
    # Benchmark target compilation checks
    just bench-check
    just book
    # WASM compilation checks
    just wasm-check
    # Golden file equivalence tests (fast, no Lean required)
    just test-golden
    just telltale-lean-check
    just telltale-lean-check-extended
    just telltale-lean-check-failing

# Rust style guide lint check (comprehensive)
lint:
    ./scripts/check-lint.sh

# Rust style guide lint check (quick - format + clippy only)
lint-quick:
    ./scripts/check-lint.sh --quick

# Rust architecture/style-guide pattern checker
check-arch-rust:
    ./scripts/check-arch-rust.sh

# Lean architecture/style-guide pattern checker
check-arch-lean:
    ./scripts/check-arch-lean.sh

# Failure theorem-capability conformance checks
check-failure-capabilities:
    ./scripts/check-failure-capabilities.sh

# Envelope theorem-capability and conformance checks
check-envelope-conformance:
    ./scripts/check-envelope-conformance.sh

# Prevent new placeholder/stub/TODO markers in executable Lean VM modules.
check-vm-placeholders:
    ./scripts/check-vm-placeholders.sh

# Lean/Rust VM parity-contract + deviation-ledger checks
check-parity-ledger:
    ./scripts/check-parity-ledger.sh

# Refresh generated Lean metrics in docs
sync-lean-metrics:
    ./scripts/sync-lean-metrics.sh

# Verify generated Lean metrics are fresh
check-lean-metrics:
    ./scripts/sync-lean-metrics.sh --check

# Generate Lean style conformance baseline report
lean-style-baseline:
    ./scripts/gen-lean-style-baseline.sh

# Check WASM compilation for choreography and core crates
wasm-check:
    cargo check --package telltale-choreography --target wasm32-unknown-unknown --features wasm
    cargo check --package telltale --target wasm32-unknown-unknown --features wasm

# Check benchmark target compilation without running benchmarks
bench-check:
    cargo bench --workspace --no-run

# Build WASM example with wasm-pack
wasm-build:
    cd examples/wasm-ping-pong && wasm-pack build --target web

# Run WASM tests (requires Chrome/Firefox)
wasm-test:
    cd examples/wasm-ping-pong && wasm-pack test --headless --chrome

# Format choreography DSL files (prints to stdout unless --write is used)
choreo-fmt *FILES:
    cargo run -p telltale-choreography --bin choreo-fmt -- {{ FILES }}

choreo-fmt-write *FILES:
    cargo run -p telltale-choreography --bin choreo-fmt -- --write {{ FILES }}

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

# Generate transient build assets (mermaid, mathjax theme override)
_gen-assets:
    #!/usr/bin/env bash
    set -euo pipefail
    mdbook-mermaid install . > /dev/null 2>&1 || true
    # Patch mermaid-init.js with null guards for mdbook 0.5.x theme buttons
    sed -i.bak 's/document\.getElementById(\(.*\))\.addEventListener/const el = document.getElementById(\1); if (el) el.addEventListener/' mermaid-init.js && rm -f mermaid-init.js.bak
    # Generate theme/index.hbs with MathJax v2 inline $ config injected before MathJax loads
    mkdir -p theme
    mdbook init --theme /tmp/mdbook-theme-gen <<< $'n\n' > /dev/null 2>&1
    sed 's|<script async src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.1/MathJax.js?config=TeX-AMS-MML_HTMLorMML"></script>|<script>window.MathJax = { tex2jax: { inlineMath: [["$","$"],["\\\\(","\\\\)"]], displayMath: [["$$","$$"],["\\\\[","\\\\]"]], processEscapes: true } };</script>\n        <script async src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.1/MathJax.js?config=TeX-AMS-MML_HTMLorMML"></script>|' /tmp/mdbook-theme-gen/theme/index.hbs > theme/index.hbs
    rm -rf /tmp/mdbook-theme-gen

# Clean transient build assets
_clean-assets:
    rm -f mermaid-init.js mermaid.min.js
    rm -rf theme

# Build the book after regenerating the summary
book: summary _gen-assets
    mdbook build && just _clean-assets

# Serve locally with live reload
serve: summary _gen-assets
    #!/usr/bin/env bash
    trap 'just _clean-assets' EXIT
    mdbook serve --open
    exit 1

# Check Lean codebase for escape hatches (sorry, axiom, unsafe, partial, etc.)
escape:
    ./scripts/check-escape.sh

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
        cd lean && lake init telltale_lean math
        echo "Lean project initialized!"
    else
        echo "Lean project already initialized"
    fi

telltale-lean-check: lean-init
    # Export rust choreography data, build the Lean runner, and verify three roles with logs
    mkdir -p lean/artifacts
    cargo run -p telltale-lean-bridge --features exporter --bin lean-bridge-exporter -- --input fixtures/choreo/lean-sample.choreo --role Chef --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-chef.json
    cargo run -p telltale-lean-bridge --features exporter --bin lean-bridge-exporter -- --input fixtures/choreo/lean-sample.choreo --role SousChef --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-sous.json
    cargo run -p telltale-lean-bridge --features exporter --bin lean-bridge-exporter -- --input fixtures/choreo/lean-sample.choreo --role Baker --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-baker.json
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-chef.json --log lean/artifacts/runner-chef.log --json-log lean/artifacts/runner-chef.json
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-sous.json --log lean/artifacts/runner-sous.log --json-log lean/artifacts/runner-sous.json
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-baker.json --log lean/artifacts/runner-baker.log --json-log lean/artifacts/runner-baker.json

telltale-lean-check-extended: lean-init
    # Extended scenario with looped service and dessert fan-out
    mkdir -p lean/artifacts
    cargo run -p telltale-lean-bridge --features exporter --bin lean-bridge-exporter -- --input fixtures/choreo/lean-extended.choreo --role Chef --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-chef.json
    cargo run -p telltale-lean-bridge --features exporter --bin lean-bridge-exporter -- --input fixtures/choreo/lean-extended.choreo --role SousChef --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-sous.json
    cargo run -p telltale-lean-bridge --features exporter --bin lean-bridge-exporter -- --input fixtures/choreo/lean-extended.choreo --role Baker --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-baker.json
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-chef.json --log lean/artifacts/runner-extended-chef.log --json-log lean/artifacts/runner-extended-chef.json
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-sous.json --log lean/artifacts/runner-extended-sous.log --json-log lean/artifacts/runner-extended-sous.json
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-baker.json --log lean/artifacts/runner-extended-baker.log --json-log lean/artifacts/runner-extended-baker.json

# Regenerate golden files from Lean (requires Lean build)
regenerate-golden: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    cargo run -p telltale-lean-bridge --bin golden --features golden -- regenerate

# Check for golden file drift (fails if golden files are outdated)
check-golden-drift: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    cargo run -p telltale-lean-bridge --bin golden --features golden -- check

# List all golden test cases
list-golden:
    cargo run -p telltale-lean-bridge --bin golden --features golden -- list

# Run golden file equivalence tests (fast, no Lean required)
test-golden:
    cargo test -p telltale-lean-bridge --test golden_equivalence_tests

# Run live Lean equivalence tests (requires Lean build)
test-live-equivalence: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    cargo test -p telltale-lean-bridge --test live_equivalence_tests

# Intentional failure fixture: labels mismatch.
telltale-lean-check-failing: lean-init
    mkdir -p lean/artifacts
    cargo run -p telltale-lean-bridge --features exporter --bin lean-bridge-exporter -- --input fixtures/choreo/lean-failing.choreo --role Chef --choreography-out lean/artifacts/lean-failing-choreography.json --program-out lean/artifacts/lean-failing-program-chef.json
    # Corrupt the exported program to introduce a label mismatch
    perl -0pi -e 's/"name": "Pong"/"name": "WrongLabel"/' lean/artifacts/lean-failing-program-chef.json
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    ! ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-failing-choreography.json --program lean/artifacts/lean-failing-program-chef.json --log lean/artifacts/runner-failing-chef.log --json-log lean/artifacts/runner-failing-chef.json

# Emit protocol-bundle artifacts by running the bridge bundle tests.
export-protocol-bundles:
    cargo test -p telltale-lean-bridge --test invariant_verification_tests -- --nocapture

# Rust/Lean VM trace correspondence checks.
verify-vm-correspondence:
    cargo test -p telltale-lean-bridge --test vm_correspondence_tests
    cargo test -p telltale-lean-bridge --test vm_differential_step_tests

# Track A gate: naming/API changes must preserve behavior.
verify-track-a:
    cargo test -p telltale-vm --test trace_corpus
    cargo test -p telltale-vm --test strict_tick_equality
    cargo test -p telltale-vm --test lean_vm_equivalence

# Lean-side invariant verification checks for protocol bundles.
verify-invariants:
    cargo test -p telltale-lean-bridge --test invariant_verification_tests

# Targeted protocol verification lane (fast CI).
verify-protocols:
    just verify-vm-correspondence
    just verify-invariants
    cargo test -p telltale-lean-bridge --test schema_version_tests

# Track B gate: semantic-alignment acceptance, including cross-target checks.
verify-track-b:
    just verify-protocols
    just verify-cross-target-matrix
    just vm-strict-conformance

# Full Lean build gate for nightly/scheduled validation.
verify-lean-full: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} elan run leanprover/lean4:v4.26.0 lake --dir lean build

# Targeted Lean VM architecture modules for fast CI checks.
verify-lean-vm-targets: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} elan run leanprover/lean4:v4.26.0 lake --dir lean build Runtime.VM.API Runtime.VM.Runtime

# Cross-target runtime comparison lane.
verify-cross-target-matrix:
    cargo test -p telltale-vm --features multi-thread --test threaded_equivalence
    cargo test -p telltale-vm --test lean_vm_equivalence
    wasm-pack test --node rust/vm --features wasm -- --nocapture
    cargo test -p telltale-lean-bridge --test vm_cross_target_matrix_tests

# Composition/concurrency stress lane.
verify-composition-stress:
    cargo test -p telltale-vm --features multi-thread --test threaded_lane_runtime -- --nocapture
    cargo test -p telltale-lean-bridge --test vm_composition_stress_tests -- --nocapture

# Property-based verification lane.
verify-properties:
    cargo test -p telltale-lean-bridge --test property_tests
    cargo test -p telltale-lean-bridge --test proptest_projection
    cargo test -p telltale-lean-bridge --test proptest_json_roundtrip
    cargo test -p telltale-lean-bridge --test proptest_async_subtyping

# Generate normalized traces for bridge-level VM correspondence fixtures.
generate-test-traces:
    cargo test -p telltale-lean-bridge --test vm_correspondence_tests -- --nocapture

# Strict Lean-core VM conformance lane (cooperative + threaded backends).
vm-strict-conformance:
    ./scripts/vm-strict-conformance.sh
