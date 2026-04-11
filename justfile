# Justfile
# Max parallel threads for Lake/Lean builds

lean_threads := "3"

# Default task
default: book

# Enter the development shell with stale temp variables cleared first.
develop:
    env -u TMPDIR -u TMP -u TEMP nix develop --override-input toolkit path:../toolkit

# Toolkit formatter check.
_toolkit-fmt-check:
    cargo fmt --all -- --check

# Internal toolkit check wrapper.
_toolkit-check name:
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ "{{name}}" == "docs_link_check" ]]; then
      generated=()
      for f in docs/SUMMARY.md docs/book; do
        if [[ -e "$f" ]]; then
          mv "$f" "$f.__toolkit_stash__"
          generated+=("$f")
        fi
      done
      restore() { for f in "${generated[@]}"; do [[ -e "$f.__toolkit_stash__" ]] && mv "$f.__toolkit_stash__" "$f"; done; }
      trap restore EXIT
      ./scripts/toolkit-shell.sh toolkit-xtask check "{{name}}" --repo-root . --config policy/toolkit.toml
      exit 0
    fi
    ./scripts/toolkit-shell.sh toolkit-xtask check "{{name}}" --repo-root . --config policy/toolkit.toml

# Run the full workspace test surface using the CI-safe split test lane.
test-workspace: check-workspace-tests-split

# Run release validation and publish crates.
# Usage:
#   just release <version> [dry_run] [skip_ci] [no_tag] [push] [allow_dirty] [no_require_main]
# Example:
#   just release 4.0.1 true true true false true false   # dry-run + skip ci + no-tag + allow dirty
release \
  version="" \
  dry_run="false" \
  skip_ci="false" \
  no_tag="false" \
  push="false" \
  allow_dirty="false" \
  no_require_main="false":
    #!/usr/bin/env bash
    set -euo pipefail
    args=()
    if [ -n "{{version}}" ]; then
      args+=(--version "{{version}}")
    fi
    if [ "{{dry_run}}" = "true" ]; then
      args+=(--dry-run)
    fi
    if [ "{{skip_ci}}" = "true" ]; then
      args+=(--skip-ci)
    fi
    if [ "{{no_tag}}" = "true" ]; then
      args+=(--no-tag)
    fi
    if [ "{{push}}" = "true" ]; then
      args+=(--push)
    fi
    if [ "{{allow_dirty}}" = "true" ]; then
      args+=(--allow-dirty)
    fi
    if [ "{{no_require_main}}" = "true" ]; then
      args+=(--no-require-main)
    fi
    ./scripts/ops/release.sh "${args[@]}"

# Keep this in the same order as GitHub workflows:
# - check.yml fast checks
# - verify.yml fast lane checks
# - verify.yml scheduled heavy lane checks when lane="full"
ci-dry-run lane="fast":
    #!/usr/bin/env bash
    set -euo pipefail
    tmp_root="${TMPDIR:-/tmp}"
    if [[ ! -d "$tmp_root" ]]; then
      export TMPDIR="/tmp"
    fi
    # Fail fast on doc/index/link drift and other cheap metadata checks before
    # any broader build/test work.
    just check-doc-fast-fail
    cargo fmt --all -- --check
    # Then run the remaining canonical PR-critical verification surface before
    # the broader build/test lanes.
    just check-pr-critical-core
    cargo build --workspace --all-targets --all-features
    # Use RUSTFLAGS to catch rustc warnings (not just clippy lints) as errors
    RUSTFLAGS="-D warnings" cargo clippy --workspace --all-targets --all-features -- -D warnings
    just check-workspace-tests-split
    just check-arch
    just check-telltale-style
    just check-semantic-name-parity
    just check-doc-quality
    just perf-baseline check
    just perf-baseline sla
    just book
    # WASM compilation checks
    just wasm-check
    just wasm-test-all
    # Golden file equivalence tests (fast, no Lean required)
    just test-golden
    just telltale-lean-check
    just telltale-lean-check-extended
    just telltale-lean-check-failing
    just check-parity
    just check-capability-gates
    # Benchmark target compilation checks
    just bench-check
    if [[ "{{lane}}" == "full" ]]; then
      just check-deep-assurance
    fi

# Canonical doc/metadata fast-fail lane used by CI and local dry runs.
check-doc-fast-fail:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp_root="${TMPDIR:-/tmp}"
    if [[ ! -d "$tmp_root" ]]; then
      export TMPDIR="/tmp"
    fi
    just check-doc-links-ci
    just check-docs-as-contract
    just check-docs-semantic-drift
    just check-docs-index
    just check-verification-inventory

# Canonical PR-critical verification lane used by fast CI and local dry runs.
check-pr-critical:
    just check-doc-fast-fail
    just check-pr-critical-core

# Canonical PR-critical verification lane minus the cheap doc/metadata fast-fail
# checks, so local wrappers can run those first without duplication.
check-pr-critical-core:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp_root="${TMPDIR:-/tmp}"
    if [[ ! -d "$tmp_root" ]]; then
      export TMPDIR="/tmp"
    fi
    just check-fast-structure
    just check-focused-assurance
    just check-package-artifacts
    just check-arch-lean
    just check-protocol-machine-placeholders
    just check-parity
    just check-ownership-contracts
    just check-aura-borrowed-lints
    just check-capability-gates
    just check-release-conformance
    just verify-lean-protocol-machine-targets
    just verify-protocols
    just verify-track-a

# Canonical scheduled deep-assurance lane for larger corpora and redundant heavy checks.
check-deep-assurance:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp_root="${TMPDIR:-/tmp}"
    if [[ ! -d "$tmp_root" ]]; then
      export TMPDIR="/tmp"
    fi
    just check-scale-budgets
    just verify-lean-full || true
    just verify-cross-target-matrix
    just verify-track-b
    just verify-properties
    just verify-composition-stress
    just perf-baseline run

# Mirror the markdown link-check action used in GitHub check.yml docs lane
check-doc-links-ci:
    just _toolkit-check docs_link_check

# Canonical fast-fail structural lane: workflow definitions, ledgers, docs snippets,
# Lean bootstrap state, and other cheap schema/convergence gates.
check-fast-structure:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp_root="${TMPDIR:-/tmp}"
    if [[ ! -d "$tmp_root" ]]; then
      export TMPDIR="/tmp"
    fi
    just check-ci-assurance-lanes
    just check-formal-claim-scope
    just check-workflow-actions
    just check-verification-inventory
    just check-bridge-normalization
    just check-fail-closed-mutations
    just check-docs-as-contract
    just check-source-doc-snippets
    just check-lean-metrics-minimal-env
    just check-lean-metrics
    just check-tooling-convergence
    just check-lean-prebuilt
    just check-lean-dependency-pins

# Canonical focused assurance lane: strict Lean-backed correspondence and the
# highest-signal PR-critical semantic/property suites that should fail before broad workspace tests.
check-focused-assurance:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp_root="${TMPDIR:-/tmp}"
    if [[ ! -d "$tmp_root" ]]; then
      export TMPDIR="/tmp"
    fi
    just check-lean-bridge-strict
    just check-compiler-pipeline
    just check-deadlock-automation
    just check-authority-metatheory
    just check-concrete-refinement
    just check-transported-theorem-boundary
    just check-handler-contracts
    just check-extension-dispatch
    just check-semantic-assurance
    just check-runtime-boundaries
    just check-search-tooling
    just check-viewer-tooling

# Verify that CI/workflow ownership flows through the canonical PR/deep lane recipes.
check-ci-assurance-lanes:
    ./scripts/check/ci-assurance-lanes.sh

# Verify that the public formal-verification claim, scope, and TCB wording stay exact.
check-formal-claim-scope:
    ./scripts/check/formal-claim-scope.sh

# Rust style guide lint check (comprehensive)
lint:
    just _toolkit-fmt-check
    just _toolkit-check unsafe_boundary
    just _toolkit-check public_type_width
    just _toolkit-check must_use_public_return
    just _toolkit-check dependency_policy

# Rust style guide lint check (quick - format + clippy only)
lint-quick:
    just _toolkit-fmt-check
    cargo clippy --workspace --all-targets --all-features -- -D warnings

# Periodic broader Clippy style audit, kept out of the default CI lane.
clippy-style-audit:
    cargo clippy --workspace --all-targets --all-features -- \
        -W clippy::must_use_candidate \
        -W clippy::trivially_copy_pass_by_ref \
        -W clippy::needless_pass_by_value \
        -W clippy::manual_let_else \
        -W clippy::unused_async \
        -W clippy::cognitive_complexity \
        -W clippy::fn_params_excessive_bools \
        -W clippy::too_many_arguments

# Rust architecture/style-guide pattern checker
check-arch-rust:
    just _toolkit-check unsafe_boundary
    just _toolkit-check rust_architecture

# TellTale syntax/style check suite (dependency layering, docs references, symbols)
check-telltale-style:
    #!/usr/bin/env bash
    set -euo pipefail
    # Remove generated docs artifacts so the link checker runs against a clean
    # tree, matching CI's fresh checkout.  Restore them afterward so local
    # workflows are unaffected.
    generated=()
    for f in docs/SUMMARY.md docs/book; do
      if [[ -e "$f" ]]; then
        mv "$f" "$f.__ci_stash__"
        generated+=("$f")
      fi
    done
    restore() { for f in "${generated[@]}"; do [[ -e "$f.__ci_stash__" ]] && mv "$f.__ci_stash__" "$f"; done; }
    trap restore EXIT
    just _toolkit-check workspace_layering
    just _toolkit-check docs_link_check
    ./scripts/check/docs-index.sh
    just _toolkit-check text_formatting

# Enforce public tooling/example cutover to generated effect interfaces and owned opens.
check-tooling-convergence:
    ./scripts/check/tooling-convergence.sh

# Validate source markdown DSL snippets against the real parser.
check-source-doc-snippets:
    ./scripts/check/source-doc-snippets.sh

# Narrow subsystem-safe simulator verification path for staged simulator-only changes.
check-simulator-subsystem-staged:
    ./scripts/check/simulator-subsystem.sh

# Self-test the staged simulator subsystem classification logic.
check-simulator-subsystem-self-test:
    ./scripts/check/simulator-subsystem.sh --self-test

# Check that key public verification/capability docs stay aligned with
# source-derived rows and trusted ledgers.
check-docs-as-contract:
    ./scripts/check/docs-as-contract.sh

# Deliberately perturb narrow verification boundaries and prove each gate fails closed.
check-fail-closed-mutations:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp_root="${TMPDIR:-/tmp}"
    if [[ ! -d "$tmp_root" ]]; then
      export TMPDIR="/tmp"
    fi
    cargo test -p telltale-bridge --lib parse_protocol_machine_run_output_rejects_ -- --nocapture
    cargo test -p telltale-machine transported_theorem_boundary_fail_closes_ -- --nocapture
    ./scripts/check/fail-closed-mutations.sh

# Reclaim build space when the local volume is close to exhaustion.
reclaim-build-space-if-needed min_free_mb="2048":
    #!/usr/bin/env bash
    set -euo pipefail
    free_mb="$(df -Pm . | awk 'NR==2 { print $4 }')"
    if [[ "${free_mb}" -lt "{{min_free_mb}}" ]]; then
      echo "Low disk space (${free_mb}MB free); reclaiming Cargo build artifacts"
      rm -rf .tmp target/capability-gates
      cargo clean
    fi

# Run the deterministic extension statement parsing/dispatch regression suites.
check-extension-dispatch:
    cargo test -p telltale-runtime --test extension_integration -- --nocapture
    cargo test -p telltale-runtime --features test-utils --test middleware_semantic_hardening -- --nocapture

# Run the machine-checkable first-party handler/transport contract boundary suites.
check-handler-contracts:
    just reclaim-build-space-if-needed
    mkdir -p .tmp
    TMPDIR=$PWD/.tmp cargo test -p telltale-runtime --test handler_contracts -- --nocapture
    TMPDIR=$PWD/.tmp cargo test -p telltale-runtime --test transport_contracts -- --nocapture
    just reclaim-build-space-if-needed
    TMPDIR=$PWD/.tmp cargo test -p telltale-transport --test transport_contract_profiles -- --nocapture

# Run the Lean-backed regular-fragment deadlock automation suites.
check-deadlock-automation:
    LEAN_NUM_THREADS="{{lean_threads}}" lake --dir lean build telltale_validator
    cargo test -p telltale-types test_reaches_communication_matches_practical_fragment_intent -- --nocapture
    TELLTALE_REQUIRE_LEAN_PROJECTION_RUNNER=1 cargo test -p telltale-bridge --test regular_practical_fragment_checks -- --nocapture
    cargo test --test dsl_runtime_semantics_tests generated_proof_status_exposes_ -- --nocapture

# Run the explicit authority-metatheory theorem slice and runtime support-matrix suites.
check-authority-metatheory:
    LEAN_NUM_THREADS="{{lean_threads}}" lake --dir lean build Runtime.Proofs.AuthorityMetatheory
    cargo test --test dsl_runtime_semantics_tests authority_metatheory_ -- --nocapture

# Run deterministic larger-corpus structural budget suites.
check-scale-budgets:
    ./scripts/check/scale-budgets.sh

# Generate Rust effect interfaces and simulator scaffolds from Telltale DSL declarations.
effect-scaffold dsl out="artifacts/effect_handler_scaffold":
    cargo run -p telltale-runtime --bin effect-scaffold -- --out {{ out }} --dsl {{ dsl }}

# Run a simulator harness config and print a JSON report.
sim-run config:
    cargo run -p telltale-simulator --bin run -- --config {{ config }} --pretty

# Run a simulator harness config and write the JSON report to a file.
sim-run-out config output:
    cargo run -p telltale-simulator --bin run -- --config {{ config }} --output {{ output }} --pretty

# Backward-compatible alias used by CI dry-run pipeline
check-arch: check-arch-rust

# Run full workspace tests in smaller package groups to keep CI memory pressure
# lower than one monolithic `cargo test --workspace`.
check-workspace-tests-split:
    #!/usr/bin/env bash
    set -euo pipefail
    tmpdir="${TMPDIR:-/tmp}"
    mkdir -p "$tmpdir"
    packages=(
      telltale
      telltale-types
      telltale-theory
      telltale-language
      telltale-macros
      telltale-machine
      telltale-runtime
      telltale-transport
      telltale-bridge
      telltale-simulator
      telltale-viewer
      telltale-ui
      telltale-web
      telltale-lints
    )
    for pkg in "${packages[@]}"; do
      echo "==> cargo test -p ${pkg} --all-targets --all-features"
      if [[ "$pkg" == "telltale-bridge" ]]; then
        TMPDIR="$tmpdir" CARGO_BUILD_JOBS=1 CARGO_PROFILE_TEST_DEBUG=0 cargo test -p "$pkg" --all-targets --all-features -- --nocapture
      else
        TMPDIR="$tmpdir" cargo test -p "$pkg" --all-targets --all-features -- --nocapture
      fi
    done

# Lean architecture/style-guide pattern checker
check-arch-lean:
    just _toolkit-check lean_escape_hatches
    just _toolkit-check lean_architecture

# Validate pinned revisions for local Lean dependency checkouts.
check-lean-dependency-pins:
    ./scripts/check/lean-dependency-pins.sh

# Ensure pinned Lean dependency checkouts also have the required prebuilt artifacts.
check-lean-prebuilt:
    ./scripts/bootstrap/ensure-lean-prebuilt.sh

# Build required Lean bridge binaries and fail closed if strict bridge suites would otherwise skip.
check-lean-bridge-strict:
    ./scripts/check/lean-bridge-strict.sh

# Consolidated capability gate checks (byzantine, delegation, envelope, failure, contracts, speculation)
check-capability-gates:
    ./scripts/check/capability-gates.sh --all

# Release theorem-capability and conformance checks
check-release-conformance:
    ./scripts/check/release-conformance.sh

# Performance baseline management (check, freeze, run, sla)
perf-baseline mode="check":
    ./scripts/ops/perf-baseline.sh {{ mode }}

# Prevent new placeholder/stub/TODO markers in executable Lean protocol machine modules.
check-protocol-machine-placeholders:
    ./scripts/check/protocol-machine-placeholders.sh

# Consolidated Lean/Rust parity checks (types, suite, conformance)
check-parity mode="--all":
    ./scripts/check/cross-runtime-parity.sh {{ mode }}

# Focused ownership-contract assertions, delegation negatives, and replay checks.
check-ownership-contracts:
    cargo test -p telltale-machine --lib ownership_
    cargo test -p telltale-machine --test ownership_contracts -- --nocapture
    cargo test -p telltale-machine --test serialization_replay ownership_transfer_ -- --nocapture
    cargo test -p telltale-machine --features multi-thread --test ownership_contracts threaded_ownership_ -- --nocapture
    cargo test -p telltale-machine --features multi-thread --test serialization_replay threaded_ownership_transfer_ -- --nocapture
    cargo test -p telltale-simulator --test ownership_faults -- --nocapture

# Enforce parity type ledger plus deviation registry presence/shape.
check-parity-ledger:
    ./scripts/check/parity-ledger.sh

# Enforce canonical Lean↔Rust protocol-machine semantic-object naming.
check-semantic-name-parity:
    ./scripts/check/lean-rust-semantic-name-parity.sh

# Check for semantic drift in backticked identifiers, paths, crates, features, and versions.
check-docs-semantic-drift:
    just _toolkit-check docs_semantic_drift

# Validate the Document Index in docs/101_introduction.md is complete and titles match.
check-docs-index:
    ./scripts/check/docs-index.sh

# Validate that all remote GitHub Action references in workflows resolve.
check-workflow-actions:
    just _toolkit-check workflow_actions

# Enforce documentation prose style and structure.
check-doc-quality:
    just _toolkit-check docs_prose_quality

# Reject raw session-store ownership mutation outside sanctioned entry points.
check-session-ingress-boundary:
    ./scripts/check/session-ingress-boundary.sh

# Reject raw wall-clock/timer usage in deterministic runtime paths.
check-time-domain-boundaries:
    ./scripts/check/time-domain-boundaries.sh

# Enforce style/serialization boundaries in selected core crates.
check-style-boundaries:
    ./scripts/check/style-boundaries.sh

# Keep a small authoritative verification inventory aligned with source-of-truth metrics.
check-verification-inventory:
    ./scripts/check/verification-inventory.sh

# Validate publishable crate artifacts from their packaged form, plus package-root
# resource boundaries and release-script resume behavior.
check-package-artifacts:
    ./scripts/check/package-artifacts.sh
    ./scripts/check/package-provenance.sh
    ./scripts/check/package-resource-audit.sh
    ./scripts/check/release-recovery.sh

# Audit the trusted bridge normalization surface so new compared fields or
# schema backfills cannot appear silently.
check-bridge-normalization:
    ./scripts/check/bridge-normalization-ledger.sh

# Run the first concrete protocol-machine refinement slice across Lean,
# cooperative Rust, and canonical threaded execution.
check-concrete-refinement:
    cargo test -p telltale-bridge --test protocol_machine_differential_steps -- --nocapture
    cargo test -p telltale-machine --test lean_protocol_machine_equivalence -- --nocapture
    cargo test -p telltale-machine test_reschedule_moves_selected_coro_to_back_of_ready_queue -- --nocapture
    cargo test -p telltale-machine --features multi-thread --test threaded_equivalence test_refinement_slices_match_across_drivers_at_canonical_concurrency -- --exact --nocapture

# Keep the transported-theorem admission boundary explicit across Lean, Rust, and bridge artifacts.
check-transported-theorem-boundary:
    LEAN_NUM_THREADS="{{lean_threads}}" lake --dir lean build Runtime.Proofs.TheoremPack.AdmissionBoundary
    LEAN_NUM_THREADS="{{lean_threads}}" lake --dir lean build protocol_machine_runner
    cargo test -p telltale-machine transported_theorem_boundary_ -- --nocapture
    cargo test -p telltale-bridge --test invariant_verification test_verify_protocol_bundle_emits_transported_theorem_boundary_inventory -- --exact --nocapture

# Run the DSL -> lowering -> export/import -> Lean projection compiler pipeline suites.
check-compiler-pipeline:
    cargo test -p telltale-bridge --test compiler_pipeline_conformance -- --nocapture
    cargo test -p telltale-bridge --test projection_equivalence -- --nocapture
    cargo test -p telltale-bridge --test proptest_json_roundtrip -- --nocapture
    TELLTALE_REQUIRE_LEAN_VALIDATOR=1 cargo test -p telltale-bridge --test lean_integration_tests -- --nocapture
    TELLTALE_REQUIRE_LEAN_VALIDATOR=1 cargo test -p telltale-bridge --test merge_semantics_tests -- --nocapture
    TELLTALE_REQUIRE_LEAN_VALIDATOR=1 cargo test -p telltale-bridge --test proptest_projection -- --nocapture

# Run the highest-signal semantic assurance suites directly.
check-semantic-assurance:
    cargo test -p telltale-machine runtime_semantic_lifecycle_harness_covers_seeded_state_machine_paths -- --nocapture
    cargo test -p telltale-machine runtime_semantic_lifecycle_adversarial_corpus_is_deterministic -- --nocapture
    cargo test -p telltale-machine --test replay_persistence_identity -- --nocapture
    cargo test -p telltale-machine reconfiguration_snapshot_restore_preserves_plan_execution_history -- --nocapture
    cargo test -p telltale-machine --features multi-thread --test threaded_equivalence -- --nocapture
    cargo test -p telltale-simulator --test harness_contracts -- --nocapture
    cargo test -p telltale-bridge --test reconfiguration_recovery_harness -- --nocapture
    cargo test -p telltale-bridge --test protocol_bundle_admission_contracts reconfiguration_plan_with_runtime_topology_artifacts_matches_lean_step_validation -- --exact --nocapture
    cargo test -p telltale-bridge --test protocol_machine_cross_target_tests -- --nocapture
    cargo test --test dsl_runtime_semantics_tests -- --nocapture

# Run targeted boundary suites that prove fail-closed language, topology, and runtime substrate behavior.
check-runtime-boundaries:
    cargo test -p telltale-runtime --test authority_control_flow_corpus -- --nocapture
    cargo test -p telltale-bridge --test protocol_bundle_admission_contracts -- --nocapture
    cargo test -p telltale-runtime topology_exports_canonical_reconfiguration_placement_artifacts -- --nocapture
    cargo test -p telltale-runtime --test runtime_substrate_contracts -- --nocapture
    cargo test -p telltale-runtime --test generated_topology_public_path -- generated_topology_public_path_executes_end_to_end_in_a_temp_crate --exact --nocapture

# Keep proc-macro UI boundary contracts under targeted trybuild coverage.
check-macro-boundaries:
    cargo test -p telltale-macros --test macro_ui -- --nocapture

# Aggregate the Aura-derived boundary checks borrowed into Telltale.
check-aura-borrowed-lints:
    just check-session-ingress-boundary
    just check-time-domain-boundaries
    just check-style-boundaries
    just check-viewer-tooling-boundaries
    just check-docs-semantic-drift
    just check-verification-inventory
    just check-durable-boundaries
    just check-durable-assurance
    just check-macro-boundaries

# Keep typed durability artifacts on the authoritative machine/runtime side.
check-durable-boundaries:
    ./scripts/check/durable-boundaries.sh

# Enforce the generic search crate boundary and docs alignment.
check-search-boundaries:
    bash ./scripts/check/search-boundaries.sh

# Focused Lean-backed search fairness gate: theorem-pack, parity fixture, and
# inventory alignment.
check-search-fairness:
    bash ./scripts/check/search-fairness.sh

# Focused telltale-search verification split: package compile and boundary checks.
check-search-tooling:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp_root="${TMPDIR:-/tmp}"
    if [[ ! -d "$tmp_root" ]]; then
      export TMPDIR="/tmp"
    fi
    cargo test -p telltale-search -- --nocapture
    cargo test -p telltale-simulator --test search_integration -- --nocapture
    cargo test -p telltale-viewer --test search_adapter -- --nocapture
    cargo test -p telltale-search --example basic_search --no-run
    if rustup target list --installed | grep -q '^wasm32-unknown-unknown$'; then
      cargo check -p telltale-search --target wasm32-unknown-unknown --tests
    fi
    just check-search-fairness
    just check-search-bench-tooling
    just check-search-boundaries

# Focused durability verification split: machine contracts, simulator assurance, and boundaries.
check-durable-assurance:
    TMPDIR=/tmp cargo test -p telltale-machine --test durable_contracts -- --nocapture
    TMPDIR=/tmp cargo test -p telltale-simulator --test durable_assurance -- --nocapture
    just check-durable-boundaries

# Enforce the shared viewer/webapp boundary and docs alignment.
check-viewer-tooling-boundaries:
    ./scripts/check/viewer-tooling-boundaries.sh

# Focused shared webapp verification split: pure model, ownership/lints, and UI integration.
check-viewer-tooling:
    cargo test -p telltale-viewer --lib
    cargo test -p telltale-ui --test shell_rendering --test interactive_workspace -- --nocapture
    cargo check -p telltale-web
    just check-viewer-tooling-boundaries

# Refresh generated Lean metrics in docs
sync-lean-metrics:
    ./scripts/ops/sync-lean-metrics.sh

# Verify generated Lean metrics are fresh
check-lean-metrics:
    ./scripts/ops/sync-lean-metrics.sh --check

# Verify lean-metrics freshness without assuming optional local tools are on PATH.
check-lean-metrics-minimal-env:
    env PATH="/usr/bin:/bin" TZ=UTC bash ./scripts/ops/sync-lean-metrics.sh --check

# Sync reproducibility rows in all three papers (pinned commit, DOI, Lean stats).
paper-repro-sync:
    bash scripts/ops/paper-repro-rows.sh --sync papers/paper1.tex papers/paper2.tex papers/paper3.tex

# Check reproducibility rows are up to date (current commit, DOI metadata, Lean stats).
paper-repro-check:
    bash scripts/ops/paper-repro-rows.sh --check papers/paper1.tex papers/paper2.tex papers/paper3.tex

# Strict reproducibility check, including DOI being set in papers/artifact_metadata.env.
paper-repro-check-strict:
    bash scripts/ops/paper-repro-rows.sh --check --strict-doi papers/paper1.tex papers/paper2.tex papers/paper3.tex

# Generate machine-readable publication supplement manifest.
artifact-manifest:
    bash scripts/ops/generate-artifact-manifest.sh

# Clean publication artifact logs.
artifact-clean:
    rm -rf artifacts/papers
    rm -rf artifacts/_tmp_backup_* artifacts/_tmp_generated_*

# One-command publication supplement verification.
artifact-check:
    mkdir -p artifacts/papers
    just paper-repro-sync
    just paper-repro-check | tee artifacts/papers/paper-repro-check.log
    just escape | tee artifacts/papers/check-escape.log
    just verify-protocols | tee artifacts/papers/verify-protocols.log
    just paper | tee artifacts/papers/paper-build.log
    just artifact-manifest | tee artifacts/papers/artifact-manifest.log

# Generate Lean style conformance baseline report
lean-style-baseline:
    ./scripts/ops/generate-lean-style-baseline.sh

# Check WASM compilation for runtime and core crates
wasm-check:
    #!/usr/bin/env bash
    set -euo pipefail
    wasm_target="$(mktemp -d "${TMPDIR:-/tmp}/telltale-wasm-check.XXXXXX")"
    trap 'rm -rf "$wasm_target"' EXIT
    CARGO_TARGET_DIR="$wasm_target" cargo check --package telltale-runtime --target wasm32-unknown-unknown --features wasm
    CARGO_TARGET_DIR="$wasm_target" cargo check --package telltale --target wasm32-unknown-unknown --features wasm

# Check benchmark target compilation without running benchmarks
bench-check:
    cargo bench --workspace --no-run

# Check the search benchmark/profiling surface explicitly, including the saved-profile script.
check-search-bench-tooling:
    #!/usr/bin/env bash
    set -euo pipefail
    bash -n scripts/ops/profile-search-bench.sh
    cargo bench -p telltale-search --bench search_profiles --bench search_machine_phases --bench search_runtime_overheads --no-run
    cargo bench -p telltale-search --features multi-thread --bench search_profiles --bench search_machine_phases --bench search_runtime_overheads --no-run

# Profile a single protocol machine runtime benchmark with samply.
profile-protocol-machine bench:
    samply record cargo bench -p telltale-machine --bench protocol_machine_runtime_bench -- {{ bench }}

# Profile one search benchmark with samply.
profile-search bench_target="search_profiles" bench="serial_chain_256":
    ./scripts/ops/profile-search-bench.sh {{ bench_target }} {{ bench }}

# Profile the canonical serial chain workload.
profile-search-chain:
    ./scripts/ops/profile-search-bench.sh search_profiles serial_chain_256

# Profile the rebuild-heavy canonical serial workload.
profile-search-rebuild:
    ./scripts/ops/profile-search-bench.sh search_profiles serial_grid_rebuild_heavy_32x32

# Profile the threaded exact single-lane search workload.
profile-search-threaded:
    ./scripts/ops/profile-search-bench.sh search_profiles threaded_exact_single_lane_grid_32x32 --features multi-thread

# Profile machine-only search cost without runtime/executor artifact overhead.
profile-search-machine-only:
    ./scripts/ops/profile-search-bench.sh search_runtime_overheads runtime_machine_only_chain_256

# Profile runtime artifact generation after a completed search run.
profile-search-artifact:
    ./scripts/ops/profile-search-bench.sh search_runtime_overheads runtime_observation_export_chain_256

# Profile invariant-checking cost on a prepared frontier snapshot.
profile-search-invariants:
    ./scripts/ops/profile-search-bench.sh search_runtime_overheads runtime_invariant_check_frontier_512

# Profile the paused-role scheduler hotspot with samply.
profile-protocol-machine-scheduler:
    samply record cargo run -p telltale-machine --release --bin profile_driver -- scheduler-many-paused-run-only 200000

# Profile the repeated load/reuse hotspot with samply.
profile-protocol-machine-load:
    samply record cargo run -p telltale-machine --release --bin profile_driver -- repeated-load-reuse

# Profile the replay/nullifier hotspot with samply.
profile-protocol-machine-replay:
    samply record cargo run -p telltale-machine --release --bin profile_driver -- send-recv-replay-nullifier

# Profile the repeated fixed-topology open path with samply.
profile-protocol-machine-open:
    samply record cargo run -p telltale-machine --release --bin profile_driver -- repeated-open-same-image

# Build WASM example with wasm-pack
wasm-build:
    #!/usr/bin/env bash
    set -euo pipefail
    wasm_target="$(mktemp -d "${TMPDIR:-/tmp}/telltale-wasm-build.XXXXXX")"
    trap 'rm -rf "$wasm_target"' EXIT
    cd examples/wasm
    CARGO_TARGET_DIR="$wasm_target" wasm-pack build --target web

# Run the example WASM tests under Node.
wasm-test:
    #!/usr/bin/env bash
    set -euo pipefail
    shim_root="$(mktemp -d)"
    wasm_target="target/wasm-test/node"
    trap 'rm -rf "$shim_root" "$wasm_target"' EXIT
    rm -rf "$wasm_target"
    mkdir -p "$(dirname "$wasm_target")"
    mkdir -p "$shim_root/env"
    cat >"$shim_root/env/index.js" <<'EOF'
    module.exports = new Proxy(
      {},
      {
        get(_target, prop) {
          if (prop === "__esModule") {
            return true;
          }
          return function () {};
        },
      },
    );
    EOF
    cd examples/wasm
    CARGO_TARGET_DIR="$wasm_target" NODE_PATH="$shim_root" wasm-pack test --node

# Run all repository-managed WASM tests without requiring a browser driver.
wasm-test-all:
    #!/usr/bin/env bash
    set -euo pipefail
    repo_root="$PWD"
    mkdir -p "$repo_root/.tmp"
    wasm_root="$(mktemp -d "$repo_root/.tmp/wasm-test-all.XXXXXX")"
    shim_root="$wasm_root/shim"
    machine_target="$wasm_root/machine"
    choreo_target="$wasm_root/choreo"
    example_target="$wasm_root/example"
    trap 'rm -rf "$wasm_root"' EXIT
    mkdir -p "$shim_root/env"
    cat >"$shim_root/env/index.js" <<'EOF'
    module.exports = new Proxy(
      {},
      {
        get(_target, prop) {
          if (prop === "__esModule") {
            return true;
          }
          return function () {};
        },
      },
    );
    EOF
    CARGO_TARGET_DIR="$machine_target" NODE_PATH="$shim_root" wasm-pack test --node rust/machine --features wasm -- --nocapture
    CARGO_TARGET_DIR="$choreo_target" NODE_PATH="$shim_root" wasm-pack test --node rust/runtime --features "wasm _wasm_integration_tests" -- --nocapture
    cd examples/wasm
    CARGO_TARGET_DIR="$example_target" NODE_PATH="$shim_root" wasm-pack test --node

# Format .tell DSL files (prints to stdout unless --write is used)
choreo-fmt *FILES:
    cargo run -p telltale-runtime --bin choreo-fmt -- {{ FILES }}

choreo-fmt-write *FILES:
    cargo run -p telltale-runtime --bin choreo-fmt -- --write {{ FILES }}

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

# Build paper PDFs (requires texlive from nix develop shell)
paper:
    #!/usr/bin/env bash
    set -euo pipefail
    cd papers
    mkdir -p build
    for p in paper1 paper2 paper3; do
        echo "Building $p.pdf..."
        pdflatex -interaction=nonstopmode -output-directory=build "$p.tex" > /dev/null || true
        pdflatex -interaction=nonstopmode -output-directory=build "$p.tex" > /dev/null
    done
    echo "Built: build/paper1.pdf build/paper2.pdf build/paper3.pdf"

# Clean paper build artifacts
paper-clean:
    rm -rf papers/build

# Build viewer tailwind CSS (static copy + runtime asset)
viewer-css:
    #!/usr/bin/env bash
    set -euo pipefail
    cd rust/web
    npm install --prefer-offline 2>/dev/null
    mkdir -p ./public/assets
    npx tailwindcss -c tailwind.config.cjs -i ./styles/app.css -o ./styles/tailwind.css --minify
    cp ./styles/tailwind.css ./public/assets/tailwind.css

# Serve the simulator viewer webapp
serve-viewer: viewer-css
    #!/usr/bin/env bash
    set -euo pipefail
    cd rust/web
    dx serve

# Serve docs locally with live reload
serve: summary _gen-assets
    #!/usr/bin/env bash
    trap 'just _clean-assets' EXIT
    mdbook serve --open
    exit 1

# Check Lean codebase for escape hatches (sorry, axiom, unsafe, partial, theorem shells, etc.)
escape:
    just _toolkit-check lean_escape_hatches

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
    ./scripts/bootstrap/ensure-lean-prebuilt.sh

telltale-lean-check: lean-init
    # Export choreography data, build the Lean runner, and verify three roles with logs
    mkdir -p lean/artifacts
    cargo run -p telltale-bridge --features exporter --bin lean-bridge-exporter -- --input rust/bridge/fixtures/lean-sample.tell --role Chef --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-chef.json
    cargo run -p telltale-bridge --features exporter --bin lean-bridge-exporter -- --input rust/bridge/fixtures/lean-sample.tell --role SousChef --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-sous.json
    cargo run -p telltale-bridge --features exporter --bin lean-bridge-exporter -- --input rust/bridge/fixtures/lean-sample.tell --role Baker --choreography-out lean/artifacts/lean-sample-choreography.json --program-out lean/artifacts/lean-sample-program-baker.json
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-chef.json --log lean/artifacts/runner-chef.log --json-log lean/artifacts/runner-chef.json
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-sous.json --log lean/artifacts/runner-sous.log --json-log lean/artifacts/runner-sous.json
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-sample-choreography.json --program lean/artifacts/lean-sample-program-baker.json --log lean/artifacts/runner-baker.log --json-log lean/artifacts/runner-baker.json

telltale-lean-check-extended: lean-init
    # Extended scenario with looped service and dessert fan-out
    mkdir -p lean/artifacts
    cargo run -p telltale-bridge --features exporter --bin lean-bridge-exporter -- --input rust/bridge/fixtures/lean-extended.tell --role Chef --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-chef.json
    cargo run -p telltale-bridge --features exporter --bin lean-bridge-exporter -- --input rust/bridge/fixtures/lean-extended.tell --role SousChef --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-sous.json
    cargo run -p telltale-bridge --features exporter --bin lean-bridge-exporter -- --input rust/bridge/fixtures/lean-extended.tell --role Baker --choreography-out lean/artifacts/lean-extended-choreography.json --program-out lean/artifacts/lean-extended-program-baker.json
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-chef.json --log lean/artifacts/runner-extended-chef.log --json-log lean/artifacts/runner-extended-chef.json
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-sous.json --log lean/artifacts/runner-extended-sous.log --json-log lean/artifacts/runner-extended-sous.json
    ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-extended-choreography.json --program lean/artifacts/lean-extended-program-baker.json --log lean/artifacts/runner-extended-baker.log --json-log lean/artifacts/runner-extended-baker.json

# Regenerate golden files from Lean (requires Lean build)
regenerate-golden: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    cargo run -p telltale-bridge --bin golden --features golden -- regenerate

# Check for golden file drift (fails if golden files are outdated)
check-golden-drift: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    cargo run -p telltale-bridge --bin golden --features golden -- check

# List all golden test cases
list-golden:
    cargo run -p telltale-bridge --bin golden --features golden -- list

# Run golden file equivalence tests (fast, no Lean required)
test-golden:
    cargo test -p telltale-bridge --test golden_equivalence_tests

# Run live Lean equivalence tests (requires Lean build)
test-live-equivalence: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    cargo test -p telltale-bridge --test live_equivalence_tests

# Intentional failure fixture: labels mismatch.
telltale-lean-check-failing: lean-init
    mkdir -p lean/artifacts
    cargo run -p telltale-bridge --features exporter --bin lean-bridge-exporter -- --input rust/bridge/fixtures/lean-failing.tell --role Chef --choreography-out lean/artifacts/lean-failing-choreography.json --program-out lean/artifacts/lean-failing-program-chef.json
    # Corrupt the exported program to introduce a label mismatch
    perl -0pi -e 's/"name": "Pong"/"name": "WrongLabel"/' lean/artifacts/lean-failing-program-chef.json
    LEAN_NUM_THREADS={{ lean_threads }} lake --dir lean build telltale_validator
    ! ./lean/.lake/build/bin/telltale_validator --choreography lean/artifacts/lean-failing-choreography.json --program lean/artifacts/lean-failing-program-chef.json --log lean/artifacts/runner-failing-chef.log --json-log lean/artifacts/runner-failing-chef.json

# Emit protocol-bundle artifacts by running the bridge bundle tests.
export-protocol-bundles:
    cargo test -p telltale-bridge --test invariant_verification_tests -- --nocapture

# Rust/Lean protocol machine trace correspondence checks.
verify-protocol-machine-correspondence:
    cargo test -p telltale-bridge --test protocol_machine_correspondence_tests
    cargo test -p telltale-bridge --test protocol_machine_differential_steps

# Track A gate: naming/API changes must preserve behavior.
verify-track-a:
    cargo test -p telltale-machine --test trace_corpus
    cargo test -p telltale-machine --test strict_tick_equality
    cargo test -p telltale-machine --test lean_protocol_machine_equivalence

# Lean-side invariant verification checks for protocol bundles.
verify-invariants:
    cargo test -p telltale-bridge --test invariant_verification

# Targeted protocol verification lane (fast CI).
verify-protocols:
    just verify-protocol-machine-correspondence
    just verify-invariants
    cargo test -p telltale-bridge --test schema_version_tests

# Track B gate: semantic-alignment acceptance, including cross-target checks.
verify-track-b:
    just verify-protocols
    just verify-cross-target-matrix
    just check-parity --conformance

# Full Lean build gate for nightly/scheduled validation.
verify-lean-full: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} elan run leanprover/lean4:v4.26.0 lake --dir lean build

# Targeted Lean protocol machine architecture modules for fast CI checks.
verify-lean-protocol-machine-targets: lean-init
    LEAN_NUM_THREADS={{ lean_threads }} elan run leanprover/lean4:v4.26.0 lake --dir lean build Runtime.ProtocolMachine.API Runtime.ProtocolMachine.Runtime

# Cross-target runtime comparison lane.
verify-cross-target-matrix:
    #!/usr/bin/env bash
    set -euo pipefail
    wasm_target="$(mktemp -d "${TMPDIR:-/tmp}/telltale-cross-target-wasm.XXXXXX")"
    trap 'rm -rf "$wasm_target"' EXIT
    cargo test -p telltale-machine --features multi-thread --test threaded_equivalence
    cargo test -p telltale-machine --test lean_protocol_machine_equivalence
    CARGO_TARGET_DIR="$wasm_target" wasm-pack test --node rust/machine --features wasm -- --nocapture
    cargo test -p telltale-bridge --test protocol_machine_cross_target_tests

# Composition/concurrency stress lane.
verify-composition-stress:
    cargo test -p telltale-machine --features multi-thread --test threaded_lane_runtime -- --nocapture
    cargo test -p telltale-bridge --test protocol_machine_composition_stress -- --nocapture

# Property-based verification lane.
verify-properties:
    cargo test -p telltale-bridge --test property_tests
    cargo test -p telltale-bridge --test proptest_projection
    cargo test -p telltale-bridge --test proptest_json_roundtrip
    cargo test -p telltale-bridge --test proptest_async_subtyping

# Generate normalized traces for bridge-level protocol machine correspondence fixtures.
generate-test-traces:
    cargo test -p telltale-bridge --test protocol_machine_correspondence_tests -- --nocapture
