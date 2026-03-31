#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

require_pattern() {
  local file="$1"
  local pattern="$2"
  local message="$3"
  if ! rg -Fq "${pattern}" "${file}"; then
    echo "error: ${message}" >&2
    exit 1
  fi
}

forbid_pattern() {
  local file="$1"
  local pattern="$2"
  local message="$3"
  if rg -Fq "${pattern}" "${file}"; then
    echo "error: ${message}" >&2
    exit 1
  fi
}

require_pattern docs/32_testing_verification_inventory.md "## Current Formal Verification Claim" "verification inventory must declare the current formal verification claim"
require_pattern docs/32_testing_verification_inventory.md "Telltale is formally verified for the declared shipped surface documented in" "verification inventory must state the final formal-verification claim"
require_pattern docs/32_testing_verification_inventory.md "## Claimed Surface" "verification inventory must describe the claimed surface"
require_pattern docs/32_testing_verification_inventory.md "## Compiler and Macro Claim Boundary" "verification inventory must define the compiler and macro claim boundary"
require_pattern docs/32_testing_verification_inventory.md "## Artifact Correspondence Claim" "verification inventory must define the artifact correspondence claim"
require_pattern docs/32_testing_verification_inventory.md "the current public formal-verification claim does not include any Rust parser," "verification inventory must explicitly exclude Rust compiler paths from the current formal claim"
require_pattern docs/32_testing_verification_inventory.md '`tell!` macro expansion are outside the formal claim' "verification inventory must explicitly exclude tell! macro expansion from the current formal claim"
require_pattern docs/32_testing_verification_inventory.md "## Out of Scope / Assumption Boundaries" "verification inventory must describe assumption boundaries"
require_pattern docs/32_testing_verification_inventory.md "First-class protocol-critical capability semantics are in scope." "verification inventory must explicitly scope protocol-critical capability semantics in"
require_pattern docs/32_testing_verification_inventory.md "General host application authorization is out of scope." "verification inventory must explicitly scope general host authorization out"
require_pattern docs/32_testing_verification_inventory.md "## Public TCB Ledger" "verification inventory must carry the public TCB ledger"
require_pattern docs/32_testing_verification_inventory.md "## Final Surface Audit" "verification inventory must include the final surface audit"
require_pattern docs/32_testing_verification_inventory.md "## Final Public Claim Text" "verification inventory must include the final public claim text"
require_pattern docs/32_testing_verification_inventory.md "## Refinement Coverage Map" "verification inventory must map the current refinement coverage"
require_pattern docs/32_testing_verification_inventory.md '| Per-step event stream, theorem-defined `pre_state`/`post_state`, selected coroutine/type state, `session_type_counts`, `ready_queue`, and `blocked` snapshots |' "verification inventory refinement map must include the per-step state boundary"
require_pattern docs/32_testing_verification_inventory.md "| Rust/Lean bridge normalization and interchange |" "verification inventory TCB ledger must include the bridge trust surface"
require_pattern docs/32_testing_verification_inventory.md "| Release/package scripts and generated resources |" "verification inventory TCB ledger must include artifact/release trust"
require_pattern README.md "Telltale is formally verified for the declared shipped surface documented in" "README must carry the final public formal-verification claim"
require_pattern docs/03_architecture.md "The current formal-verification claim is narrower than this full architecture" "architecture docs must explicitly scope the formal claim below the full Rust compiler/runtime architecture"
require_pattern rust/language/src/lib.rs "intentionally outside the current formal-verification claim" "language crate docs must explicitly exclude Rust compiler-pipeline APIs from the current formal claim"
require_pattern rust/runtime/src/compiler/mod.rs "intentionally outside the current" "runtime compiler docs must explicitly scope compiler helpers outside the current formal claim"

forbid_pattern docs/32_testing_verification_inventory.md 'blanket public claim that "Telltale is' "verification inventory must no longer use the old blanket-claim rejection wording"
forbid_pattern docs/32_testing_verification_inventory.md 'formally verified" end to end.' "verification inventory must no longer use the old blanket-claim rejection wording"
forbid_pattern docs/05_theory.md "implements these concepts in Rust with formal verification in Lean." "docs/05_theory.md still overclaims end-to-end formal verification"
forbid_pattern docs/06_choreographic_dsl.md "tell! is part of the current formal-verification claim" "docs/06_choreographic_dsl.md must not claim tell! is formally verified"
forbid_pattern rust/bridge/src/lib.rs "enabling formal verification of" "rust/bridge crate docs still overclaim formal verification"
forbid_pattern rust/types/src/lib.rs "enabling formal verification and proof correspondence." "rust/types crate docs still overclaim formal verification"

echo "formal-claim-scope: ok"
