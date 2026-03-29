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
require_pattern docs/32_testing_verification_inventory.md 'blanket public claim that "Telltale is' "verification inventory must explicitly reject the blanket end-to-end formal-verification claim"
require_pattern docs/32_testing_verification_inventory.md 'formally verified" end to end.' "verification inventory must explicitly reject the blanket end-to-end formal-verification claim"
require_pattern docs/32_testing_verification_inventory.md "## Claimed Surface" "verification inventory must describe the claimed surface"
require_pattern docs/32_testing_verification_inventory.md "## Out of Scope / Assumption Boundaries" "verification inventory must describe assumption boundaries"
require_pattern docs/32_testing_verification_inventory.md "## Public TCB Ledger" "verification inventory must carry the public TCB ledger"
require_pattern docs/32_testing_verification_inventory.md "## Refinement Coverage Map" "verification inventory must map the current refinement coverage"
require_pattern docs/32_testing_verification_inventory.md '| Per-step event stream, `session_type_counts`, `ready_queue`, and `blocked` snapshots |' "verification inventory refinement map must include the per-step state boundary"
require_pattern docs/32_testing_verification_inventory.md "| Rust/Lean bridge normalization and interchange |" "verification inventory TCB ledger must include the bridge trust surface"
require_pattern docs/32_testing_verification_inventory.md "| Release/package scripts and generated resources |" "verification inventory TCB ledger must include artifact/release trust"

forbid_pattern docs/05_theory.md "implements these concepts in Rust with formal verification in Lean." "docs/05_theory.md still overclaims end-to-end formal verification"
forbid_pattern rust/bridge/src/lib.rs "enabling formal verification of" "rust/bridge crate docs still overclaim formal verification"
forbid_pattern rust/types/src/lib.rs "enabling formal verification and proof correspondence." "rust/types crate docs still overclaim formal verification"

echo "formal-claim-scope: ok"
