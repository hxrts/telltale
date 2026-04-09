#!/usr/bin/env bash
# Verify that docs/902_verification_inventory.md metrics match actual values
# derived from CODE_MAP.md, justfile recipe counts, and macro UI fixture counts.
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

errors=()

explicit_failure_timeout_events=(
  TimeoutIssued
  CancellationRequested
  Cancelled
  FailureBranchEntered
  SessionTerminal
)

authority_ownership_suites=(
  rust/machine/tests/ownership_contracts.rs
  rust/simulator/tests/ownership_faults.rs
)

lean_correspondence_strict_suites=(
  rust/bridge/tests/lean_trace_validation.rs
  rust/bridge/tests/property_tests.rs
  rust/bridge/tests/protocol_bundle_admission_contracts.rs
  rust/bridge/tests/protocol_machine_correspondence_tests.rs
  rust/bridge/tests/protocol_machine_differential_steps.rs
  rust/bridge/tests/capability_model_correspondence.rs
  rust/bridge/tests/heap_lean_parity.rs
  rust/simulator/tests/lean_reference_parity.rs
)

identity_replay_suites=(
  rust/machine/tests/serialization_replay.rs
  rust/machine/tests/replay_persistence_identity.rs
  rust/bridge/tests/semantic_object_roundtrip.rs
  rust/bridge/tests/protocol_machine_cross_target_tests.rs
  rust/bridge/tests/reconfiguration_recovery_harness.rs
)

commitment_progress_suites=(
  rust/machine/tests/unit/protocol_machine/tests_semantic_state.rs
  rust/machine/tests/conformance_lean.rs
  rust/machine/tests/threaded_equivalence.rs
  rust/machine/src/runtime_contracts.rs
)

cross_mode_semantic_parity_suites=(
  rust/machine/tests/threaded_equivalence.rs
  rust/machine/tests/wasm_trace_equivalence.rs
  rust/bridge/tests/semantic_object_roundtrip.rs
  rust/bridge/tests/protocol_machine_cross_target_tests.rs
)

fail_closed_lowering_admission_suites=(
  rust/language/src/compiler/parser/mod.rs
  rust/runtime/tests/authority_compile_fail.rs
  rust/runtime/tests/authority_control_flow_corpus.rs
  rust/machine/src/runtime_contracts.rs
  rust/machine/src/composition.rs
)

structure_reconfiguration_suites=(
  rust/machine/src/engine/runtime_exec/semantic_state.rs
  rust/machine/tests/ownership_contracts.rs
  rust/machine/src/composition.rs
  rust/bridge/tests/protocol_bundle_admission_contracts.rs
  rust/runtime/tests/generated_topology_public_path.rs
)

semantic_lifecycle_invariant_suites=(
  rust/machine/src/engine/runtime_exec/semantic_state.rs
)

adversarial_lifecycle_cases=(
  stale_late_result_after_handoff
  owner_crash_before_handoff
  owner_crash_after_handoff
  timeout_vs_cancellation_race
  retry_after_terminalization
  duplicate_publication_attempt
  observed_read_use_on_authoritative_path
  missing_canonical_handle_on_parity_critical_path
  blocked_progress_escalation
  immediate_effect_misuse
)

dsl_runtime_semantics_suites=(
  rust/tests/dsl_runtime_semantics_tests.rs
)

simulator_semantic_contract_categories=(
  parity_progress_contracts
  exact_once_effect_resolution
  canonical_publication_uniqueness
  authoritative_observed_separation
  progress_escalation_visibility
  semantic_object_coherence
)

theorem_pack_admission_suites=(
  rust/bridge/tests/protocol_bundle_admission_contracts.rs
  rust/bridge/tests/invariant_verification.rs
  rust/machine/src/runtime_contracts.rs
  rust/tests/dsl_runtime_semantics_tests.rs
)

distributed_topology_semantic_harness_suites=(
  rust/simulator/tests/distributed.rs
  rust/machine/tests/topology_effect_ingress.rs
  rust/runtime/tests/generated_topology_public_path.rs
)

agreement_composition_runtime_semantic_suites=(
  rust/machine/src/effect/core_types.rs
  rust/machine/src/semantic_objects.rs
  rust/machine/tests/threaded_equivalence.rs
  rust/tests/dsl_runtime_semantics_tests.rs
)

extension_middleware_semantic_hardening_suites=(
  rust/runtime/tests/extension_integration.rs
  rust/runtime/tests/middleware_semantic_hardening.rs
)

generated_topology_transport_public_path_suites=(
  rust/runtime/tests/generated_topology_public_path.rs
)

runtime_substrate_boundary_suites=(
  rust/runtime/tests/runtime_substrate_contracts.rs
  rust/runtime/tests/wasm_compat.rs
)

handler_contract_boundary_suites=(
  rust/runtime/tests/handler_contracts.rs
  rust/runtime/tests/transport_contracts.rs
)

long_horizon_recovery_harness_suites=(
  rust/bridge/tests/reconfiguration_recovery_harness.rs
)

artifact_release_assurance_suites=(
  scripts/check/package-artifacts.sh
  scripts/check/package-provenance.sh
  scripts/check/package-resource-audit.sh
  scripts/check/release-recovery.sh
)

mutation_fail_closed_assurance_suites=(
  rust/machine/src/runtime_contracts.rs
  scripts/check/fail-closed-mutations.sh
)

concrete_protocol_machine_refinement_suites=(
  rust/bridge/tests/protocol_machine_differential_steps.rs
  rust/machine/tests/lean_protocol_machine_equivalence.rs
  rust/machine/tests/threaded_equivalence.rs
)

compiler_serialization_pipeline_suites=(
  rust/bridge/tests/compiler_pipeline_conformance.rs
  rust/bridge/tests/projection_equivalence.rs
  rust/bridge/tests/proptest_json_roundtrip.rs
  rust/bridge/tests/lean_integration_tests.rs
  rust/bridge/tests/merge_semantics_tests.rs
)

deadlock_automation_fragment_suites=(
  rust/types/src/local.rs
  rust/bridge/tests/regular_practical_fragment_checks.rs
  rust/tests/dsl_runtime_semantics_tests.rs
)

docs_as_contract_assurance_suites=(
  rust/bridge/tests/docs_contract_tests.rs
  scripts/check/verification-inventory.sh
  scripts/check/bridge-normalization-ledger.sh
)

deterministic_scale_budget_assurance_suites=(
  rust/bridge/tests/scale_budget_contracts.rs
)

explicit_unsupported_fail_closed_notes=()

forbidden_inventory_gap_phrases=(
  "not yet as a full semantic lifecycle harness"
  "still incomplete"
  "load-only Lean output"
  "fail-closed placeholder"
)

gate_ownership_recipes=(
  check-fast-structure
  check-focused-assurance
  check-package-artifacts
  check-pr-critical
  check-deep-assurance
)

# ── Helpers ───────────────────────────────────────────────────────────

# Extract the documented value for a named metric from the inventory doc.
# Usage: metric_value "Metric name"
metric_value() {
  local name="$1"
  local row
  row=$(grep -E "^\|[[:space:]]*${name}[[:space:]]*\|" docs/902_verification_inventory.md) || true
  if [[ -z "$row" ]]; then
    echo "missing metric row in docs/902_verification_inventory.md: ${name}" >&2
    exit 1
  fi
  # Extract the numeric value column (second pipe-delimited field), strip commas
  echo "$row" | sed 's/|/|/g' | awk -F'|' '{gsub(/[^0-9]/, "", $3); print $3}'
}

# Count non-comment, non-blank indented lines in a justfile recipe body.
# Usage: recipe_command_count "recipe-name"
recipe_command_count() {
  local recipe="$1"
  local in_recipe=0
  local count=0
  while IFS= read -r line; do
    if [[ "$in_recipe" -eq 1 ]]; then
      # Recipe body lines start with space or tab
      if [[ "$line" =~ ^[[:space:]] ]]; then
        local stripped
        stripped="${line#"${line%%[![:space:]]*}"}"
        # Skip blank and comment lines
        if [[ -n "$stripped" && ! "$stripped" =~ ^# ]]; then
          count=$((count + 1))
        fi
        continue
      else
        break
      fi
    fi
    # Match recipe header: name followed by colon or whitespace
    if [[ "$line" =~ ^${recipe}(:|[[:space:]]) ]]; then
      in_recipe=1
    fi
  done < justfile
  if [[ "$in_recipe" -eq 0 ]]; then
    echo "missing just recipe: ${recipe}" >&2
    exit 1
  fi
  echo "$count"
}

# Compare a documented value against an actual value.
# Usage: check_metric "Metric name" actual_value
check_metric() {
  local name="$1"
  local actual="$2"
  local documented
  documented=$(metric_value "$name")
  if [[ "$documented" -ne "$actual" ]]; then
    errors+=("docs/902_verification_inventory.md: metric \`${name}\` documents ${documented} but actual is ${actual}")
  fi
}

count_list() {
  echo "$#"
}

bucket_has_coverage() {
  local count="$1"
  if [[ "$count" -gt 0 ]]; then
    echo 1
  else
    echo 0
  fi
}

# ── Lean CODE_MAP.md Total Metrics ────────────────────────────────────

total_row=$(grep -E '^\|[[:space:]]+\*\*Total\*\*[[:space:]]+\|[[:space:]]+\*\*[0-9,]+\*\*[[:space:]]+\|[[:space:]]+\*\*[0-9,]+\*\*' lean/CODE_MAP.md | head -1) || true
if [[ -z "$total_row" ]]; then
  echo "failed to parse lean/CODE_MAP.md total metrics" >&2
  exit 1
fi

# Extract files count (second bold value) and lines count (third bold value)
actual_files=$(echo "$total_row" | sed 's/[*,]//g' | awk -F'|' '{gsub(/[^0-9]/, "", $3); print $3}')
actual_lines=$(echo "$total_row" | sed 's/[*,]//g' | awk -F'|' '{gsub(/[^0-9]/, "", $4); print $4}')
actual_search_fairness_inventory=$(grep -c '("search_' lean/Runtime/Proofs/Search/Inventory.lean || echo 0)

check_metric "Lean core-library files" "$actual_files"
check_metric "Lean core-library lines" "$actual_lines"
check_metric "Lean-backed search fairness inventory entries" "$actual_search_fairness_inventory"

# ── Justfile Recipe Command Counts ────────────────────────────────────

actual_ownership=$(recipe_command_count "check-ownership-contracts")
actual_aura=$(recipe_command_count "check-aura-borrowed-lints")

check_metric "Ownership contract gate commands" "$actual_ownership"
check_metric "Aura-derived boundary checks" "$actual_aura"

# ── Explicit Failure/Timeout Event Inventory ─────────────────────────

actual_explicit_failure_timeout_events=$(count_list "${explicit_failure_timeout_events[@]}")
check_metric "Explicit failure/timeout observable event kinds" "$actual_explicit_failure_timeout_events"

# ── Macro UI Fixture Counts ───────────────────────────────────────────

macro_ui_file="rust/macros/tests/macro_ui.rs"

actual_pass=$(grep -c '\bt\.pass(' "$macro_ui_file" || echo 0)
actual_fail=$(grep -c '\bt\.compile_fail(' "$macro_ui_file" || echo 0)

check_metric "Macro UI pass fixtures" "$actual_pass"
check_metric "Macro UI compile-fail fixtures" "$actual_fail"

# ── Property Coverage Baseline ───────────────────────────────────────

actual_lean_correspondence_strict=$(count_list "${lean_correspondence_strict_suites[@]}")
actual_authority_ownership=$(count_list "${authority_ownership_suites[@]}")
actual_identity_replay=$(count_list "${identity_replay_suites[@]}")
actual_commitment_progress=$(count_list "${commitment_progress_suites[@]}")
actual_cross_mode_semantic_parity=$(count_list "${cross_mode_semantic_parity_suites[@]}")
actual_fail_closed_lowering_admission=$(count_list "${fail_closed_lowering_admission_suites[@]}")
actual_structure_reconfiguration=$(count_list "${structure_reconfiguration_suites[@]}")
actual_semantic_lifecycle_invariant_suites=$(count_list "${semantic_lifecycle_invariant_suites[@]}")
actual_adversarial_lifecycle_scenarios=$(count_list "${adversarial_lifecycle_cases[@]}")
actual_dsl_runtime_semantics_suites=$(count_list "${dsl_runtime_semantics_suites[@]}")
actual_simulator_semantic_contract_categories=$(count_list "${simulator_semantic_contract_categories[@]}")
actual_theorem_pack_admission_suites=$(count_list "${theorem_pack_admission_suites[@]}")
actual_distributed_topology_semantic_harness_suites=$(count_list "${distributed_topology_semantic_harness_suites[@]}")
actual_agreement_composition_runtime_semantic_suites=$(count_list "${agreement_composition_runtime_semantic_suites[@]}")
actual_extension_middleware_semantic_hardening_suites=$(count_list "${extension_middleware_semantic_hardening_suites[@]}")
actual_generated_topology_transport_public_path_suites=$(count_list "${generated_topology_transport_public_path_suites[@]}")
actual_runtime_substrate_boundary_suites=$(count_list "${runtime_substrate_boundary_suites[@]}")
actual_handler_contract_boundary_suites=$(count_list "${handler_contract_boundary_suites[@]}")
actual_long_horizon_recovery_harness_suites=$(count_list "${long_horizon_recovery_harness_suites[@]}")
actual_artifact_release_assurance_suites=$(count_list "${artifact_release_assurance_suites[@]}")
actual_mutation_fail_closed_assurance_suites=$(count_list "${mutation_fail_closed_assurance_suites[@]}")
actual_concrete_protocol_machine_refinement_suites=$(count_list "${concrete_protocol_machine_refinement_suites[@]}")
actual_compiler_serialization_pipeline_suites=$(count_list "${compiler_serialization_pipeline_suites[@]}")
actual_deadlock_automation_fragment_suites=$(count_list "${deadlock_automation_fragment_suites[@]}")
actual_docs_as_contract_assurance_suites=$(count_list "${docs_as_contract_assurance_suites[@]}")
actual_deterministic_scale_budget_assurance_suites=$(count_list "${deterministic_scale_budget_assurance_suites[@]}")
actual_explicit_unsupported_fail_closed_notes=$(count_list "${explicit_unsupported_fail_closed_notes[@]}")

actual_executable_property_buckets=$(
  (
    bucket_has_coverage "$actual_authority_ownership"
    bucket_has_coverage "$actual_lean_correspondence_strict"
    bucket_has_coverage "$actual_identity_replay"
    bucket_has_coverage "$actual_commitment_progress"
    bucket_has_coverage "$actual_cross_mode_semantic_parity"
    bucket_has_coverage "$actual_fail_closed_lowering_admission"
    bucket_has_coverage "$actual_structure_reconfiguration"
    bucket_has_coverage "$actual_theorem_pack_admission_suites"
    bucket_has_coverage "$actual_distributed_topology_semantic_harness_suites"
    bucket_has_coverage "$actual_agreement_composition_runtime_semantic_suites"
    bucket_has_coverage "$actual_extension_middleware_semantic_hardening_suites"
    bucket_has_coverage "$actual_generated_topology_transport_public_path_suites"
    bucket_has_coverage "$actual_runtime_substrate_boundary_suites"
    bucket_has_coverage "$actual_handler_contract_boundary_suites"
    bucket_has_coverage "$actual_long_horizon_recovery_harness_suites"
    bucket_has_coverage "$actual_artifact_release_assurance_suites"
    bucket_has_coverage "$actual_mutation_fail_closed_assurance_suites"
    bucket_has_coverage "$actual_concrete_protocol_machine_refinement_suites"
    bucket_has_coverage "$actual_compiler_serialization_pipeline_suites"
    bucket_has_coverage "$actual_deadlock_automation_fragment_suites"
    bucket_has_coverage "$actual_docs_as_contract_assurance_suites"
    bucket_has_coverage "$actual_deterministic_scale_budget_assurance_suites"
  ) | awk '{sum += $1} END {print sum + 0}'
)
actual_lacking_property_buckets=$((22 - actual_executable_property_buckets))

check_metric "Property buckets with executable assurance suites" "$actual_executable_property_buckets"
check_metric "Property buckets currently lacking executable assurance suites" "$actual_lacking_property_buckets"
check_metric "Authority and ownership semantic assurance suites" "$actual_authority_ownership"
check_metric "Lean-backed correspondence strict suites" "$actual_lean_correspondence_strict"
check_metric "Identity and replay semantic assurance suites" "$actual_identity_replay"
check_metric "Commitment and progress semantic assurance suites" "$actual_commitment_progress"
check_metric "Cross-mode semantic parity suites" "$actual_cross_mode_semantic_parity"
check_metric "Fail-closed lowering and admission gate suites" "$actual_fail_closed_lowering_admission"
check_metric "Structural locality and reconfiguration executable assurance suites" "$actual_structure_reconfiguration"
check_metric "Semantic lifecycle invariant suites" "$actual_semantic_lifecycle_invariant_suites"
check_metric "Deterministic adversarial lifecycle scenarios" "$actual_adversarial_lifecycle_scenarios"
check_metric "End-to-end DSL runtime semantic conformance suites" "$actual_dsl_runtime_semantics_suites"
check_metric "Simulator semantic contract categories enforced automatically" "$actual_simulator_semantic_contract_categories"
check_metric "Theorem-pack and admission executable assurance suites" "$actual_theorem_pack_admission_suites"
check_metric "Distributed and topology semantic harness suites" "$actual_distributed_topology_semantic_harness_suites"
check_metric "Agreement and composition runtime semantic suites" "$actual_agreement_composition_runtime_semantic_suites"
check_metric "Extension and middleware semantic hardening suites" "$actual_extension_middleware_semantic_hardening_suites"
check_metric "Generated topology and transport public-path suites" "$actual_generated_topology_transport_public_path_suites"
check_metric "Runtime substrate boundary assurance suites" "$actual_runtime_substrate_boundary_suites"
check_metric "Handler contract boundary assurance suites" "$actual_handler_contract_boundary_suites"
check_metric "Long-horizon recovery differential harness suites" "$actual_long_horizon_recovery_harness_suites"
check_metric "Artifact and release assurance suites" "$actual_artifact_release_assurance_suites"
check_metric "Mutation fail-closed assurance suites" "$actual_mutation_fail_closed_assurance_suites"
check_metric "Concrete protocol-machine refinement suites" "$actual_concrete_protocol_machine_refinement_suites"
check_metric "Compiler and serialization pipeline suites" "$actual_compiler_serialization_pipeline_suites"
check_metric "Deadlock automation fragment assurance suites" "$actual_deadlock_automation_fragment_suites"
check_metric "Docs-as-contract assurance suites" "$actual_docs_as_contract_assurance_suites"
check_metric "Deterministic scale and budget assurance suites" "$actual_deterministic_scale_budget_assurance_suites"
check_metric "Explicit unsupported or fail-closed property notes" "$actual_explicit_unsupported_fail_closed_notes"

for phrase in "${forbidden_inventory_gap_phrases[@]}"; do
  if rg -Fq "$phrase" docs/902_verification_inventory.md; then
    errors+=("docs/902_verification_inventory.md: stale gap phrase remains in inventory: ${phrase}")
  fi
done

if ! rg -q "^## Gate Ownership" docs/902_verification_inventory.md; then
  errors+=("docs/902_verification_inventory.md: missing 'Gate Ownership' section")
fi

for recipe in "${gate_ownership_recipes[@]}"; do
  recipe_code_span="$(printf '`just %s`' "${recipe}")"
  recipe_command_count "${recipe}" >/dev/null
  if ! rg -Fq "${recipe_code_span}" docs/902_verification_inventory.md; then
    errors+=("docs/902_verification_inventory.md: missing gate ownership entry for ${recipe}")
  fi
done

# ── Report ────────────────────────────────────────────────────────────

if [[ ${#errors[@]} -gt 0 ]]; then
  for err in "${errors[@]}"; do
    echo "$err" >&2
  done
  exit 1
fi

echo "verification inventory check passed"
