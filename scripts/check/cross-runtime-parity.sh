#!/usr/bin/env bash
# Consolidated Lean/Rust cross-runtime parity checks.
# Compares type shapes (enum variants, struct fields) between Lean and Rust,
# runs the protocol machine differential parity test suite, and validates CI gate markers.
set -euo pipefail

# Usage:
#   ./scripts/check/cross-runtime-parity.sh [--all|--types|--suite|--conformance]
#
# Modes:
#   --all         Run all parity checks (default)
#   --types       Type shape parity (enum variants, struct fields)
#   --suite       protocol machine differential parity test suite
#   --conformance Strict Lean-core protocol machine conformance (cooperative + threaded)

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"
mkdir -p "${ROOT_DIR}/.tmp"
if [[ -z "${TMPDIR:-}" || ! -d "${TMPDIR}" ]]; then
  export TMPDIR="${ROOT_DIR}/.tmp"
fi

MODE="${1:---all}"

ensure_lean_prebuilt() {
  "${ROOT_DIR}/scripts/bootstrap/ensure-lean-prebuilt.sh"
}

# ── Counters and Helpers ──────────────────────────────────────

checks=0
failures=0

run_check() {
  local name="$1"
  local cmd="$2"
  checks=$((checks + 1))
  echo "[parity] ${name}"
  if eval "${cmd}"; then
    echo "[parity] OK: ${name}"
  else
    failures=$((failures + 1))
    echo "[parity] FAIL: ${name}" >&2
  fi
  echo
}

# ── Type Shape Parity ─────────────────────────────────────────
check_types() {
  local mismatches=()

  # ── Parser helpers ─────────────────────────────────────────

  # parse_lean_inductive_variants FILE TYPE_NAME
  # Prints one variant name per line.
  parse_lean_inductive_variants() {
    local file="$1" type_name="$2"
    awk -v tname="$type_name" '
      BEGIN { in_block = 0; found = 0 }
      !in_block {
        if ($0 ~ "^[[:space:]]*inductive[[:space:]]+" tname "[[:space:]]+where") {
          in_block = 1
        }
        next
      }
      /^[[:space:]]*\|[[:space:]]*[A-Za-z_][A-Za-z0-9_]*/ {
        line = $0
        sub(/^[[:space:]]*\|[[:space:]]*/, "", line)
        sub(/[[:space:]].*/, "", line)
        print line
        found = 1
        next
      }
      found && /^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?(def|theorem|lemma|structure|class|instance|abbrev|inductive|namespace|open|set_option|universe)/ {
        exit
      }
    ' "$file"
  }

  # parse_rust_enum_variants FILE ENUM_NAME
  # Prints one variant name per line.
  parse_rust_enum_variants() {
    local file="$1" enum_name="$2"
    awk -v ename="$enum_name" '
      BEGIN { in_block = 0; depth = 0 }
      !in_block {
        if ($0 ~ "^[[:space:]]*pub[[:space:]]+enum[[:space:]]+" ename "[[:space:]]*\\{") {
          in_block = 1
          depth = gsub(/\{/, "{") - gsub(/\}/, "}")
        }
        next
      }
      {
        depth += gsub(/\{/, "{") - gsub(/\}/, "}")
        code = $0
        sub(/\/\/.*/, "", code)        # strip line comments
        gsub(/^[[:space:]]+/, "", code) # strip leading whitespace
        gsub(/[[:space:]]+$/, "", code) # strip trailing whitespace
        if (code != "" && code !~ /^#/ && code !~ /^\/\/\//) {
          if (match(code, /^([A-Za-z_][A-Za-z0-9_]*)[[:space:]]*[({,]/, arr)) {
            print arr[1]
          }
        }
        if (depth <= 0) exit
      }
    ' "$file"
  }

  # parse_lean_structure_fields FILE STRUCT_NAME
  # Prints one field name per line.
  parse_lean_structure_fields() {
    local file="$1" struct_name="$2"
    awk -v sname="$struct_name" '
      BEGIN { in_block = 0; found = 0 }
      !in_block {
        if ($0 ~ "^[[:space:]]*structure[[:space:]]+" sname "([[:space:]]|$)" && $0 ~ "(^|[[:space:]])where([[:space:]]|$)") {
          in_block = 1
        }
        next
      }
      {
        code = $0
        sub(/--.*/, "", code)           # strip Lean comments
        gsub(/^[[:space:]]+/, "", code)
        gsub(/[[:space:]]+$/, "", code)
        if (code == "") next
        if (match(code, /^([A-Za-z_][A-Za-z0-9_'"'"']*)[[:space:]]*:[[:space:]]*/)) {
          field = code
          sub(/[[:space:]]*:.*/, "", field)
          print field
          found = 1
          next
        }
        if (found && code ~ /^(private[[:space:]]+|protected[[:space:]]+)?(def|theorem|lemma|structure|class|instance|abbrev|inductive|namespace|open|set_option|universe)/) {
          exit
        }
      }
    ' "$file"
  }

  # parse_rust_struct_fields FILE STRUCT_NAME
  # Prints one field name per line.
  parse_rust_struct_fields() {
    local file="$1" struct_name="$2"
    awk -v sname="$struct_name" '
      BEGIN { in_block = 0; depth = 0 }
      !in_block {
        if ($0 ~ "^[[:space:]]*pub[[:space:]]+struct[[:space:]]+" sname "(<[^>]+>)?[[:space:]]*\\{") {
          in_block = 1
          depth = gsub(/\{/, "{") - gsub(/\}/, "}")
        }
        next
      }
      {
        depth += gsub(/\{/, "{") - gsub(/\}/, "}")
        code = $0
        sub(/\/\/.*/, "", code)
        gsub(/^[[:space:]]+/, "", code)
        gsub(/[[:space:]]+$/, "", code)
        if (match(code, /^pub[[:space:]]+([A-Za-z_][A-Za-z0-9_]*)[[:space:]]*:/, arr)) {
          print arr[1]
        }
        if (depth <= 0) exit
      }
    ' "$file"
  }

  # ucfirst STRING — capitalize first letter
  ucfirst() {
    local s="$1"
    if [[ -z "$s" ]]; then
      echo ""
    else
      echo "$(echo "${s:0:1}" | tr '[:lower:]' '[:upper:]')${s:1}"
    fi
  }

  # normalize_lean_variant NAME MAP_KEYS MAP_VALUES
  # MAP_KEYS and MAP_VALUES are parallel |-delimited lists.
  normalize_lean_variant() {
    local name="$1" map_keys="$2" map_vals="$3"
    if [[ -n "$map_keys" ]]; then
      IFS='|' read -ra keys <<< "$map_keys"
      IFS='|' read -ra vals <<< "$map_vals"
      for i in "${!keys[@]}"; do
        if [[ "$name" == "${keys[$i]}" ]]; then
          echo "${vals[$i]}"
          return
        fi
      done
    fi
    ucfirst "$name"
  }

  # sorted_unique — sort lines and deduplicate
  sorted_unique() {
    sort -u
  }

  # set_diff A B — lines in A not in B (inputs must be sorted)
  set_diff() {
    comm -23 <(echo "$1") <(echo "$2")
  }

  # compare_enum LABEL LEAN_FILE LEAN_TYPE RUST_FILE RUST_TYPE MAP_KEYS MAP_VALS
  compare_enum() {
    local label="$1" lean_file="$2" lean_type="$3" rust_file="$4" rust_type="$5"
    local map_keys="$6" map_vals="$7"

    local lean_raw rust_raw
    lean_raw="$(parse_lean_inductive_variants "$lean_file" "$lean_type")"
    if [[ -z "$lean_raw" ]]; then
      echo "ERROR: could not parse Lean variants for ${lean_type} in ${lean_file}"
      exit 1
    fi
    rust_raw="$(parse_rust_enum_variants "$rust_file" "$rust_type")"
    if [[ -z "$rust_raw" ]]; then
      echo "ERROR: could not parse Rust variants for ${rust_type} in ${rust_file}"
      exit 1
    fi

    # Normalize Lean variants through mapping
    local lean_norm=""
    while IFS= read -r v; do
      local nv
      nv="$(normalize_lean_variant "$v" "$map_keys" "$map_vals")"
      if [[ -n "$lean_norm" ]]; then
        lean_norm="${lean_norm}"$'\n'"${nv}"
      else
        lean_norm="${nv}"
      fi
    done <<< "$lean_raw"

    local lean_sorted rust_sorted
    lean_sorted="$(echo "$lean_norm" | sorted_unique)"
    rust_sorted="$(echo "$rust_raw" | sorted_unique)"

    echo "[parity] ${label}: Lean=[${lean_sorted//$'\n'/, }] Rust=[${rust_sorted//$'\n'/, }]"

    local missing_in_lean missing_in_rust
    missing_in_lean="$(set_diff "$rust_sorted" "$lean_sorted")"
    missing_in_rust="$(set_diff "$lean_sorted" "$rust_sorted")"

    while IFS= read -r v; do
      if [[ -n "$v" ]]; then mismatches+=("${label}:missing_in_lean:${v}"); fi
    done <<< "$missing_in_lean"
    while IFS= read -r v; do
      if [[ -n "$v" ]]; then mismatches+=("${label}:missing_in_rust:${v}"); fi
    done <<< "$missing_in_rust"
  }

  # compare_struct LABEL LEAN_FILE LEAN_TYPE RUST_FILE RUST_TYPE MAP_KEYS MAP_VALS
  compare_struct() {
    local label="$1" lean_file="$2" lean_type="$3" rust_file="$4" rust_type="$5"
    local map_keys="$6" map_vals="$7"

    local lean_raw rust_raw
    lean_raw="$(parse_lean_structure_fields "$lean_file" "$lean_type")"
    if [[ -z "$lean_raw" ]]; then
      echo "ERROR: could not parse Lean fields for ${lean_type} in ${lean_file}"
      exit 1
    fi
    rust_raw="$(parse_rust_struct_fields "$rust_file" "$rust_type")"
    if [[ -z "$rust_raw" ]]; then
      echo "ERROR: could not parse Rust fields for ${rust_type} in ${rust_file}"
      exit 1
    fi

    # Normalize Lean field names through mapping (identity if no mapping)
    local lean_norm=""
    while IFS= read -r f; do
      local nf="$f"
      if [[ -n "$map_keys" ]]; then
        IFS='|' read -ra keys <<< "$map_keys"
        IFS='|' read -ra vals <<< "$map_vals"
        for i in "${!keys[@]}"; do
          if [[ "$f" == "${keys[$i]}" ]]; then
            nf="${vals[$i]}"
            break
          fi
        done
      fi
      if [[ -n "$lean_norm" ]]; then
        lean_norm="${lean_norm}"$'\n'"${nf}"
      else
        lean_norm="${nf}"
      fi
    done <<< "$lean_raw"

    local lean_sorted rust_sorted
    lean_sorted="$(echo "$lean_norm" | sorted_unique)"
    rust_sorted="$(echo "$rust_raw" | sorted_unique)"

    echo "[parity] ${label}: LeanFields=[${lean_sorted//$'\n'/, }] RustFields=[${rust_sorted//$'\n'/, }]"

    local missing_in_lean missing_in_rust
    missing_in_lean="$(set_diff "$rust_sorted" "$lean_sorted")"
    missing_in_rust="$(set_diff "$lean_sorted" "$rust_sorted")"

    while IFS= read -r f; do
      if [[ -n "$f" ]]; then mismatches+=("${label}:missing_field_in_lean:${f}"); fi
    done <<< "$missing_in_lean"
    while IFS= read -r f; do
      if [[ -n "$f" ]]; then mismatches+=("${label}:missing_field_in_rust:${f}"); fi
    done <<< "$missing_in_rust"
  }

  # ── Enum checks ───────────────────────────────────────────

  compare_enum "FlowPolicy" \
    "${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/Knowledge.lean" "FlowPolicy" \
    "${ROOT_DIR}/rust/machine/src/engine/runtime_state/policy.rs" "FlowPolicy" \
    "allowAll|denyAll|allowRoles|denyRoles|predicate|predicateExpr" \
    "AllowAll|DenyAll|AllowRoles|DenyRoles|Predicate|PredicateExpr"

  compare_enum "FlowPredicate" \
    "${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/Knowledge.lean" "FlowPredicate" \
    "${ROOT_DIR}/rust/machine/src/engine/runtime_state/policy.rs" "FlowPredicate" \
    "targetRolePrefix|factContains|endpointRoleMatchesTarget|all|any" \
    "TargetRolePrefix|FactContains|EndpointRoleMatchesTarget|All|Any"

  compare_enum "OutputConditionPolicy" \
    "${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/OutputCondition.lean" "OutputConditionPolicy" \
    "${ROOT_DIR}/rust/machine/src/output_condition.rs" "OutputConditionPolicy" \
    "disabled|allowAll|denyAll|predicateAllowList" \
    "Disabled|AllowAll|DenyAll|PredicateAllowList"

  compare_enum "Value" \
    "${ROOT_DIR}/lean/Protocol/Values.lean" "Value" \
    "${ROOT_DIR}/rust/machine/src/coroutine.rs" "Value" \
    "string|chan" \
    "Str|Endpoint"

  compare_enum "CommunicationReplayMode" \
    "${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/Config.lean" "CommunicationReplayMode" \
    "${ROOT_DIR}/rust/machine/src/communication_replay/identity.rs" "CommunicationReplayMode" \
    "off|sequence|nullifier" \
    "Off|Sequence|Nullifier"

  # ── Struct checks ─────────────────────────────────────────

  compare_struct "ProgressToken" \
    "${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/State.lean" "ProgressToken" \
    "${ROOT_DIR}/rust/machine/src/coroutine.rs" "ProgressToken" \
    "" ""

  compare_struct "SignedValue" \
    "${ROOT_DIR}/lean/Runtime/ProtocolMachine/Model/TypeClasses.lean" "SignedValue" \
    "${ROOT_DIR}/rust/machine/src/buffer.rs" "SignedValue" \
    "seqNo" \
    "sequence_no"

  # ── Report mismatches ─────────────────────────────────────

  if (( ${#mismatches[@]} > 0 )); then
    echo "[parity] uncovered mismatches:"
    for m in "${mismatches[@]}"; do
      echo "  - ${m}"
    done
    echo "ERROR: found Lean/Rust parity mismatches - add deviation entry to docs/802_rust_lean_parity.md Deviation Registry"
    exit 1
  fi

  echo "[parity] policy/data shape parity check passed with no mismatches"

  # ── CI marker checks ─────────────────────────────────────

  local verify_workflow="${ROOT_DIR}/.github/workflows/verify.yml"
  local check_workflow="${ROOT_DIR}/.github/workflows/check.yml"
  local justfile="${ROOT_DIR}/justfile"

  if ! grep -qF "just check-parity" "$verify_workflow"; then
    echo "ERROR: missing verify workflow parity gate: expected marker \`just check-parity\`"
    exit 1
  fi
  if ! grep -qF "./scripts/check/cross-runtime-parity.sh" "$check_workflow"; then
    echo "ERROR: missing check workflow parity gate: expected marker \`./scripts/check/cross-runtime-parity.sh\`"
    exit 1
  fi
  if ! grep -qF "just check-parity" "$justfile"; then
    echo "ERROR: missing ci-dry-run parity gate: expected marker \`just check-parity\`"
    exit 1
  fi

  echo "[parity] CI parity-regression gates are present in workflows and ci-dry-run"
}

# ── Suite: Protocol Machine Differential Parity Suite ───────────────────────
check_suite() {
  echo "== Protocol Machine Parity Suite =="
  ensure_lean_prebuilt
  run_check "lean conformance corpus" \
    "cargo test -p telltale-machine --test conformance_lean"
  run_check "lean equivalence corpus" \
    "cargo test -p telltale-machine --test equivalence_lean"
  run_check "differential step corpus" \
    "cargo test -p telltale-machine --test differential_step_corpus"
  run_check "bridge protocol machine correspondence" \
    "cargo test -p telltale-bridge --test protocol_machine_correspondence_tests"
  run_check "bridge protocol machine differential-step correspondence" \
    "cargo test -p telltale-bridge --test protocol_machine_differential_steps"
  run_check "simulator lean-reference parity suite" \
    "cargo test -p telltale-simulator --test lean_reference_parity"
  run_check "simulator material parity fixtures (Rust handlers)" \
    "cargo test -p telltale-simulator --test field_handler_parity"
  run_check "simulator material parity fixtures (Lean mirror)" \
    "lake --dir lean build simulator_parity_tests && ./lean/.lake/build/bin/simulator_parity_tests"
  run_check "heap parity fixtures (Lean mirror)" \
    "lake --dir lean build heap_parity_runner && cargo test -p telltale-bridge --test heap_lean_parity"
  run_check "threaded parity equivalence" \
    "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-machine --features multi-thread --test threaded_equivalence"
  run_check "planner trace worker-count conformance" \
    "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-machine --features multi-thread --test threaded_lane_runtime planner_trace_is_worker_count_invariant_for_fixed_ready_set"
  run_check "v2 parity fixtures (speculation/scheduler/failure-envelope)" \
    "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-machine --features multi-thread --test parity_fixtures_v2"
}

# ── Conformance: Strict Protocol Machine Conformance ────────────────────────
check_conformance() {
  echo "== Strict Protocol Machine Conformance =="

  # Cooperative backend
  cargo test -p telltale-machine --test conformance_lean
  cargo test -p telltale-machine --test equivalence_lean
  cargo test -p telltale-machine --test lean_vm_equivalence
  cargo test -p telltale-machine --test trace_corpus
  cargo test -p telltale-machine --test strict_tick_equality

  cargo test -p telltale-machine --test differential_step_corpus
  cargo test -p telltale-machine --test strict_value_rejection
  cargo test -p telltale-machine --test instr_fault_snapshots
  cargo test -p telltale-machine --test schedule_robustness
  cargo test -p telltale-machine --test serialization_lean
  cargo test -p telltale-machine --test bytecode_conformance

  # Threaded backend
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-machine --features multi-thread --test threaded_contract
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-machine --features multi-thread --test threaded_equivalence
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-machine --features multi-thread --test threaded_lane_runtime
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-machine --features multi-thread --test differential_step_corpus
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-machine --features multi-thread --test schedule_robustness

  echo "OK   strict protocol machine conformance passed"
}

# ── Main ──────────────────────────────────────────────────────
case "${MODE}" in
  --all)
    check_types
    echo ""
    check_suite
    ;;
  --types)
    check_types
    ;;
  --suite)
    check_suite
    ;;
  --conformance)
    check_conformance
    ;;
  *)
    echo "error: unknown mode ${MODE}" >&2
    echo "Usage: $0 [--all|--types|--suite|--conformance]" >&2
    exit 2
    ;;
esac

if [[ "${MODE}" == "--suite" ]] || [[ "${MODE}" == "--all" ]]; then
  echo ""
  echo "[parity] Summary: ${checks} checks, ${failures} failures."
  if (( failures > 0 )); then
    exit 1
  fi
fi
