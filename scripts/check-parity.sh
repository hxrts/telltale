#!/usr/bin/env bash
set -euo pipefail

# Consolidated Lean/Rust parity checks.
# Usage:
#   ./scripts/check-parity.sh [--all|--types|--suite|--conformance]
#
# Modes:
#   --all         Run all parity checks (default)
#   --types       Type shape parity (enum variants, struct fields)
#   --suite       VM differential parity test suite
#   --conformance Strict Lean-core VM conformance (cooperative + threaded)

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

MODE="${1:---all}"

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

# --- Type Shape Parity (from check-parity-ledger.sh) ---
check_types() {
  python3 - "${ROOT_DIR}" <<'PY'
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])


def fail(msg: str) -> None:
    print(f"ERROR: {msg}")
    sys.exit(1)


def parse_lean_inductive_variants(path: Path, inductive_name: str) -> list[str]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    start_re = re.compile(rf"^\s*inductive\s+{re.escape(inductive_name)}\s+where\b")
    variant_re = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_]*)")
    stop_re = re.compile(
        r"^\s*(?:(?:private|protected)\s+)?"
        r"(def|theorem|lemma|structure|class|instance|abbrev|inductive|namespace|open|set_option|universe)\b"
    )

    in_block = False
    variants: list[str] = []
    for line in lines:
        if not in_block:
            if start_re.match(line):
                in_block = True
            continue

        match = variant_re.match(line)
        if match:
            variants.append(match.group(1))
            continue

        if variants and stop_re.match(line):
            break

    if not variants:
        fail(f"could not parse Lean variants for {inductive_name} in {path}")
    return variants


def parse_rust_enum_variants(path: Path, enum_name: str) -> list[str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    start_re = re.compile(rf"^\s*pub\s+enum\s+{re.escape(enum_name)}\s*\{{")
    variant_re = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(|\{|,)")

    in_block = False
    brace_depth = 0
    variants: list[str] = []

    for line in lines:
        if not in_block:
            if start_re.match(line):
                in_block = True
                brace_depth = line.count("{") - line.count("}")
            continue

        brace_depth += line.count("{") - line.count("}")
        code = line.split("//", 1)[0].strip()

        if code and not code.startswith("#") and not code.startswith("///"):
            match = variant_re.match(code)
            if match:
                variants.append(match.group(1))

        if brace_depth == 0:
            break

    if not variants:
        fail(f"could not parse Rust variants for {enum_name} in {path}")
    return variants


def parse_lean_structure_fields(path: Path, structure_name: str) -> list[str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    start_re = re.compile(rf"^\s*structure\s+{re.escape(structure_name)}\s+where\b")
    field_re = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*")
    stop_re = re.compile(
        r"^\s*(?:(?:private|protected)\s+)?"
        r"(def|theorem|lemma|structure|class|instance|abbrev|inductive|namespace|open|set_option|universe)\b"
    )

    in_block = False
    fields: list[str] = []
    for line in lines:
        if not in_block:
            if start_re.match(line):
                in_block = True
            continue

        code = line.split("--", 1)[0].strip()
        if not code:
            continue
        match = field_re.match(code)
        if match:
            fields.append(match.group(1))
            continue

        if fields and stop_re.match(code):
            break

    if not fields:
        fail(f"could not parse Lean fields for {structure_name} in {path}")
    return fields


def parse_rust_struct_fields(path: Path, struct_name: str) -> list[str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    start_re = re.compile(rf"^\s*pub\s+struct\s+{re.escape(struct_name)}(?:<[^>]+>)?\s*\{{")
    field_re = re.compile(r"^\s*pub\s+([A-Za-z_][A-Za-z0-9_]*)\s*:")

    in_block = False
    brace_depth = 0
    fields: list[str] = []
    for line in lines:
        if not in_block:
            if start_re.match(line):
                in_block = True
                brace_depth = line.count("{") - line.count("}")
            continue

        brace_depth += line.count("{") - line.count("}")
        code = line.split("//", 1)[0].strip()
        match = field_re.match(code)
        if match:
            fields.append(match.group(1))

        if brace_depth == 0:
            break

    if not fields:
        fail(f"could not parse Rust fields for {struct_name} in {path}")
    return fields


def normalize_lean_variant(name: str, mapping: dict[str, str]) -> str:
    if name in mapping:
        return mapping[name]
    if not name:
        return name
    return name[0].upper() + name[1:]


enum_checks = [
    {
        "label": "FlowPolicy",
        "lean_file": root / "lean/Runtime/VM/Model/Knowledge.lean",
        "lean_type": "FlowPolicy",
        "rust_file": root / "rust/vm/src/vm.rs",
        "rust_type": "FlowPolicy",
        "map": {
            "allowAll": "AllowAll",
            "denyAll": "DenyAll",
            "allowRoles": "AllowRoles",
            "denyRoles": "DenyRoles",
            "predicate": "Predicate",
            "predicateExpr": "PredicateExpr",
        },
    },
    {
        "label": "FlowPredicate",
        "lean_file": root / "lean/Runtime/VM/Model/Knowledge.lean",
        "lean_type": "FlowPredicate",
        "rust_file": root / "rust/vm/src/vm.rs",
        "rust_type": "FlowPredicate",
        "map": {
            "targetRolePrefix": "TargetRolePrefix",
            "factContains": "FactContains",
            "endpointRoleMatchesTarget": "EndpointRoleMatchesTarget",
            "all": "All",
            "any": "Any",
        },
    },
    {
        "label": "OutputConditionPolicy",
        "lean_file": root / "lean/Runtime/VM/Model/OutputCondition.lean",
        "lean_type": "OutputConditionPolicy",
        "rust_file": root / "rust/vm/src/output_condition.rs",
        "rust_type": "OutputConditionPolicy",
        "map": {
            "disabled": "Disabled",
            "allowAll": "AllowAll",
            "denyAll": "DenyAll",
            "predicateAllowList": "PredicateAllowList",
        },
    },
    {
        "label": "Value",
        "lean_file": root / "lean/Protocol/Values.lean",
        "lean_type": "Value",
        "rust_file": root / "rust/vm/src/coroutine.rs",
        "rust_type": "Value",
        "map": {
            "string": "Str",
            "chan": "Endpoint",
        },
    },
]

struct_checks = [
    {
        "label": "ProgressToken",
        "lean_file": root / "lean/Runtime/VM/Model/State.lean",
        "lean_type": "ProgressToken",
        "rust_file": root / "rust/vm/src/coroutine.rs",
        "rust_type": "ProgressToken",
        "map": {},
    },
]

verify_workflow = root / ".github/workflows/verify.yml"
check_workflow = root / ".github/workflows/check.yml"
justfile = root / "justfile"

mismatches: list[str] = []
for check in enum_checks:
    lean_variants = parse_lean_inductive_variants(check["lean_file"], check["lean_type"])
    rust_variants = parse_rust_enum_variants(check["rust_file"], check["rust_type"])

    lean_norm = {normalize_lean_variant(name, check["map"]) for name in lean_variants}
    rust_set = set(rust_variants)

    missing_in_lean = sorted(rust_set - lean_norm)
    missing_in_rust = sorted(lean_norm - rust_set)

    print(f"[parity] {check['label']}: Lean={sorted(lean_norm)} Rust={sorted(rust_set)}")

    for variant in missing_in_lean:
        mismatches.append(f"{check['label']}:missing_in_lean:{variant}")
    for variant in missing_in_rust:
        mismatches.append(f"{check['label']}:missing_in_rust:{variant}")

for check in struct_checks:
    lean_fields = parse_lean_structure_fields(check["lean_file"], check["lean_type"])
    rust_fields = parse_rust_struct_fields(check["rust_file"], check["rust_type"])
    lean_norm = {check["map"].get(name, name) for name in lean_fields}
    rust_set = set(rust_fields)

    missing_in_lean = sorted(rust_set - lean_norm)
    missing_in_rust = sorted(lean_norm - rust_set)

    print(f"[parity] {check['label']}: LeanFields={sorted(lean_norm)} RustFields={sorted(rust_set)}")

    for field in missing_in_lean:
        mismatches.append(f"{check['label']}:missing_field_in_lean:{field}")
    for field in missing_in_rust:
        mismatches.append(f"{check['label']}:missing_field_in_rust:{field}")

if mismatches:
    print("[parity] uncovered mismatches:")
    for mismatch in mismatches:
        print(f"  - {mismatch}")
    fail("found Lean/Rust parity mismatches - add deviation entry to docs/15_vm_parity.md Deviation Registry")

print("[parity] policy/data shape parity check passed with no mismatches")

verify_text = verify_workflow.read_text(encoding="utf-8")
check_text = check_workflow.read_text(encoding="utf-8")
just_text = justfile.read_text(encoding="utf-8")

required_ci_markers = [
    ("verify workflow parity gate", "just check-parity", verify_text),
    ("check workflow parity gate", "./scripts/check-parity.sh", check_text),
    ("ci-dry-run parity gate", "just check-parity", just_text),
]

for desc, needle, haystack in required_ci_markers:
    if needle not in haystack:
        fail(f"missing {desc}: expected marker `{needle}`")

print("[parity] CI parity-regression gates are present in workflows and ci-dry-run")
PY
}

# --- Suite: VM Differential Parity Suite ---
check_suite() {
  echo "== VM Parity Suite =="
  run_check "lean conformance corpus" \
    "cargo test -p telltale-vm --test conformance_lean"
  run_check "lean equivalence corpus" \
    "cargo test -p telltale-vm --test equivalence_lean"
  run_check "differential step corpus" \
    "cargo test -p telltale-vm --test differential_step_corpus"
  run_check "bridge vm correspondence" \
    "cargo test -p telltale-lean-bridge --test vm_correspondence_tests"
  run_check "bridge vm differential-step correspondence" \
    "cargo test -p telltale-lean-bridge --test vm_differential_step_tests"
  run_check "simulator lean-reference parity suite" \
    "cargo test -p telltale-simulator --test lean_reference_parity"
  run_check "simulator material parity fixtures (Rust handlers)" \
    "cargo test -p telltale-simulator --test material_handler_parity"
  run_check "simulator material parity fixtures (Lean mirror)" \
    "if command -v lake >/dev/null 2>&1; then lake --dir lean build simulator_parity_tests && ./lean/.lake/build/bin/simulator_parity_tests; else echo '[parity] SKIP: lake not found; skipping Lean mirror simulator parity check'; fi"
  run_check "threaded parity equivalence" \
    "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_equivalence"
  run_check "planner trace worker-count conformance" \
    "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_lane_runtime planner_trace_is_worker_count_invariant_for_fixed_ready_set"
  run_check "v2 parity fixtures (speculation/scheduler/failure-envelope)" \
    "TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test parity_fixtures_v2"
}

# --- Conformance: Strict VM Conformance ---
check_conformance() {
  echo "== Strict VM Conformance =="

  # Cooperative backend
  cargo test -p telltale-vm --test conformance_lean
  cargo test -p telltale-vm --test equivalence_lean
  cargo test -p telltale-vm --test lean_vm_equivalence
  cargo test -p telltale-vm --test trace_corpus
  cargo test -p telltale-vm --test strict_tick_equality

  cargo test -p telltale-vm --test differential_step_corpus
  cargo test -p telltale-vm --test strict_value_rejection
  cargo test -p telltale-vm --test instruction_fault_snapshots
  cargo test -p telltale-vm --test schedule_robustness
  cargo test -p telltale-vm --test serialization_strict_lean
  cargo test -p telltale-vm --test bytecode_mutation_conformance

  # Threaded backend
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_feature_contract
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_equivalence
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test threaded_lane_runtime
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test differential_step_corpus
  TT_EXPECT_MULTI_THREAD=1 cargo test -p telltale-vm --features multi-thread --test schedule_robustness

  echo "OK   strict VM conformance passed"
}

# --- Main ---
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
