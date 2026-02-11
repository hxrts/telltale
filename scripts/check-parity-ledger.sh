#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEDGER_PATH="${ROOT_DIR}/docs/lean_vs_rust_deviations.json"

if [[ ! -f "${LEDGER_PATH}" ]]; then
  echo "error: missing deviation ledger at ${LEDGER_PATH}" >&2
  exit 1
fi

python3 - "${ROOT_DIR}" "${LEDGER_PATH}" <<'PY'
import json
import re
import sys
from pathlib import Path
from datetime import datetime

root = Path(sys.argv[1])
ledger_path = Path(sys.argv[2])


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

try:
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
except json.JSONDecodeError as exc:
    fail(f"invalid JSON in {ledger_path}: {exc}")

if not isinstance(ledger, dict):
    fail("deviation ledger root must be a JSON object")
if not isinstance(ledger.get("schema_version"), int):
    fail("deviation ledger must include integer schema_version")
deviations = ledger.get("deviations")
if not isinstance(deviations, list):
    fail("deviation ledger must include array field deviations")

allowed_status = {"active", "resolved"}
seen_ids: set[str] = set()
active_coverage: set[str] = set()

required_fields = {
    "id",
    "owner",
    "status",
    "reason",
    "impact",
    "alternatives_considered",
    "revisit_date",
    "covers",
    "lean_refs",
    "rust_refs",
}

for idx, entry in enumerate(deviations):
    if not isinstance(entry, dict):
        fail(f"deviations[{idx}] must be an object")
    missing = sorted(required_fields - set(entry.keys()))
    if missing:
        fail(f"deviations[{idx}] missing required fields: {', '.join(missing)}")

    entry_id = entry["id"]
    if not isinstance(entry_id, str) or not entry_id:
        fail(f"deviations[{idx}].id must be a non-empty string")
    if entry_id in seen_ids:
        fail(f"duplicate deviation id: {entry_id}")
    seen_ids.add(entry_id)

    status = entry["status"]
    if status not in allowed_status:
        fail(f"deviation {entry_id}: status must be one of {sorted(allowed_status)}")

    owner = entry["owner"]
    if not isinstance(owner, str) or not owner.strip():
        fail(f"deviation {entry_id}: owner must be a non-empty string")

    revisit = entry["revisit_date"]
    if not isinstance(revisit, str):
        fail(f"deviation {entry_id}: revisit_date must be a YYYY-MM-DD string")
    try:
        datetime.strptime(revisit, "%Y-%m-%d")
    except ValueError:
        fail(f"deviation {entry_id}: invalid revisit_date (expected YYYY-MM-DD)")

    covers = entry["covers"]
    if not isinstance(covers, list) or not all(isinstance(item, str) for item in covers):
        fail(f"deviation {entry_id}: covers must be an array of strings")

    for ref_field in ("lean_refs", "rust_refs"):
        refs = entry[ref_field]
        if not isinstance(refs, list) or not refs or not all(isinstance(item, str) for item in refs):
            fail(f"deviation {entry_id}: {ref_field} must be a non-empty array of strings")

    for text_field in ("reason", "impact", "alternatives_considered"):
        if not isinstance(entry[text_field], str) or not entry[text_field].strip():
            fail(f"deviation {entry_id}: {text_field} must be a non-empty string")

    if status == "active":
        if not covers:
            fail(f"deviation {entry_id}: active deviation must cover at least one mismatch fingerprint")
        active_coverage.update(covers)

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

if not mismatches:
    print("[parity] policy/data shape parity check passed with no mismatches")
else:
    uncovered = [m for m in mismatches if m not in active_coverage]
    if uncovered:
        print("[parity] uncovered mismatches:")
        for mismatch in uncovered:
            print(f"  - {mismatch}")
        fail("found Lean/Rust parity mismatches without active ledger coverage")
    print("[parity] mismatches are fully covered by active ledger entries")

verify_text = verify_workflow.read_text(encoding="utf-8")
check_text = check_workflow.read_text(encoding="utf-8")
just_text = justfile.read_text(encoding="utf-8")

required_ci_markers = [
    ("verify workflow parity ledger gate", "just check-parity-ledger", verify_text),
    ("verify workflow parity suite gate", "just check-vm-parity-suite", verify_text),
    ("check workflow parity ledger gate", "./scripts/check-parity-ledger.sh", check_text),
    ("check workflow parity suite gate", "./scripts/check-vm-parity-suite.sh", check_text),
    ("ci-dry-run parity ledger gate", "just check-parity-ledger", just_text),
    ("ci-dry-run parity suite gate", "just check-vm-parity-suite", just_text),
]

for desc, needle, haystack in required_ci_markers:
    if needle not in haystack:
        fail(f"missing {desc}: expected marker `{needle}`")

print("[parity] CI parity-regression gates are present in workflows and ci-dry-run")
PY
