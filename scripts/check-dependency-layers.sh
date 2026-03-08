#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if ! command -v python3 >/dev/null 2>&1; then
  echo "error: python3 is required" >&2
  exit 2
fi

if ! command -v cargo >/dev/null 2>&1; then
  echo "error: cargo is required" >&2
  exit 2
fi

echo "Checking TellTale dependency-layer ordering..."
echo

python3 - "$ROOT_DIR" <<'PY'
import json
import subprocess
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve()
metadata_json = subprocess.check_output(
    ["cargo", "metadata", "--no-deps", "--format-version", "1"],
    cwd=root,
    text=True,
)
metadata = json.loads(metadata_json)

layer_of = {
    # Foundation
    "telltale-types": 1,
    # Core algorithm and macro layer
    "telltale-theory": 2,
    "telltale-macros": 2,
    # Runtime/verification
    "telltale-vm": 3,
    # Session tooling, transport, and facade layer
    "telltale-choreography": 4,
    "telltale-lean-bridge": 4,
    "telltale-simulator": 4,
    "telltale-transport": 4,
    "telltale": 4,
    # Internal support utility
    "effect-scaffold": 4,
}

workspace_members = set(metadata["workspace_members"])
packages = {pkg["name"]: pkg for pkg in metadata["packages"] if pkg["id"] in workspace_members}

errors = []
unknown = []

for package_name, package in packages.items():
    if package_name not in layer_of:
        unknown.append(f"package_not_layered={package_name}")
        continue

    package_layer = layer_of[package_name]
    for dep in package["dependencies"]:
        if dep["source"] is not None:
            continue
        if dep.get("kind") not in (None,):
            continue

        dep_name = dep["name"]
        if dep_name not in layer_of:
            unknown.append(f"{package_name} -> {dep_name}")
            continue

        dep_layer = layer_of[dep_name]
        if dep_layer > package_layer:
            errors.append((package_name, package_layer, dep_name, dep_layer))

if unknown:
    print("Dependency layer check failed: unmapped local dependencies detected.")
    print("Add these crates to the layer map:")
    for item in sorted(set(unknown)):
        print(f"  - {item}")
    print()

if errors:
    print("Dependency layer check failed: forbidden upward dependency found.")
    for package_name, package_layer, dep_name, dep_layer in sorted(errors):
        print(f"  - {package_name}(L{package_layer}) -> {dep_name}(L{dep_layer})")
    print()

if unknown or errors:
    total = len(errors) + len(set(unknown))
    print(f"dependency-layer violations: {total}")
    sys.exit(1)

print("dependency-layer check passed")
print(f"checked {len(packages)} workspace packages")
PY
