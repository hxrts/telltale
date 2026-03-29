#!/usr/bin/env bash

# Publishable crates in release order (leaves first).
RELEASE_PACKAGES=(
  "telltale-types"
  "telltale-language"
  "telltale-theory"
  "telltale-macros"
  "telltale-machine"
  "telltale"
  "telltale-runtime"
  "telltale-transport"
  "telltale-simulator"
  "telltale-bridge"
)

WASM_EXAMPLE_LOCK_PATH="examples/wasm/Cargo.lock"
WASM_EXAMPLE_LOCK_PACKAGES=(
  "telltale"
  "telltale-language"
  "telltale-machine"
  "telltale-macros"
  "telltale-theory"
  "telltale-types"
)

manifest_path() {
  local crate="$1"
  case "${crate}" in
    telltale-types) echo "rust/types/Cargo.toml" ;;
    telltale-language) echo "rust/language/Cargo.toml" ;;
    telltale-theory) echo "rust/theory/Cargo.toml" ;;
    telltale-macros) echo "rust/macros/Cargo.toml" ;;
    telltale-machine) echo "rust/machine/Cargo.toml" ;;
    telltale) echo "Cargo.toml" ;;
    telltale-runtime) echo "rust/runtime/Cargo.toml" ;;
    telltale-transport) echo "rust/transport/Cargo.toml" ;;
    telltale-simulator) echo "rust/simulator/Cargo.toml" ;;
    telltale-bridge) echo "rust/bridge/Cargo.toml" ;;
    *)
      echo "unknown package: ${crate}" >&2
      return 1
      ;;
  esac
}
