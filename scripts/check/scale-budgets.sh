#!/usr/bin/env bash
set -euo pipefail

TELLTALE_REQUIRE_LEAN_VALIDATOR=1 cargo test -p telltale-bridge --test scale_budget_contracts -- --nocapture
echo "scale-budgets: ok"
