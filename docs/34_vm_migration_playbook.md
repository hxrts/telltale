# VM Migration Playbook for Intentional Parity Breaks

Use this playbook when introducing a Lean/Rust mismatch intentionally.

## Step 1: Define the Break

- Record scope (files, types, behavior).
- Explain why parity cannot be kept.

## Step 2: Record Justification

- Fill `docs/templates/justified_break.md`.
- Add entry in `docs/lean_vs_rust_deviations.json` with owner + revisit date + coverage fingerprints.

## Step 3: Contain Blast Radius

- Keep mismatch local to one module boundary.
- Add explicit adapters/translators where needed.

## Step 4: Add Guardrails

- Add tests that lock the intended behavior.
- Ensure CI checks fail on uncatalogued mismatches.

## Step 5: Plan Reconciliation

- Track exit criteria for removing the break.
- Revisit by the listed date.
