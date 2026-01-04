import Lake
open Lake DSL

/-! # Rumpsteak Lean Package

Lake build definition for the Rumpsteak verification library and runner.

## Targets

- `Rumpsteak` - Library containing protocol definitions and proofs
- `rumpsteak_runner` - CLI executable for validating choreographies
-/

package rumpsteakLean

-- Mathlib provides standard lemmas and automation for proofs.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

/-- The main library containing all Protocol, Proofs, Runner, and Diagnostics modules. -/
lean_lib Rumpsteak

/-- CLI executable for validating choreography/program pairs. -/
@[default_target]
lean_exe rumpsteak_runner where
  root := `Rumpsteak.Runner.Main
  supportInterpreter := true
