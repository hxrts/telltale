import Lake
open Lake DSL

/-! # RumpsteakV2 Lean Package

Lake build definition for the RumpsteakV2 verification library.
V1 (Rumpsteak) is intentionally excluded from build targets.
-/

package rumpsteakLean

-- Mathlib provides standard lemmas and automation for proofs.
-- Pin to a mathlib tag that matches the Lean toolchain.
require mathlib from "/Users/hxrts/projects/lean_common/mathlib4"

-- Pin Mathlib's dependencies to the versions it was tested with
-- (prevents Lake from resolving to newer incompatible versions)
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "24241822"
require Qq from git
  "https://github.com/leanprover-community/quote4" @ "93125039"
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "2f6d2387"
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "b4fb2aa5"
require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "933fce7e"
require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "e9f31324"
require LeanSearchClient from git
  "https://github.com/leanprover-community/LeanSearchClient" @ "3591c3f6"
require plausible from git
  "https://github.com/leanprover-community/plausible" @ "160af9e8"

-- Paco provides parametrized coinduction for EQ2 proofs.
require paco from git
  "https://github.com/hxrts/paco-lean" @ "v0.1.3"

/-- V2 library containing the new protocol semantics and proofs. -/
@[default_target]
lean_lib RumpsteakV2 where
  globs := #[`RumpsteakV2.*]

/-- Session types with async effects - formalized preservation proofs. -/
lean_lib Effects where
  globs := #[`Effects.*]

-- Linter executables disabled due to module build complexity and cache issues
