import Lake
open Lake DSL

/-! # RumpsteakV2 Lean Package

Lake build definition for the RumpsteakV2 verification library.
V1 (Rumpsteak) is intentionally excluded from build targets.
-/

package rumpsteakLean

-- Mathlib provides standard lemmas and automation for proofs.
-- Pin to a mathlib tag that matches the Lean toolchain.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0-rc1"

-- Paco provides parametrized coinduction for EQ2 proofs.
require paco from git
  "https://github.com/hxrts/paco-lean" @ "bfac3ec"

/-- V2 library containing the new protocol semantics and proofs. -/
@[default_target]
lean_lib RumpsteakV2 where
  globs := #[`RumpsteakV2.*]
