import Lake
open Lake DSL

/-! # RumpsteakV2 Lean Package

Lake build definition for the RumpsteakV2 verification library.
V1 (Rumpsteak) is intentionally excluded from build targets.
-/

package rumpsteakLean

-- Mathlib provides standard lemmas and automation for proofs.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.0"

/-- V2 library containing the new protocol semantics and proofs. -/
@[default_target]
lean_lib RumpsteakV2 where
  globs := #[`RumpsteakV2.*]
