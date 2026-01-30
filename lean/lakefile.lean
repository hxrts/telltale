import Lake
open Lake DSL

/-! # Telltale Lean Package

Lake build definition for the Telltale verification library.
Six libraries organized by subject: types, coinductive theory, choreography,
semantics, async protocol, and runtime.
-/

package telltale

-- Mathlib provides standard lemmas and automation for proofs.
-- Pin to a mathlib tag that matches the Lean toolchain.
require mathlib from "/Users/hxrts/projects/lean_common/mathlib4"

-- Paco provides parametrized coinduction for EQ2 proofs.
require paco from git
  "https://github.com/hxrts/paco-lean" @ "v0.1.3"

/-- Global and local session type definitions. -/
lean_lib SessionTypes where
  globs := #[`SessionTypes.*]

/-- Coinductive theory: EQ2, bisimulation, roundtrip bridge. -/
lean_lib SessionCoTypes where
  globs := #[`SessionCoTypes.*]

/-- Projection from global to local types and harmony correctness. -/
lean_lib Choreography where
  globs := #[`Choreography.*]

/-- Operational semantics, typing, determinism, deadlock freedom. -/
lean_lib Semantics where
  globs := #[`Semantics.*]

/-- Async buffered multiparty session types with coherence. -/
lean_lib Protocol where
  globs := #[`Protocol.*]

/-- VM, Iris separation logic backend, resource algebras, WP rules. -/
@[default_target]
lean_lib Runtime where
  globs := #[`Runtime.*]
