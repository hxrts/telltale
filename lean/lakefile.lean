import Lake
open Lake DSL

/-! # Telltale Lean Package

Lake build definition for the Telltale verification library.
Six libraries organized by subject: types, coinductive theory, choreography,
semantics, async protocol, and runtime.
-/

package telltale where
  -- Temporarily silence linter noise from iris-lean dependencies.
  moreLeanArgs := #[
    "-Dlinter.unusedSectionVars=false",
    "-Dlinter.unusedVariables=false"
  ]

-- Paco provides parametrized coinduction for EQ2 proofs.
require paco from git
  "https://github.com/hxrts/paco-lean" @ "v0.2.0"

-- Iris separation logic framework (revision-pinned for drift control).
require iris from git
  "https://github.com/leanprover-community/iris-lean" @ "ac6e3745f735496e6db0592b17f78a4f9dbba384" / "Iris"

-- Lean 4 code formatter.
require leanfmt from git
  "https://github.com/toku-sa-n/leanfmt" @ "main"

-- Mathlib is required last so its transitive pins take precedence.
-- Mathlib provides standard lemmas and automation for proofs.
-- Revision is pinned to the exact commit used during development.
-- Run `lake exe cache get` to fetch prebuilt oleans — Mathlib is never
-- rebuilt from source when the cache is available.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

/-! ## Libraries -/

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

/-- Protocol machine, Iris separation logic backend, resource algebras, WP rules. -/
@[default_target]
lean_lib Runtime where
  globs := #[`Runtime.*]

/-- Classical transport layer: imported theorem interfaces and discharged kernels. -/
lean_lib ClassicalLayer where
  globs := #[`Classical.*]

/-- Distributed hypothesis validation and protocol-space classification. -/
lean_lib Distributed where
  globs := #[`Distributed.*]

/-- Analysis and extraction boundary layers. -/
lean_lib Entropy where
  globs := #[
    `ClassicalAnalysisAPI,
    `ClassicalAnalysisInstance,
    `ClassicalAnalysisInstance.*,
    `IrisExtractionAPI,
    `IrisExtractionInstance,
    `IrisExtractionInstance.*
  ]

/-- Finite-discrete Fisher information geometry boundary layers. -/
lean_lib FisherInformation where
  globs := #[
    `FisherInformationAPI,
    `FisherInformationInstance,
    `FisherInformationInstance.*
  ]

/-- Linker args to silence macOS deployment target warnings for test executables. -/
def macosLinkArgs : Array String :=
  -- Match the toolchain's minimum macOS version for system libraries.
  if System.Platform.isOSX then
    #["-mmacosx-version-min=15.0"]
  else
    #[]

/-! ## Executables -/

/-- Executable runtime tests for the protocol machine. -/
lean_exe runtime_tests where
  root := `Runtime.Tests.Main
  moreLinkArgs := macosLinkArgs

/-- Executable simulator parity fixtures for material dynamics. -/
lean_exe simulator_parity_tests where
  root := `Runtime.Tests.SimulatorParity
  moreLinkArgs := macosLinkArgs

/-- Protocol machine runner: executes choreographies and emits observable traces. -/
lean_exe protocol_machine_runner where
  root := `Runtime.Tests.ProtocolMachineRunner
  moreLinkArgs := macosLinkArgs

/-- Protocol machine validator: capability-model and bundle-admission checks. -/
lean_exe protocol_machine_validator where
  root := `Runtime.Tests.ProtocolMachineValidator
  moreLinkArgs := macosLinkArgs

/-- Heap parity runner: mirrors heap encoding, ordering, and proof structure. -/
lean_exe heap_parity_runner where
  root := `Runtime.Tests.HeapParityRunner
  moreLinkArgs := macosLinkArgs

/-- Reduced semantic-effect parity runner for Rust/Lean alignment. -/
lean_exe semantic_effect_parity_runner where
  root := `Runtime.Tests.SemanticEffectParity
  moreLinkArgs := macosLinkArgs

/-- Reduced search parity runner for Rust/Lean alignment. -/
lean_exe search_parity_runner where
  root := `Runtime.Tests.SearchParity
  moreLinkArgs := macosLinkArgs

/-- Projection validator (compares projected local types). -/
@[default_target]
lean_exe telltale_validator where
  root := `Choreography.Projection.Validator
  moreLinkArgs := macosLinkArgs
