import Runtime.Proofs.Lowering.API
import Runtime.Proofs.TheoremPack.Build

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.DistributedLoweringProfiles

Examples tying distributed theorem-pack profiles to the existing lowering
surface. These examples intentionally start from `TelltaleSurfaceSpec` and
`ParsedProtocolAST`, so distributed profiles reuse the current choreography /
lowering path instead of introducing a separate input language.
-/

namespace Runtime
namespace Proofs
namespace Examples

open Runtime.Proofs.Lowering

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν} {State : Type v}

/-! ## Lowering-Backed Distributed Spaces -/

/-- Minimal surface used to exercise the distributed theorem-pack path. -/
def emptyDistributedSurface : TelltaleSurfaceSpec :=
  { protocolName := "distributed-empty"
  , globalType := .end
  , requestedRoles := []
  , proofOnlyForms := false
  , wantsGeneratedArtifacts := true
  }

/-- The parsed AST is produced by the canonical lowering parser. -/
def emptyDistributedAST : ParsedProtocolAST :=
  parseSurface emptyDistributedSurface

/-- The empty surface refines to its parser output by definition. -/
theorem empty_distributed_surface_refines_ast :
    SurfaceRefinesAST emptyDistributedSurface emptyDistributedAST := by
  rfl

/-- The empty AST is executable: no duplicate roles and no missing projections. -/
theorem empty_distributed_ast_executable :
    emptyDistributedAST.executable := by
  simp [ParsedProtocolAST.executable, ParsedProtocolAST.fullSpec,
    ParsedProtocolAST.projectable, ParsedProtocolAST.proofOnly,
    emptyDistributedAST, emptyDistributedSurface, parseSurface]

/-- Base invariant space annotated with the parsed AST it came from. -/
def loweringBackedDistributedSpace
    (_ast : ParsedProtocolAST)
    (bundle : ProtocolMachineLivenessBundle store₀) :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.mk
    (Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles.mk
      (ProtocolMachineInvariantSpace.mk (some bundle) none none none)
      {})
    {}

/--
Attaching a distributed CAP profile through the existing lowering-backed space
materializes the runtime theorem-pack artifact.
-/
example (bundle : ProtocolMachineLivenessBundle store₀)
    (cap : Adapters.CAPProfile) :
    let ast := emptyDistributedAST
    let space := (loweringBackedDistributedSpace
      (ν := ν) (store₀ := store₀) (State := State) ast bundle).withCAP cap
    (buildProtocolMachineTheoremPack (space := space)).capImpossibility?.isSome = true := by
  rfl

/--
Golden path: from the lowering-backed space, attaching a CAP profile yields a
concrete theorem artifact whose proof is derived by the family API.
-/
example (bundle : ProtocolMachineLivenessBundle store₀)
    (cap : Adapters.CAPProfile) :
    let ast := emptyDistributedAST
    let space := (loweringBackedDistributedSpace
      (ν := ν) (store₀ := store₀) (State := State) ast bundle).withCAP cap
    let expected : CAPImpossibilityArtifact :=
      { protocol := cap
      , proof := Distributed.CAP.impossibility_of_protocol cap
      }
    (buildProtocolMachineTheoremPack (space := space)).capImpossibility? = some expected := by
  rfl

/--
The same lowering-backed path can attach all distributed profiles at once via
the canonical distributed-profile bundle.
-/
example (bundle : ProtocolMachineLivenessBundle store₀)
    (profiles : Adapters.DistributedProfiles) :
    let ast := emptyDistributedAST
    let space := (loweringBackedDistributedSpace
      (ν := ν) (store₀ := store₀) (State := State) ast bundle).withDistributedProfiles profiles
    (buildProtocolMachineTheoremPack (space := space)).proofCarryingMetadata.progress.requiresExplicitProgressContracts =
      true := by
  rfl

end

end Examples
end Proofs
end Runtime
