import Runtime.ProtocolMachine.Model.Program
import Runtime.ProtocolMachine.Model.SemanticObjects.Core

set_option autoImplicit false

/-!
# Runtime.Proofs.Lowering.Core

Proof-oriented lowering chain for relating the language surface to parsed AST,
semantic objects, protocol-machine lowering, and generated artifacts.
-/

namespace Runtime
namespace Proofs
namespace Lowering

open SessionTypes.LocalTypeR
open Classical

universe u

structure TelltaleSurfaceSpec where
  protocolName : String
  globalType : GlobalType
  requestedRoles : List Role
  proofOnlyForms : Bool := false
  wantsGeneratedArtifacts : Bool := true

structure ParsedProtocolAST where
  protocolName : String
  globalType : GlobalType
  requestedRoles : List Role
  projectedLocalTypes : List (Role × LocalTypeR) := []
  proofOnlyForms : Bool
  wantsGeneratedArtifacts : Bool

def parseSurface (surface : TelltaleSurfaceSpec) : ParsedProtocolAST :=
  { protocolName := surface.protocolName
  , globalType := surface.globalType
  , requestedRoles := surface.requestedRoles
  , projectedLocalTypes := []
  , proofOnlyForms := surface.proofOnlyForms
  , wantsGeneratedArtifacts := surface.wantsGeneratedArtifacts }

def SurfaceRefinesAST (surface : TelltaleSurfaceSpec) (ast : ParsedProtocolAST) : Prop :=
  ast = parseSurface surface

def ParsedProtocolAST.fullSpec (ast : ParsedProtocolAST) : Prop :=
  ast.requestedRoles.Nodup

def ParsedProtocolAST.projectable (ast : ParsedProtocolAST) : Prop :=
  ∀ role, role ∈ ast.requestedRoles →
    ∃ lt, (role, lt) ∈ ast.projectedLocalTypes

def ParsedProtocolAST.proofOnly (ast : ParsedProtocolAST) : Prop :=
  ast.proofOnlyForms = true

def ParsedProtocolAST.executable (ast : ParsedProtocolAST) : Prop :=
  ast.fullSpec ∧ ast.projectable ∧ ¬ ast.proofOnly

inductive LoweringRejectionReason where
  | duplicateRequestedRoles
  | nonProjectableRole (role : Role)
  | proofOnlySurface
  deriving Repr, DecidableEq

noncomputable def ParsedProtocolAST.rejectionReasons (ast : ParsedProtocolAST) :
    List LoweringRejectionReason :=
  let duplicateReasons :=
    if h : ast.fullSpec then
      []
    else
      [LoweringRejectionReason.duplicateRequestedRoles]
  let nonProjectableReasons :=
    ast.requestedRoles.foldr
      (fun role acc =>
        if h : ∃ lt, (role, lt) ∈ ast.projectedLocalTypes then
          acc
        else
          LoweringRejectionReason.nonProjectableRole role :: acc)
      []
  let proofOnlyReasons :=
    if h : ast.proofOnly then
      [LoweringRejectionReason.proofOnlySurface]
    else
      []
  duplicateReasons ++ nonProjectableReasons ++ proofOnlyReasons

structure SemanticLowering where
  ast : ParsedProtocolAST
  objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects

def ASTRefinesSemanticObjects
    (ast : ParsedProtocolAST)
    (semantic : SemanticLowering) : Prop :=
  semantic.ast = ast

structure ProtocolMachineLowering where
  semantic : SemanticLowering

def lowerASTToSemanticObjects
    (ast : ParsedProtocolAST)
    (objects : Runtime.ProtocolMachine.Model.ProtocolMachineSemanticObjects) :
    SemanticLowering :=
  { ast := ast, objects := objects }

def lowerSemanticToProtocolMachine
    (semantic : SemanticLowering) : ProtocolMachineLowering :=
  { semantic := semantic }

def SemanticObjectsRefineProtocolMachine
    (semantic : SemanticLowering)
    (lowering : ProtocolMachineLowering) : Prop :=
  lowering.semantic = semantic

private def lookupProjectedLocalType
    (role : Role) : List (Role × LocalTypeR) → Option LocalTypeR
  | [] => none
  | (role', lt) :: rest =>
      if role' = role then some lt else lookupProjectedLocalType role rest

def ProtocolMachineLowering.localTypeAt
    (lowering : ProtocolMachineLowering) (role : Role) : Option LocalTypeR :=
  lookupProjectedLocalType role lowering.semantic.ast.projectedLocalTypes

def ProtocolMachineLowering.emittedLocalTypes
    (lowering : ProtocolMachineLowering) : List (Role × LocalTypeR) :=
  lowering.semantic.ast.projectedLocalTypes

structure GeneratedArtifactSurface (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  lowering : ProtocolMachineLowering
  image : CodeImage γ ε

def lowerProtocolMachineToArtifacts
    {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (lowering : ProtocolMachineLowering) : GeneratedArtifactSurface γ ε :=
  { lowering := lowering
  , image := CodeImage.fromLocalTypes lowering.emittedLocalTypes lowering.semantic.ast.globalType }

def ProtocolMachineRefinesArtifacts
    {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (lowering : ProtocolMachineLowering)
    (artifacts : GeneratedArtifactSurface γ ε) : Prop :=
  artifacts = lowerProtocolMachineToArtifacts (γ := γ) (ε := ε) lowering

def GeneratedArtifactSurface.supportsExecution
    {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (artifacts : GeneratedArtifactSurface γ ε) : Prop :=
  artifacts.lowering.semantic.ast.executable

end Lowering
end Proofs
end Runtime
