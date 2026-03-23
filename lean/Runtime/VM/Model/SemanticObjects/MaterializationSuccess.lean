import Runtime.VM.Model.SemanticObjects.Core
import Runtime.VM.Model.SemanticObjects.Invariants

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.MaterializationSuccess

The Problem.
Parity-critical operations need an explicit success-proof story: semantic
success on targeted paths must be backed by a materialization proof and a
canonical handle, while weaker observational reads must not establish
canonical materialization.

Solution Structure.
This module defines success-proof contexts, adequacy conditions for
`MaterializationProof` and `CanonicalHandle`, and the core protocol-machine
predicates that express proof-backed success and the insufficiency of
observational reads.
-/

namespace Runtime.VM.Model

structure SuccessProofContext where
  operationId : String
  operationKind : String
  session : Option Nat
  requiredPredicateRef : String
  requiredHandleKind : CanonicalHandleKind
  requiredOutputDigest : Option String
  requiresWitnessRef : Bool
  deriving Repr, DecidableEq

def OperationInstance.requiresSuccessProofFor
    (operation : OperationInstance)
    (ctx : SuccessProofContext) : Prop :=
  operation.operationId = ctx.operationId ∧
  operation.kind = ctx.operationKind ∧
  operation.session = ctx.session ∧
  operation.phase = .succeeded ∧
  operation.requiresProof

def MaterializationProof.adequateForSuccessContext
    (proof : MaterializationProof)
    (ctx : SuccessProofContext) : Prop :=
  proof.session = ctx.session ∧
  proof.predicateRef = ctx.requiredPredicateRef ∧
  (match ctx.requiredOutputDigest with
   | none => True
   | some digest => proof.outputDigest = digest) ∧
  (¬ ctx.requiresWitnessRef ∨ proof.witnessRef.isSome) ∧
  proof.passed

def CanonicalHandle.adequateForSuccessContext
    (handle : CanonicalHandle)
    (ctx : SuccessProofContext)
    (proof : MaterializationProof) : Prop :=
  handle.session = ctx.session ∧
  handle.kind = ctx.requiredHandleKind ∧
  handle.proofRef = some proof.proofId

def ProtocolMachineSemanticObjects.hasAdequateSuccessArtifacts
    (objects : ProtocolMachineSemanticObjects)
    (ctx : SuccessProofContext) : Prop :=
  ∃ proof ∈ objects.materializationProofs,
    proof.adequateForSuccessContext ctx ∧
    ∃ handle ∈ objects.canonicalHandles,
      handle.adequateForSuccessContext ctx proof

def ProtocolMachineSemanticObjects.successProofBacked
    (objects : ProtocolMachineSemanticObjects)
    (ctx : SuccessProofContext) : Prop :=
  ∀ operation ∈ objects.operationInstances,
    operation.requiresSuccessProofFor ctx →
      objects.hasAdequateSuccessArtifacts ctx

def ProtocolMachineSemanticObjects.semanticSuccessPermitted
    (objects : ProtocolMachineSemanticObjects)
    (ctx : SuccessProofContext) : Prop :=
  ∃ operation ∈ objects.operationInstances,
    operation.requiresSuccessProofFor ctx ∧
      objects.hasAdequateSuccessArtifacts ctx

def ObservedRead.establishesCanonicalMaterialization
    (_read : ObservedRead)
    (_ctx : SuccessProofContext) : Prop :=
  False

def ProtocolMachineSemanticObjects.observedMaterializationInsufficient
    (objects : ProtocolMachineSemanticObjects)
    (ctx : SuccessProofContext) : Prop :=
  ∀ read ∈ objects.observedReads,
    ¬ read.establishesCanonicalMaterialization ctx

end Runtime.VM.Model
