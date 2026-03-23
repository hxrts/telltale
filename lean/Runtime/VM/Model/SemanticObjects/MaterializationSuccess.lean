import Runtime.VM.Model.SemanticObjects.Core
import Runtime.VM.Model.SemanticObjects.Invariants
import Runtime.VM.Model.SemanticObjects.AuthoritativeReadsPublication

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

def CanonicalHandle.sameHandleDomain
    (left right : CanonicalHandle) : Prop :=
  left.session = right.session ∧
  left.ownerId = right.ownerId ∧
  left.kind = right.kind

def PublicationEvent.adequateForSuccessContext
    (event : PublicationEvent)
    (ctx : SuccessProofContext)
    (proof : MaterializationProof)
    (handle : CanonicalHandle) : Prop :=
  event.operationId = ctx.operationId ∧
  event.session = ctx.session ∧
  event.status = .published ∧
  event.observerClass = .canonical ∧
  event.proofRef = some proof.proofId ∧
  event.handleRef = some handle.handleId

def ProtocolMachineSemanticObjects.hasAdequateSuccessArtifacts
    (objects : ProtocolMachineSemanticObjects)
    (ctx : SuccessProofContext) : Prop :=
  ∃ proof ∈ objects.materializationProofs,
    proof.adequateForSuccessContext ctx ∧
    ∃ handle ∈ objects.canonicalHandles,
      handle.adequateForSuccessContext ctx proof

def ProtocolMachineSemanticObjects.authoritativeMaterializationAdequate
    (objects : ProtocolMachineSemanticObjects)
    (ctx : SuccessProofContext) : Prop :=
  ∃ proof ∈ objects.materializationProofs,
    proof.adequateForSuccessContext ctx ∧
    ∃ handle ∈ objects.canonicalHandles,
      handle.adequateForSuccessContext ctx proof ∧
      ∃ event ∈ objects.publicationEvents,
        event.adequateForSuccessContext ctx proof handle ∧
        event.hasCanonicalAuthorityEvidence

def ProtocolMachineSemanticObjects.canonicalHandleDomainUnique
    (objects : ProtocolMachineSemanticObjects)
    (ctx : SuccessProofContext) : Prop :=
  ∀ handle₁ ∈ objects.canonicalHandles,
    ∀ handle₂ ∈ objects.canonicalHandles,
      (∃ proof ∈ objects.materializationProofs,
        proof.adequateForSuccessContext ctx ∧
        handle₁.adequateForSuccessContext ctx proof) →
      (∃ proof ∈ objects.materializationProofs,
        proof.adequateForSuccessContext ctx ∧
        handle₂.adequateForSuccessContext ctx proof) →
      handle₁.handleId = handle₂.handleId

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

def ProtocolMachineSemanticObjects.weakerPublicationInsufficient
    (objects : ProtocolMachineSemanticObjects)
    (ctx : SuccessProofContext) : Prop :=
  ∀ event ∈ objects.publicationEvents,
    event.observerClass ≠ .canonical →
      ∀ proof ∈ objects.materializationProofs,
        ∀ handle ∈ objects.canonicalHandles,
          ¬ event.adequateForSuccessContext ctx proof handle

end Runtime.VM.Model
