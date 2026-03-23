import Runtime.VM.Model.SemanticObjects.Core
import Runtime.VM.Model.SemanticObjects.Invariants

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.AuthoritativeReadsPublication

The Problem.
The protocol-machine needs a theorem-facing distinction between authoritative
reads that may justify commitment and observational reads that may not. It also
needs a precise publication discipline so canonical publication paths and
observer-class visibility are explicit semantic objects.

Solution Structure.
This module defines authoritative-commitment contexts, observer-class
projections over publication events, and the core predicates that rule out
observed-state promotion and duplicate canonical publication roots.
-/

namespace Runtime.VM.Model

/-! ## Commitment Contexts -/

structure AuthoritativeCommitmentContext where
  operationId : String
  session : Option Nat
  ownerId : Option String
  requiredKind : AuthoritativeReadKind
  requiredGeneration : Option Nat
  requiresWitness : Bool
  publicationObserverClass : PublicationObserverClass
  deriving Repr, DecidableEq

def AuthoritativeRead.satisfiesCommitmentContext
    (read : AuthoritativeRead)
    (ctx : AuthoritativeCommitmentContext) : Prop :=
  read.hasAuthorityContext ∧
  read.session = ctx.session ∧
  read.ownerId = ctx.ownerId ∧
  read.kind = ctx.requiredKind ∧
  (match ctx.requiredGeneration with
   | none => True
   | some generation => read.generation = some generation) ∧
  (¬ ctx.requiresWitness ∨ read.witnessId.isSome) ∧
  read.lifecycle = .verified

def ObservedRead.satisfiesCommitmentContext
    (_read : ObservedRead)
    (_ctx : AuthoritativeCommitmentContext) : Prop :=
  False

def ProtocolMachineSemanticObjects.authoritativeCommitPermitted
    (objects : ProtocolMachineSemanticObjects)
    (ctx : AuthoritativeCommitmentContext) : Prop :=
  ∃ read ∈ objects.authoritativeReads,
    read.satisfiesCommitmentContext ctx

def ProtocolMachineSemanticObjects.observedStateCannotAuthorTruth
    (objects : ProtocolMachineSemanticObjects)
    (ctx : AuthoritativeCommitmentContext) : Prop :=
  ∀ read ∈ objects.observedReads,
    ¬ read.satisfiesCommitmentContext ctx

/-! ## Publication Discipline -/

def PublicationEvent.visibleToObserverClass
    (event : PublicationEvent)
    (observerClass : PublicationObserverClass) : Prop :=
  event.observerClass = observerClass ∧ event.status = .published

def PublicationEvent.canonicalPublicationFor
    (event : PublicationEvent)
    (ctx : AuthoritativeCommitmentContext) : Prop :=
  event.operationId = ctx.operationId ∧
  event.session = ctx.session ∧
  event.observerClass = ctx.publicationObserverClass ∧
  event.status = .published

def PublicationEvent.hasCanonicalAuthorityEvidence
    (event : PublicationEvent) : Prop :=
  event.ownerId.isSome ∧ event.proofRef.isSome ∧ event.handleRef.isSome

def ProtocolMachineSemanticObjects.observerPublicationProjection
    (objects : ProtocolMachineSemanticObjects)
    (observerClass : PublicationObserverClass) : List PublicationEvent :=
  objects.publicationEvents.filter (fun event =>
    match event.observerClass, event.status with
    | cls, .published => decide (cls = observerClass)
    | _, _ => false)

def ProtocolMachineSemanticObjects.canonicalPublicationPathUnique
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ event₁ ∈ objects.publicationEvents,
    ∀ event₂ ∈ objects.publicationEvents,
      event₁.observerClass = .canonical →
      event₂.observerClass = .canonical →
      event₁.status = .published →
      event₂.status = .published →
      event₁.operationId = event₂.operationId →
      event₁.session = event₂.session →
      event₁.publicationId = event₂.publicationId

def ProtocolMachineSemanticObjects.canonicalPublicationSurfaceExclusive
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ event₁ ∈ objects.publicationEvents,
    ∀ event₂ ∈ objects.publicationEvents,
      event₁.observerClass = .canonical →
      event₂.observerClass = .canonical →
      event₁.status = .published →
      event₂.status = .published →
      event₁.operationId = event₂.operationId →
      event₁.session = event₂.session →
      event₁.publicationId = event₂.publicationId ∧
      event₁.proofRef = event₂.proofRef ∧
      event₁.handleRef = event₂.handleRef

def ProtocolMachineSemanticObjects.publicationObserverClassDisciplined
    (objects : ProtocolMachineSemanticObjects) : Prop :=
  ∀ event ∈ objects.publicationEvents,
    event.observerClass = .canonical →
      event.status = .published →
      event.hasCanonicalAuthorityEvidence

def ProtocolMachineSemanticObjects.commitmentPublicationDisciplined
    (objects : ProtocolMachineSemanticObjects)
    (ctx : AuthoritativeCommitmentContext) : Prop :=
  objects.authoritativeCommitPermitted ctx →
    ∃ event ∈ objects.publicationEvents,
      event.canonicalPublicationFor ctx ∧ event.hasCanonicalAuthorityEvidence

end Runtime.VM.Model
