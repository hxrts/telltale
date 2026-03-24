import Runtime.ProtocolMachine.Model.SemanticObjects.Discipline

set_option autoImplicit false

/-!
# Runtime.Proofs.ProtocolMachine.SemanticObjects.Invariants

The Problem.
The protocol-machine semantic objects already expose semantic predicates in
`Runtime.ProtocolMachine.Model.SemanticObjects.Discipline`. This file contains
the theorem layer over those predicates.

Solution Structure.
This module proves helper theorems over the canonical semantic-object
discipline predicates. Later phases can refine these predicates into stronger
adequacy and transport results.
-/
namespace Runtime.ProtocolMachine.Model

theorem uniqueSemanticOwner_of_mem
    {objects : ProtocolMachineSemanticObjects}
    {operation₁ operation₂ : OperationInstance}
    (hUnique : objects.uniqueSemanticOwner)
    (hMem₁ : operation₁ ∈ objects.operationInstances)
    (hMem₂ : operation₂ ∈ objects.operationInstances)
    (hId : operation₁.operationId = operation₂.operationId)
    (hOwner₁ : operation₁.phase.requiresActiveOwner)
    (hOwner₂ : operation₂.phase.requiresActiveOwner) :
    operation₁.ownerId = operation₂.ownerId :=
  hUnique operation₁ hMem₁ operation₂ hMem₂ hId hOwner₁ hOwner₂

theorem observedRead_is_non_authoritative
    {read : ObservedRead} :
    read.isNonAuthoritative :=
  trivial

end Runtime.ProtocolMachine.Model
