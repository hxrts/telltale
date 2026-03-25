import Runtime.ProtocolMachine.Model.SemanticObjects.Core
import Runtime.ProtocolMachine.Model.SemanticObjects.AgreementCore
import Runtime.ProtocolMachine.Model.SemanticObjects.Discipline
import Runtime.ProtocolMachine.Model.SemanticObjects.OutstandingEffects
import Runtime.ProtocolMachine.Model.SemanticObjects.SemanticHandoffTransition
import Runtime.ProtocolMachine.Model.SemanticObjects.AuthoritativeReadsPublication
import Runtime.ProtocolMachine.Model.SemanticObjects.MaterializationSuccess
import Runtime.ProtocolMachine.Model.SemanticObjects.ProgressContracts
import Runtime.ProtocolMachine.Model.SemanticObjects.ReplayFailureExactness
import Runtime.ProtocolMachine.Model.SemanticObjects.CrossTargetProgressDependentWork
import Runtime.ProtocolMachine.Model.SemanticObjects.TransformationLocalObligations

set_option autoImplicit false

/-! # Runtime.ProtocolMachine.Model.SemanticObjects

Canonical import point for the protocol-machine semantic-object family.

This barrel keeps the executable semantic-object vocabulary under
`Runtime.ProtocolMachine.Model/` proof-free while re-exporting the discipline and
executable semantic relations defined over that vocabulary.
-/
