import Runtime.ProtocolMachine.Model.TypeClasses
import Runtime.ProtocolMachine.Model.Domain
import Runtime.ProtocolMachine.Model.Core
import Runtime.ProtocolMachine.Model.OutputCondition
import Runtime.ProtocolMachine.Model.Violation
import Runtime.ProtocolMachine.Model.SchedulerTypes
import Runtime.ProtocolMachine.Model.Knowledge
import Runtime.ProtocolMachine.Model.Config
import Runtime.ProtocolMachine.Model.CompileLocalTypeR
import Runtime.ProtocolMachine.Model.Program
import Runtime.ProtocolMachine.Model.Effects
import Runtime.ProtocolMachine.Model.SemanticObjects.Core
import Runtime.ProtocolMachine.Model.SemanticObjects.Discipline
import Runtime.ProtocolMachine.Model.SemanticObjects.OutstandingEffects
import Runtime.ProtocolMachine.Model.SemanticObjects.SemanticHandoffTransition
import Runtime.ProtocolMachine.Model.SemanticObjects.AuthoritativeReadsPublication
import Runtime.ProtocolMachine.Model.SemanticObjects.MaterializationSuccess
import Runtime.ProtocolMachine.Model.SemanticObjects.ProgressContracts
import Runtime.ProtocolMachine.Model.SemanticObjects.ReplayFailureExactness
import Runtime.ProtocolMachine.Model.SemanticObjects.CrossTargetProgressDependentWork
import Runtime.ProtocolMachine.Model.SemanticObjects.TransformationLocalObligations
import Runtime.ProtocolMachine.Model.State
import Runtime.ProtocolMachine.Model.UnitModel

set_option autoImplicit false


/-! # Runtime.ProtocolMachine.Model

protocol machine data model layer: types, configuration, protocol image/model state, and
unit/default model instances.
-/
