import Runtime.VM.Model.TypeClasses
import Runtime.VM.Model.Domain
import Runtime.VM.Model.Core
import Runtime.VM.Model.OutputCondition
import Runtime.VM.Model.Violation
import Runtime.VM.Model.SchedulerTypes
import Runtime.VM.Model.Knowledge
import Runtime.VM.Model.Config
import Runtime.VM.Model.CompileLocalTypeR
import Runtime.VM.Model.Program
import Runtime.VM.Model.Effects
import Runtime.VM.Model.EffectsLemmas
import Runtime.VM.Model.SemanticObjects.Core
import Runtime.VM.Model.SemanticObjects.Invariants
import Runtime.VM.Model.SemanticObjects.OutstandingEffects
import Runtime.VM.Model.SemanticObjects.OutstandingEffectsLemmas
import Runtime.VM.Model.SemanticObjects.SemanticHandoffTransition
import Runtime.VM.Model.SemanticObjects.SemanticHandoffLemmas
import Runtime.VM.Model.SemanticObjects.AuthoritativeReadsPublication
import Runtime.VM.Model.SemanticObjects.AuthoritativeReadsPublicationLemmas
import Runtime.VM.Model.SemanticObjects.MaterializationSuccess
import Runtime.VM.Model.SemanticObjects.MaterializationSuccessLemmas
import Runtime.VM.Model.SemanticObjects.ProgressContracts
import Runtime.VM.Model.SemanticObjects.ProgressContractsLemmas
import Runtime.VM.Model.SemanticObjects.ReplayFailureExactness
import Runtime.VM.Model.SemanticObjects.ReplayFailureExactnessLemmas
import Runtime.VM.Model.SemanticObjects.CrossTargetProgressDependentWork
import Runtime.VM.Model.SemanticObjects.CrossTargetProgressDependentWorkLemmas
import Runtime.VM.Model.SemanticObjects.TransformationLocalObligations
import Runtime.VM.Model.SemanticObjects.TransformationLocalObligationsLemmas
import Runtime.VM.Model.State
import Runtime.VM.Model.UnitModel

set_option autoImplicit false


/-! # Runtime.VM.Model

VM data model layer: types, configuration, protocol image/model state, and
unit/default model instances.
-/
