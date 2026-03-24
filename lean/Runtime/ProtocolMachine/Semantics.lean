import Runtime.ProtocolMachine.Semantics.InstrSpec
import Runtime.ProtocolMachine.Semantics.ExecHelpers
import Runtime.ProtocolMachine.Semantics.ExecComm
import Runtime.ProtocolMachine.Semantics.ExecSession
import Runtime.ProtocolMachine.Semantics.ExecOwnership
import Runtime.ProtocolMachine.Semantics.ExecControl
import Runtime.ProtocolMachine.Semantics.ExecGuardEffect
import Runtime.ProtocolMachine.Semantics.ExecSpeculation
import Runtime.ProtocolMachine.Semantics.ExecSteps
import Runtime.ProtocolMachine.Semantics.Exec

set_option autoImplicit false


/-! # Runtime.ProtocolMachine.Semantics

Operational and denotational instruction semantics for protocol machine execution.
-/
