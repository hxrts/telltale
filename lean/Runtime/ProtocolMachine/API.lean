import Runtime.ProtocolMachine.Model.State
import Runtime.ProtocolMachine.Semantics.Exec


/-! # protocol machine Definition (Re-exports)

Single import point for the protocol machine specification. Importing this file gives access to
the full runtime state (`ProtocolMachineState`, `CoroutineState`, events, results) from `State`
and the instruction stepper (`execInstr`) from `Exec`. Other modules in the runtime
stack (scheduler, adequacy, program logic) should import this rather than reaching
into individual files.
-/

set_option autoImplicit false
