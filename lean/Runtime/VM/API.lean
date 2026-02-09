import Runtime.VM.Model.State
import Runtime.VM.Semantics.Exec

/-!
# VM Definition (Re-exports)

Single import point for the VM specification. Importing this file gives access to
the full runtime state (`VMState`, `CoroutineState`, events, results) from `State`
and the instruction stepper (`execInstr`) from `Exec`. Other modules in the runtime
stack (scheduler, adequacy, program logic) should import this rather than reaching
into individual files.
-/

set_option autoImplicit false
