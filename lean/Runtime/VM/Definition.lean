import Runtime.VM.State
import Runtime.VM.Exec

/-
The Problem. Provide a single import point for VM state and instruction
semantics used across the runtime stack.

Solution Structure. Re-export state definitions and the exec stepper from
`Runtime.VM.State` and `Runtime.VM.Exec`.
-/

set_option autoImplicit false
