import Runtime.VM.Definition
import Runtime.Shim.WeakestPre

/-!
# Task 12: Language Instance

Instantiate the Iris `Language` typeclass for the bytecode VM.
Connects VM execution to Iris program logic.

## Definitions

- `SessionVM` — the language tag
- `instance : Language SessionVM`
- `to_val` / `of_val` / `prim_step`
- `LanguageMixin` proofs

Dependencies: Task 11, Shim.WeakestPre.
-/

set_option autoImplicit false

-- TODO: implement Task 12
