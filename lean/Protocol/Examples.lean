import Protocol.Deployment

/-!
# Examples (Minimal)

This module is currently minimal to keep the Protocol build green while
example proofs are refactored.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

-- Minimal theorem to keep the module non-empty while examples are refactored.
theorem examples_trivial : True := trivial
