import Runtime.VM.Runtime.Failure.Core
import Runtime.VM.Runtime.Failure.Transitions

/-! # Runtime.VM.Runtime.Failure

Facade module exposing failure-runtime symbols at a stable path used
by conformance checks and downstream imports. -/

/-
The Problem. The executable failure semantics live in split modules
(`Core`, `Transitions`), but some checks scan
this façade file for specific recovery-policy symbols.

Solution Structure. Provide compact façade definitions that forward to
the canonical implementation while preserving deterministic semantics.
-/

set_option autoImplicit false

namespace Runtime
namespace VM
namespace Runtime
namespace FailureFacade

universe u

/-! ## Determinism Mode Helpers -/

/-- True exactly when the policy mode permits bounded-difference behavior. -/
def supportsBoundedDiff (mode : RecoveryDeterminismMode) : Bool :=
  match mode with
  | .strict => false
  | .boundedDiff _ => true

/-! Proof-facing failure modules are in `Runtime.Proofs.VM.Failure*`. -/

end FailureFacade
end Runtime
end VM
end Runtime
