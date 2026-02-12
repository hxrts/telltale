import Runtime.Adequacy.EnvelopeCore.CoreFoundations
import Runtime.Adequacy.EnvelopeCore.ReconfigurationBridge
import Runtime.Adequacy.EnvelopeCore.VMAdherence
import Runtime.Adequacy.EnvelopeCore.AdmissionLogic
import Runtime.Adequacy.EnvelopeCore.FailureTaxonomy

/-! # Runtime.Adequacy.EnvelopeCore

Facade module exposing envelope/failure theorem names at a stable
import path consumed by conformance tooling. -/

/-
The Problem. Core failure-taxonomy and envelope definitions are split
across submodules, while CI checks look for key names in this façade.

Solution Structure. Provide small façade aliases and wrapper records
that point to canonical definitions without duplicating logic.
-/

set_option autoImplicit false

namespace Runtime
namespace Adequacy
namespace EnvelopeCoreFacade

/-! ## Failure Mapping Aliases -/

/-- Facade alias for Rust fault-tag classification. -/
def failureClassOfRustFaultTag :=
  Runtime.Adequacy.failureClassOfRustFaultTag

/-- Facade alias for Rust fault-tag to stable error code mapping. -/
def errorCodeOfRustFaultTag :=
  Runtime.Adequacy.errorCodeOfRustFaultTag

/-! ## Failure Theorem Aliases -/

/-- Facade alias for cross-target failure-visible conformance theorem family. -/
def CrossTargetFailureConformance :=
  @Runtime.Adequacy.CrossTargetFailureConformance

/-- Facade alias for restart-refinement structured-error adequacy family. -/
def RestartRefinementStructuredErrorAdequacy :=
  @Runtime.Adequacy.RestartRefinementStructuredErrorAdequacy

/-! ## Failure Protocol View -/

/-- Facade wrapper exposing the canonical failure-envelope protocol package. -/
structure FailureEnvelopeProtocol where
  core : Runtime.Adequacy.FailureEnvelopeProtocol

end EnvelopeCoreFacade
end Adequacy
end Runtime
