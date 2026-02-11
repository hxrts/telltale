import Distributed.Families.FLP.Core

set_option autoImplicit false

/-! # Distributed.Families.FLP.API

High-level API for automatic FLP lower-bound certification.

When a protocol instance is built with the reusable FLP hypotheses and the
standard lower-bound premises, the FLP non-termination witness theorem is
materialized automatically.
-/

namespace Distributed
namespace FLP

universe u v w x

/-- A protocol packaged for FLP lower-bound certification.

`lowerBound` has a default proof term, so users only provide model assumptions
and valency-style premises; the theorem is derived automatically. -/
structure LowerBoundProtocol where
  State : Type u
  Value : Type v
  Event : Type w
  Party : Type x
  model : Model State Value Event Party
  assumptions : Assumptions model
  premises : LowerBoundPremises model
  lowerBound :
    ∃ run, premises.FairRun run ∧ ∀ n, premises.Uncommitted (run n) :=
      lowerBound_of_assumptions assumptions premises

/-- Stronger protocol package: includes premises sufficient to derive
the full FLP impossibility (negation of universal fair-run termination). -/
structure ImpossibilityProtocol where
  State : Type u
  Value : Type v
  Event : Type w
  Party : Type x
  model : Model State Value Event Party
  assumptions : Assumptions model
  premises : ImpossibilityPremises model
  lowerBound :
    ∃ run, premises.FairRun run ∧ ∀ n, premises.Uncommitted (run n) :=
      lowerBound_of_assumptions assumptions premises.toLowerBoundPremises
  impossibility :
    ¬ TerminatesOnAllFairRuns model premises.FairRun :=
      impossibility_of_assumptions assumptions premises

/-- Extract the FLP lower-bound theorem from a certified protocol bundle. -/
theorem lowerBound_of_protocol (P : LowerBoundProtocol) :
    ∃ run, P.premises.FairRun run ∧ ∀ n, P.premises.Uncommitted (run n) :=
  P.lowerBound

/-- Extract the full FLP impossibility theorem from a full protocol bundle. -/
theorem impossibility_of_protocol (P : ImpossibilityProtocol) :
    ¬ TerminatesOnAllFairRuns P.model P.premises.FairRun :=
  P.impossibility

/-- Runtime-style certificate object for downstream APIs. -/
structure LowerBoundCertificate (P : LowerBoundProtocol) where
  run : Nat → P.State
  fair : P.premises.FairRun run
  uncommitted : ∀ n, P.premises.Uncommitted (run n)

/-- Materialize a certificate witness from a certified protocol bundle. -/
theorem certify (P : LowerBoundProtocol) : Nonempty (LowerBoundCertificate P) := by
  classical
  refine ⟨⟨Classical.choose P.lowerBound, ?_, ?_⟩⟩
  · exact (Classical.choose_spec P.lowerBound).1
  · exact (Classical.choose_spec P.lowerBound).2

/-- FLP core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : LowerBoundProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

/-- FLP core assumptions are always validated for a certified full protocol. -/
theorem coreAssumptions_allPassed_impossibility (P : ImpossibilityProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end FLP
end Distributed
