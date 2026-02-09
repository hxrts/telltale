import Consensus.FLP.Hypotheses

set_option autoImplicit false

/-! # Consensus.FLP.Api

High-level API for automatic FLP lower-bound certification.

When a protocol instance is built with the reusable FLP hypotheses and the
standard lower-bound premises, the FLP non-termination witness theorem is
materialized automatically.
-/

namespace Consensus
namespace FLP

universe u v w x

/-- A protocol packaged for FLP lower-bound certification.

`lowerBound` has a default proof term, so users only provide model assumptions
and valency-style premises; the theorem is derived automatically. -/
structure Protocol where
  State : Type u
  Value : Type v
  Event : Type w
  Party : Type x
  model : Model State Value Event Party
  assumptions : Assumptions model
  premises : LowerBoundPremises model
  lowerBound :
    ∃ run, premises.FairRun run ∧ ∀ n, premises.Uncommitted (run n) :=
      lowerBound_of_hypotheses assumptions premises

/-- Stronger protocol package: includes premises sufficient to derive
the full FLP impossibility (negation of universal fair-run termination). -/
structure FullProtocol where
  State : Type u
  Value : Type v
  Event : Type w
  Party : Type x
  model : Model State Value Event Party
  assumptions : Assumptions model
  premises : ImpossibilityPremises model
  lowerBound :
    ∃ run, premises.FairRun run ∧ ∀ n, premises.Uncommitted (run n) :=
      lowerBound_of_hypotheses assumptions premises.toLowerBoundPremises
  impossibility :
    ¬ TerminatesOnAllFairRuns model premises.FairRun :=
      impossibility_of_hypotheses assumptions premises

/-- Extract the FLP lower-bound theorem from a certified protocol bundle. -/
theorem lowerBound_of_protocol (P : Protocol) :
    ∃ run, P.premises.FairRun run ∧ ∀ n, P.premises.Uncommitted (run n) :=
  P.lowerBound

/-- Extract the full FLP impossibility theorem from a full protocol bundle. -/
theorem impossibility_of_protocol (P : FullProtocol) :
    ¬ TerminatesOnAllFairRuns P.model P.premises.FairRun :=
  P.impossibility

/-- Runtime-style certificate object for downstream APIs. -/
structure LowerBoundCertificate (P : Protocol) where
  run : Nat → P.State
  fair : P.premises.FairRun run
  uncommitted : ∀ n, P.premises.Uncommitted (run n)

/-- Materialize an explicit certificate from a certified protocol bundle. -/
noncomputable def certify (P : Protocol) : LowerBoundCertificate P := by
  classical
  refine ⟨Classical.choose P.lowerBound, ?_, ?_⟩
  · exact (Classical.choose_spec P.lowerBound).1
  · exact (Classical.choose_spec P.lowerBound).2

/-- FLP core assumptions are always validated for a certified protocol. -/
theorem coreHypotheses_allPassed (P : Protocol) :
    (runValidation P.assumptions coreHypotheses).2 = true := by
  rfl

/-- FLP core assumptions are always validated for a certified full protocol. -/
theorem coreHypotheses_allPassed_full (P : FullProtocol) :
    (runValidation P.assumptions coreHypotheses).2 = true := by
  rfl

end FLP
end Consensus
