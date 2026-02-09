import Distributed.Model.Assumptions
import Distributed.Transport.Context

set_option autoImplicit false

/-! # Distributed.Transport.Contracts

Transport-level summary contracts for consensus-family validation.
-/

namespace Distributed

/-- Summary of assumption validation for one protocol spec. -/
structure AssumptionSummary where
  space : ProtocolSpace
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- True iff every classical-property validation passed. -/
def allClassicalPassed (rs : List ClassicalValidationResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Combined summary over consensus assumptions and classical-property checks. -/
structure CombinedSummary where
  consensus : AssumptionSummary
  classical : List ClassicalValidationResult
  classicalAllPassed : Bool
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

end Distributed

