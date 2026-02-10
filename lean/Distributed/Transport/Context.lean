import Distributed.Model.Classifier

set_option autoImplicit false

/-! # Distributed.Transport.Context

Assumption-profile checks for transported theorem families.

This module is intentionally decoupled from `Classical` implementation details:
it tracks family-level eligibility labels only. Cross-family proof composition
is performed in Runtime/VM proof layers.
-/

/-
The Problem. Classical theorem families (Foster-Lyapunov, large deviations, mixing times)
require specific assumptions to apply. We need to check whether a protocol configuration
satisfies the preconditions for each family.

Solution Structure. We define:
1. `ClassicalProperty`: enumeration of transportable theorem families
2. `ClassicalAssumption`: atoms required by each family
3. Profile-checking functions that validate family eligibility
This enables safe theorem transport with explicit assumption tracking.
-/

/-! ## Core Development -/

namespace Distributed

/-- Classical theorem families available through the transport layer. -/
inductive ClassicalProperty where
  | fosterLyapunov
  | maxWeight
  | largeDeviation
  | meanField
  | heavyTraffic
  | mixingTime
  | fluidLimit
  | concentration
  | littlesLaw
  | functionalCLT
  | spectralGapTermination
  deriving Repr, DecidableEq, Inhabited

/-- Assumption atoms used by coarse classical-property validation. -/
inductive ClassicalAssumption where
  | finiteState
  | coherentInvariant
  | harmonyCommutation
  | markovAbstraction
  | driftWitness
  | schedulerOptimality
  | exponentialTailWitness
  | exchangeability
  | heavyTrafficScaling
  | mixingWitness
  | fluidDescentWitness
  | boundedIncrementWitness
  | queueRateWaitInputs
  | cltMomentWitness
  | spectralGapPos
  deriving Repr, DecidableEq, Inhabited

/-- User-supplied evidence profile for classical transport checks. -/
structure ClassicalEvidence where
  finiteState : Bool := false
  coherentInvariant : Bool := false
  harmonyCommutation : Bool := false
  markovAbstraction : Bool := false
  driftWitness : Bool := false
  schedulerOptimality : Bool := false
  exponentialTailWitness : Bool := false
  exchangeability : Bool := false
  heavyTrafficScaling : Bool := false
  mixingWitness : Bool := false
  fluidDescentWitness : Bool := false
  boundedIncrementWitness : Bool := false
  queueRateWaitInputs : Bool := false
  cltMomentWitness : Bool := false
  spectralGapPos : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one transported-property request. -/
structure ClassicalValidationResult where
  property : ClassicalProperty
  familyId : String
  passed : Bool
  missing : List ClassicalAssumption
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Canonical family identifier for each transported property family. -/
def familyIdFor (p : ClassicalProperty) : String :=
  match p with
  | .fosterLyapunov => "foster_lyapunov"
  | .maxWeight => "max_weight"
  | .largeDeviation => "large_deviation"
  | .meanField => "mean_field"
  | .heavyTraffic => "heavy_traffic"
  | .mixingTime => "mixing_time"
  | .fluidLimit => "fluid_limit"
  | .concentration => "concentration"
  | .littlesLaw => "littles_law"
  | .functionalCLT => "functional_clt"
  | .spectralGapTermination => "spectral_gap_termination"

/-- Required assumption profile per classical property family. -/
def assumptionsFor (p : ClassicalProperty) : List ClassicalAssumption :=
  let base := [ClassicalAssumption.finiteState, .coherentInvariant, .harmonyCommutation]
  match p with
  | .fosterLyapunov =>
      base ++ [.markovAbstraction, .driftWitness]
  | .maxWeight =>
      base ++ [.schedulerOptimality]
  | .largeDeviation =>
      base ++ [.markovAbstraction, .exponentialTailWitness]
  | .meanField =>
      base ++ [.exchangeability]
  | .heavyTraffic =>
      base ++ [.markovAbstraction, .heavyTrafficScaling]
  | .mixingTime =>
      base ++ [.markovAbstraction, .mixingWitness]
  | .fluidLimit =>
      base ++ [.fluidDescentWitness]
  | .concentration =>
      base ++ [.boundedIncrementWitness]
  | .littlesLaw =>
      base ++ [.queueRateWaitInputs]
  | .functionalCLT =>
      base ++ [.markovAbstraction, .cltMomentWitness]
  | .spectralGapTermination =>
      base ++ [.markovAbstraction, .spectralGapPos]

/-- Check whether one assumption atom is present in the evidence profile. -/
def hasAssumption (ev : ClassicalEvidence) (a : ClassicalAssumption) : Bool :=
  match a with
  | .finiteState => ev.finiteState
  | .coherentInvariant => ev.coherentInvariant
  | .harmonyCommutation => ev.harmonyCommutation
  | .markovAbstraction => ev.markovAbstraction
  | .driftWitness => ev.driftWitness
  | .schedulerOptimality => ev.schedulerOptimality
  | .exponentialTailWitness => ev.exponentialTailWitness
  | .exchangeability => ev.exchangeability
  | .heavyTrafficScaling => ev.heavyTrafficScaling
  | .mixingWitness => ev.mixingWitness
  | .fluidDescentWitness => ev.fluidDescentWitness
  | .boundedIncrementWitness => ev.boundedIncrementWitness
  | .queueRateWaitInputs => ev.queueRateWaitInputs
  | .cltMomentWitness => ev.cltMomentWitness
  | .spectralGapPos => ev.spectralGapPos

/-- Assumption atoms still missing for a requested property. -/
def missingAssumptions (ev : ClassicalEvidence) (p : ClassicalProperty) :
    List ClassicalAssumption :=
  (assumptionsFor p).filter (fun a => !(hasAssumption ev a))

/-- Coarse eligibility check for using classical transport machinery. -/
def validateClassicalProperty (spec : ProtocolSpec) (ev : ClassicalEvidence)
    (p : ClassicalProperty) : ClassicalValidationResult :=
  let missing := missingAssumptions ev p
  let passed := isSoundConsensus spec && missing.isEmpty
  let detail :=
    if !isSoundConsensus spec then
      "Protocol spec is outside supported consensus spaces."
    else if missing.isEmpty then
      "All required assumptions satisfied."
    else
      "Missing required assumptions for requested classical property."
  { property := p
  , familyId := familyIdFor p
  , passed := passed
  , missing := missing
  , detail := detail
  }

/-- Validate a batch of classical properties. -/
def validateClassicalProperties (spec : ProtocolSpec) (ev : ClassicalEvidence)
    (ps : List ClassicalProperty) : List ClassicalValidationResult :=
  ps.map (validateClassicalProperty spec ev)

/-- Default classical property set used for broad capability checks. -/
def classicalCoreProperties : List ClassicalProperty :=
  [ .fosterLyapunov
  , .mixingTime
  , .largeDeviation
  , .littlesLaw
  , .spectralGapTermination
  ]

end Distributed
