import Classical.Transport
import Consensus.Classifier

set_option autoImplicit false

/-! # Consensus.ClassicalValidation

Assumption-profile checks for using theorem families exposed by
`Classical.Transport`.
-/

namespace Consensus

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

/-- Validation result for one classical property request. -/
structure ClassicalValidationResult where
  property : ClassicalProperty
  theoremName : String
  passed : Bool
  missing : List ClassicalAssumption
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Canonical theorem name for each classical property family. -/
def theoremFor (p : ClassicalProperty) : String :=
  match p with
  | .fosterLyapunov => "Classical.Transport.transported_fosterLyapunov"
  | .maxWeight => "Classical.Transport.transported_maxWeight"
  | .largeDeviation => "Classical.Transport.transported_ldp"
  | .meanField => "Classical.Transport.transported_meanField"
  | .heavyTraffic => "Classical.Transport.transported_heavyTraffic"
  | .mixingTime => "Classical.Transport.transported_mixing"
  | .fluidLimit => "Classical.Transport.transported_fluidLimit"
  | .concentration => "Classical.Transport.transported_concentration"
  | .littlesLaw => "Classical.Transport.transported_littlesLaw"
  | .functionalCLT => "Classical.Transport.transported_functionalCLT"
  | .spectralGapTermination => "Classical.SpectralGapTermination.expected_termination_bound"

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
  , theoremName := theoremFor p
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

end Consensus
