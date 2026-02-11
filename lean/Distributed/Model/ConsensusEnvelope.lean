import Distributed.Model.Assumptions

set_option autoImplicit false

/-! # Distributed.Model.ConsensusEnvelope

Consensus envelope forms that reuse `ProtocolSpec` classification and assumption
validation from `Distributed.Model`.
-/

/-
The Problem. Consensus-family theorem artifacts need a uniform envelope surface
for soundness/completeness/maximality, compositional committee bounds, and
interactive-distance (`d_int`) interfaces without duplicating model glue.

Solution Structure. We introduce core envelope forms first, then committee/shard
composition bounds, then `d_int` bounds and theorem-object packaging, and finally
admission/capability extraction wrappers over the existing assumption validator.
-/

namespace Distributed
namespace ConsensusEnvelope

universe u v

/-! ## Core Envelope Forms -/

/-- Canonical run type used in consensus envelope statements. -/
abbrev Run (State : Type u) := Nat → State

/-- Safety-visible observation for consensus state. -/
def Obs_consensus
    {State : Type u} {Obs : Type v}
    (observe : State → Obs) (s : State) : Obs :=
  observe s

/-- Safety-visible observational equivalence for consensus states. -/
def Eq_safe_consensus
    {State : Type u} {Obs : Type v}
    (observe : State → Obs) (s₁ s₂ : State) : Prop :=
  Obs_consensus observe s₁ = Obs_consensus observe s₂

/-- Envelope relation for one reference/deployed consensus run pair. -/
def Envelope_consensus
    {State : Type u} {Obs : Type v}
    (observe : State → Obs)
    (ref impl : Run State) : Prop :=
  ∀ n, Eq_safe_consensus observe (ref n) (impl n)

/-- Soundness half: admitted implementations stay inside the consensus envelope. -/
def EnvelopeSoundness_consensus
    {State : Type u} {Obs : Type v}
    (observe : State → Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → ImplRun impl → Envelope_consensus observe ref impl

/-- Realizability/completeness half: every envelope-admitted diff is realizable. -/
def EnvelopeRealizability_consensus
    {State : Type u} {Obs : Type v}
    (observe : State → Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → Envelope_consensus observe ref impl → ImplRun impl

/-- Relative maximality for consensus envelope relations. -/
def EnvelopeMaximality_consensus
    {State : Type u} {Obs : Type v}
    (observe : State → Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ R : Run State → Run State → Prop,
    (∀ ref impl, RefRun ref → ImplRun impl → R ref impl →
      ∀ n, Eq_safe_consensus observe (ref n) (impl n)) →
      (∀ ref impl, RefRun ref → ImplRun impl → R ref impl →
        Envelope_consensus observe ref impl)

/-- Exact characterization theorem form for `Envelope_consensus`. -/
def ExactEnvelopeCharacterization_consensus
    {State : Type u} {Obs : Type v}
    (observe : State → Obs)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  EnvelopeSoundness_consensus observe RefRun ImplRun ∧
  EnvelopeRealizability_consensus observe RefRun ImplRun ∧
  EnvelopeMaximality_consensus observe RefRun ImplRun

/-- Abstract-vs-runtime adequacy modulo the consensus envelope. -/
def ObservationalAdequacyModuloEnvelope_consensus
    {State : Type u} {Obs : Type v}
    (observe : State → Obs)
    (AbstractRun RuntimeRun : Run State → Prop) : Prop :=
  ∀ abs rt, AbstractRun abs → RuntimeRun rt → Envelope_consensus observe abs rt

/-- Consensus-family eligibility based on existing protocol-space classifier. -/
def consensusFamilyAdmissible (p : ProtocolSpec) : Bool :=
  inBFTSpace p || inNakamotoSpace p || inHybridSpace p

/-- Core consensus assumptions passed under the existing model validator. -/
def consensusCoreAssumptionsPassed (p : ProtocolSpec) : Bool :=
  (runAssumptionValidation p coreAssumptions).allPassed

/-- Capability budget domain for consensus profile admission checks. -/
abbrev DiffBudget := Nat

/-- Committee/shard identifier used in compositional consensus theorems. -/
abbrev CommitteeId := Nat

/-! ## Compositional Committee Bounds -/

/-- Per-committee envelope-bound function. -/
abbrev CommitteeEnvelopeBound {State : Type u} :=
  CommitteeId → Run State → Run State → DiffBudget

/-- Cross-committee interaction-bound function. -/
abbrev CrossCommitteeEnvelopeBound {State : Type u} :=
  CommitteeId → CommitteeId → Run State → Run State → DiffBudget

/-- Recursive sum of per-committee envelope bounds over a committee list. -/
def committeeBoundSum
    {State : Type u}
    (committees : List CommitteeId)
    (component : CommitteeEnvelopeBound (State := State))
    (ref impl : Run State) : DiffBudget :=
  match committees with
  | [] => 0
  | c :: cs => component c ref impl + committeeBoundSum cs component ref impl

/-- Recursive sum of cross-committee interaction bounds over listed pairs. -/
def crossCommitteeBoundSum
    {State : Type u}
    (pairs : List (CommitteeId × CommitteeId))
    (interaction : CrossCommitteeEnvelopeBound (State := State))
    (ref impl : Run State) : DiffBudget :=
  match pairs with
  | [] => 0
  | pair :: rest =>
      interaction pair.1 pair.2 ref impl +
        crossCommitteeBoundSum rest interaction ref impl

/-- Every listed cross-committee pair references distinct committees. -/
def CrossCommitteePairsWellFormed
    (pairs : List (CommitteeId × CommitteeId)) : Prop :=
  ∀ pair, pair ∈ pairs → pair.1 ≠ pair.2

/-- Explicit non-interference assumption: distinct committees have zero interaction term. -/
def CrossCommitteeNonInterference
    {State : Type u}
    (interaction : CrossCommitteeEnvelopeBound (State := State)) : Prop :=
  ∀ c₁ c₂, c₁ ≠ c₂ → ∀ ref impl, interaction c₁ c₂ ref impl = 0

/-- Global composition law: total envelope budget = component budgets + interaction term. -/
def CompositionalEnvelopeBound_consensus
    {State : Type u}
    (committees : List CommitteeId)
    (pairs : List (CommitteeId × CommitteeId))
    (component : CommitteeEnvelopeBound (State := State))
    (interaction : CrossCommitteeEnvelopeBound (State := State))
    (total : Run State → Run State → DiffBudget) : Prop :=
  ∀ ref impl,
    total ref impl =
      committeeBoundSum committees component ref impl +
        crossCommitteeBoundSum pairs interaction ref impl

/-- Cross-committee interaction sum collapses to zero under explicit non-interference. -/
theorem crossCommitteeBoundSum_eq_zero_of_nonInterference
    {State : Type u}
    (pairs : List (CommitteeId × CommitteeId))
    (interaction : CrossCommitteeEnvelopeBound (State := State))
    (hPairs : CrossCommitteePairsWellFormed pairs)
    (hNI : CrossCommitteeNonInterference interaction)
    (ref impl : Run State) :
    crossCommitteeBoundSum pairs interaction ref impl = 0 := by
  induction pairs with
  | nil =>
      simp [crossCommitteeBoundSum]
  | cons pair rest ih =>
      have hPairNe : pair.1 ≠ pair.2 := hPairs pair (by simp)
      have hHeadZero : interaction pair.1 pair.2 ref impl = 0 :=
        hNI pair.1 pair.2 hPairNe ref impl
      have hRestPairs : CrossCommitteePairsWellFormed rest := by
        intro pair' hMem
        exact hPairs pair' (by simp [hMem])
      have hTailZero : crossCommitteeBoundSum rest interaction ref impl = 0 :=
        ih hRestPairs
      simp [crossCommitteeBoundSum, hHeadZero, hTailZero]

/-- Compositional exactness under explicit cross-committee/shard non-interference. -/
theorem compositionalExactness_under_nonInterference_consensus
    {State : Type u}
    (committees : List CommitteeId)
    (pairs : List (CommitteeId × CommitteeId))
    (component : CommitteeEnvelopeBound (State := State))
    (interaction : CrossCommitteeEnvelopeBound (State := State))
    (total : Run State → Run State → DiffBudget)
    (hComp :
      CompositionalEnvelopeBound_consensus committees pairs component interaction total)
    (hPairs : CrossCommitteePairsWellFormed pairs)
    (hNI : CrossCommitteeNonInterference interaction) :
    ∀ ref impl,
      total ref impl = committeeBoundSum committees component ref impl := by
  intro ref impl
  have hInteractionZero :
      crossCommitteeBoundSum pairs interaction ref impl = 0 :=
    crossCommitteeBoundSum_eq_zero_of_nonInterference pairs interaction hPairs hNI ref impl
  have hTotal := hComp ref impl
  simpa [hInteractionZero] using hTotal

/-- Representative consensus families for `d_int` theorem-object bounds. -/
inductive ConsensusModelClass where
  | quorum
  | work
  | coupled
  deriving Repr, DecidableEq, Inhabited

/-- Canonical representative family class inferred from the protocol certificate tag. -/
def consensusModelClassOf (p : ProtocolSpec) : ConsensusModelClass :=
  match p.certificate with
  | .quorum => .quorum
  | .work => .work
  | .hybrid => .coupled

/-- Lower bound candidate for interactive distance (`d_int`) by family class. -/
def dIntLowerBound (p : ProtocolSpec) : DiffBudget :=
  match consensusModelClassOf p with
  | .quorum => p.f + 1
  | .work => p.adversarialWeightPermille + 1
  | .coupled => p.f + p.adversarialWeightPermille + 1

/-- Upper bound candidate for interactive distance (`d_int`) by family class. -/
def dIntUpperBound (p : ProtocolSpec) : DiffBudget :=
  match consensusModelClassOf p with
  | .quorum => p.n + (p.f + 1)
  | .work => p.n + (p.adversarialWeightPermille + 1)
  | .coupled => p.n + (p.f + p.adversarialWeightPermille + 1)

/-- `d_int` lower/upper-bound theorem object for a fixed protocol instance. -/
structure DIntTheoremObject (protocol : ProtocolSpec) where
  modelClass : ConsensusModelClass := consensusModelClassOf protocol
  lower : DiffBudget := dIntLowerBound protocol
  upper : DiffBudget := dIntUpperBound protocol
  lowerLEUpper : lower ≤ upper
  declared : protocol.interactiveDistanceDeclared = true

/-- Generic lower<=upper bound proof for `d_int` representatives. -/
theorem dIntLower_le_dIntUpper (p : ProtocolSpec) :
    dIntLowerBound p ≤ dIntUpperBound p := by
  cases hClass : consensusModelClassOf p <;>
    simp [dIntLowerBound, dIntUpperBound, hClass, Nat.le_add_left]

/-- Canonical constructor for `d_int` theorem objects from declared protocol models. -/
def mkDIntTheoremObject
    (p : ProtocolSpec)
    (hDeclared : p.interactiveDistanceDeclared = true) :
    DIntTheoremObject p where
  modelClass := consensusModelClassOf p
  lower := dIntLowerBound p
  upper := dIntUpperBound p
  lowerLEUpper := dIntLower_le_dIntUpper p
  declared := hDeclared

/-- Representative class theorem: quorum model `d_int` bounds. -/
theorem dIntBounds_quorum
    (p : ProtocolSpec)
    (hCert : p.certificate = .quorum) :
    dIntLowerBound p = p.f + 1 ∧ dIntUpperBound p = p.n + (p.f + 1) := by
  simp [dIntLowerBound, dIntUpperBound, consensusModelClassOf, hCert]

/-- Representative class theorem: work model `d_int` bounds. -/
theorem dIntBounds_work
    (p : ProtocolSpec)
    (hCert : p.certificate = .work) :
    dIntLowerBound p = p.adversarialWeightPermille + 1 ∧
    dIntUpperBound p = p.n + (p.adversarialWeightPermille + 1) := by
  simp [dIntLowerBound, dIntUpperBound, consensusModelClassOf, hCert]

/-- Representative class theorem: coupled model `d_int` bounds. -/
theorem dIntBounds_coupled
    (p : ProtocolSpec)
    (hCert : p.certificate = .hybrid) :
    dIntLowerBound p = p.f + p.adversarialWeightPermille + 1 ∧
    dIntUpperBound p = p.n + (p.f + p.adversarialWeightPermille + 1) := by
  simp [dIntLowerBound, dIntUpperBound, consensusModelClassOf, hCert]

/-- Admissibility relation induced by a consensus envelope budget. -/
def CapabilityAdmissible_consensus (envelopeBudget : DiffBudget) (d : DiffBudget) : Prop :=
  d ≤ envelopeBudget

/-- Principal-capability theorem form for consensus profile inference. -/
def PrincipalCapability_consensus
    (dProg envelopeBudget : DiffBudget) : Prop :=
  dProg = envelopeBudget

/-- Admission soundness theorem form for consensus profile inference. -/
def AdmissionSoundness_consensus
    (dProg envelopeBudget : DiffBudget) : Prop :=
  ∀ dUser, dUser ≤ dProg → CapabilityAdmissible_consensus envelopeBudget dUser

/-- Admission completeness theorem form for consensus profile inference. -/
def AdmissionCompleteness_consensus
    (dProg envelopeBudget : DiffBudget) : Prop :=
  ∀ dUser, dUser ≤ dProg ↔ CapabilityAdmissible_consensus envelopeBudget dUser

/-- Capability floor associated with each consensus protocol-space class. -/
def capabilityForSpace : ProtocolSpace → DiffBudget
  | .outside => 0
  | .nakamoto => 1
  | .bft => 2
  | .hybrid => 3

/-- Canonical capability inferred from the existing classifier. -/
def inferConsensusCapability (p : ProtocolSpec) : DiffBudget :=
  capabilityForSpace (classify p)

/-- Principal-capability theorem for consensus profile inference. -/
theorem principalCapability_inferred_consensus (p : ProtocolSpec) :
    PrincipalCapability_consensus (inferConsensusCapability p) (capabilityForSpace (classify p)) := by
  rfl

/-- Admission soundness for canonical consensus capability inference. -/
theorem admissionSoundness_inferred_consensus (p : ProtocolSpec) :
    AdmissionSoundness_consensus (inferConsensusCapability p) (capabilityForSpace (classify p)) := by
  intro dUser hLe
  exact hLe

/-- Admission completeness for canonical consensus capability inference. -/
theorem admissionCompleteness_inferred_consensus (p : ProtocolSpec) :
    AdmissionCompleteness_consensus (inferConsensusCapability p) (capabilityForSpace (classify p)) := by
  intro dUser
  constructor
  · intro hLe
    exact hLe
  · intro hAdmit
    exact hAdmit

/-- Premises for consensus envelope statements over an existing `ProtocolSpec`. -/
structure Premises
    {State : Type u} {Obs : Type v}
    (observe : State → Obs) : Type (max u v) where
  protocol : ProtocolSpec
  dIntTheorem : DIntTheoremObject protocol
  familyAdmissible : consensusFamilyAdmissible protocol = true
  coreAssumptionsPassed : consensusCoreAssumptionsPassed protocol = true
  RefRun : Run State → Prop
  ImplRun : Run State → Prop
  adequacyWitness :
    ObservationalAdequacyModuloEnvelope_consensus observe RefRun ImplRun
  envelopeBudget : DiffBudget
  inferredBudget : DiffBudget
  principalCapabilityWitness :
    PrincipalCapability_consensus inferredBudget envelopeBudget
  admissionSoundnessWitness :
    AdmissionSoundness_consensus inferredBudget envelopeBudget
  admissionCompletenessWitness :
    AdmissionCompleteness_consensus inferredBudget envelopeBudget
  envelopeSoundnessWitness :
    EnvelopeSoundness_consensus observe RefRun ImplRun
  envelopeRealizabilityWitness :
    EnvelopeRealizability_consensus observe RefRun ImplRun
  envelopeMaximalityWitness :
    EnvelopeMaximality_consensus observe RefRun ImplRun

/-- Exact envelope characterization follows from protocol-aligned premises. -/
theorem exactEnvelope_consensus_of_premises
    {State : Type u} {Obs : Type v}
    {observe : State → Obs}
    (p : Premises observe) :
    ExactEnvelopeCharacterization_consensus observe p.RefRun p.ImplRun := by
  exact ⟨p.envelopeSoundnessWitness, p.envelopeRealizabilityWitness, p.envelopeMaximalityWitness⟩

/-- Observational adequacy follows directly from consensus envelope premises. -/
theorem adequacy_consensus_of_premises
    {State : Type u} {Obs : Type v}
    {observe : State → Obs}
    (p : Premises observe) :
    ObservationalAdequacyModuloEnvelope_consensus observe p.RefRun p.ImplRun :=
  p.adequacyWitness

/-- `d_int` lower/upper bound witness extraction from consensus premises. -/
theorem dIntBounds_of_premises
    {State : Type u} {Obs : Type v}
    {observe : State → Obs}
    (p : Premises observe) :
    p.dIntTheorem.lower ≤ p.dIntTheorem.upper :=
  p.dIntTheorem.lowerLEUpper

/-- Certified consensus-envelope package tied to `Distributed.Model` validation. -/
structure ConsensusEnvelopeProtocol where
  State : Type u
  Obs : Type v
  observe : State → Obs
  premises : Premises observe
  exactEnvelope :
    ExactEnvelopeCharacterization_consensus observe premises.RefRun premises.ImplRun :=
      exactEnvelope_consensus_of_premises premises
  adequacy :
    ObservationalAdequacyModuloEnvelope_consensus observe premises.RefRun premises.ImplRun :=
      adequacy_consensus_of_premises premises
  principalCapability :
    PrincipalCapability_consensus premises.inferredBudget premises.envelopeBudget :=
      premises.principalCapabilityWitness
  admissionSoundness :
    AdmissionSoundness_consensus premises.inferredBudget premises.envelopeBudget :=
      premises.admissionSoundnessWitness
  admissionCompleteness :
    AdmissionCompleteness_consensus premises.inferredBudget premises.envelopeBudget :=
      premises.admissionCompletenessWitness
  dIntBounds :
    premises.dIntTheorem.lower ≤ premises.dIntTheorem.upper :=
      dIntBounds_of_premises premises

end ConsensusEnvelope
end Distributed
