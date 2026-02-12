import Distributed.Model.Assumptions
import Distributed.Model.Classifier
import Distributed.Families.QuorumGeometry
import Distributed.Families.AccountableSafety
import Distributed.Families.AtomicBroadcast
import Distributed.Families.Nakamoto

set_option autoImplicit false

/-! # Distributed.Families.ByzantineSafety

Reusable Byzantine-safety characterization forms and specialization bridges.
-/

/-
The Problem. Crash-stop exactness is not enough for the stronger distributed
story: we need a scoped Byzantine safety characterization with explicit
assumptions, converse direction, and packaging hooks for envelope/capability
layers.

Solution Structure. Define the core Byzantine observation/envelope interfaces,
state the exact-characterization form (soundness + completeness + maximality),
and provide specialization bridges into existing quorum/accountability/
atomic-broadcast families.
-/

/-! ## Core Development -/

namespace Distributed
namespace ByzantineSafety

universe u v w x

/-- Canonical run type for Byzantine safety/equivalence statements. -/
abbrev Run (State : Type u) := Nat → State

/-! ## Determinism and Diff Policies -/

/-- Determinism profiles used by Byzantine admission and envelope contracts. -/
inductive DeterminismProfile where
  | full
  | traceModulo
  | commutativityModulo
  deriving Repr, DecidableEq, Inhabited

/-- User-facing diff policy for Byzantine envelope admission. -/
inductive DiffPolicy where
  | fullDeterminism
  | boundedDiff (budget : Nat)
  deriving Repr, DecidableEq, Inhabited

/-! ## Event and Evidence Vocabulary -/

/-- Byzantine environment events visible to the abstract model. -/
inductive ByzantineEvent where
  | equivocation
  | withholding
  | delay
  | reorder
  | invalidAuth
  deriving Repr, DecidableEq, Inhabited

/-- Structured Byzantine evidence payload used by counterexample packaging. -/
structure ByzantineEvidence where
  eventId : Nat
  classTag : String
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Deterministic event-class mapping used by normalization and traces. -/
def eventClass : ByzantineEvent → String
  | .equivocation => "equivocation"
  | .withholding => "withholding"
  | .delay => "delay"
  | .reorder => "reorder"
  | .invalidAuth => "invalid_auth"

/-- Canonical evidence-class normalizer (stable identity in this model). -/
def normalizeEvidence (ev : ByzantineEvidence) : ByzantineEvidence :=
  -- Keep normalization explicit and deterministic for tooling stability.
  { ev with classTag := ev.classTag }

/-- Evidence validity predicate used by structured-counterexample packaging. -/
def EvidenceValid (ev : ByzantineEvidence) : Prop :=
  normalizeEvidence ev = ev

/-- Normalization is idempotent. -/
theorem normalizeEvidence_idempotent (ev : ByzantineEvidence) :
    normalizeEvidence (normalizeEvidence ev) = normalizeEvidence ev := by
  -- The normalizer is a stable projection, so a second pass is a no-op.
  rfl

/-- Normalized evidence is always valid in this canonical representation. -/
theorem evidenceValid_of_normalize (ev : ByzantineEvidence) :
    EvidenceValid (normalizeEvidence ev) := by
  -- Idempotence gives the required fixed-point equation.
  simpa [EvidenceValid] using normalizeEvidence_idempotent ev

/-- Event classification is deterministic under repeated evaluation. -/
theorem eventClass_deterministic (ev : ByzantineEvent) :
    eventClass ev = eventClass ev := by
  -- Determinism is definitional for this total classifier.
  rfl

/-! ## Core Model Interface -/

/-- Minimal model interface for Byzantine safety characterization. -/
structure Model
    (State : Type u) (Decision : Type v) (Certificate : Type w) (Obs : Type x) where
  observe : State → Obs
  certified : State → Decision → Certificate → Prop
  committed : State → Decision → Prop
  conflicts : Decision → Decision → Prop
  certificateWitness : ∀ {s d}, committed s d → ∃ c, certified s d c
  commitmentFromCertificate : ∀ {s d c}, certified s d c → committed s d

/-- Safety-visible observation projection for Byzantine analyses. -/
def Obs_safe_byz
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) (s : State) : Obs :=
  M.observe s

/-- Safety-visible equivalence relation for Byzantine analyses. -/
def Eq_safe_byz
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) (s₁ s₂ : State) : Prop :=
  Obs_safe_byz M s₁ = Obs_safe_byz M s₂

/-! ## Envelope and Safety Relations -/

/-- Envelope relation for one reference/deployed run pair under Byzantine scope. -/
def Envelope_byz
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs)
    (ref impl : Run State) : Prop :=
  ∀ n, Eq_safe_byz M (ref n) (impl n)

/-- Admission relation for requested diff budgets against certified envelope budgets. -/
def DiffAdmissible (envelopeBudget requestedBudget : Nat) : Prop :=
  requestedBudget ≤ envelopeBudget

/-- Byzantine safety property over committed decisions. -/
def ByzantineSafety
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) : Prop :=
  ∀ s d₁ d₂, M.committed s d₁ → M.committed s d₂ → ¬ M.conflicts d₁ d₂

/-- Characterization-side safety condition over certified decisions. -/
def CharacterizationCondition
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) : Prop :=
  ∀ s d₁ d₂ c₁ c₂,
    M.certified s d₁ c₁ → M.certified s d₂ c₂ → ¬ M.conflicts d₁ d₂

/-- Safety-visible contradiction witness for conflicting certified decisions. -/
structure SafetyContradictionWitness
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  state : State
  leftDecision : Decision
  rightDecision : Decision
  leftCert : Certificate
  rightCert : Certificate
  leftCertified : M.certified state leftDecision leftCert
  rightCertified : M.certified state rightDecision rightCert
  conflicts : M.conflicts leftDecision rightDecision

/-! ## Exactness Forms (Soundness/Completeness/Maximality) -/

/-- Soundness theorem form for Byzantine characterization. -/
def ByzantineSafetySoundness
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) : Prop :=
  CharacterizationCondition M → ByzantineSafety M

/-- Completeness theorem form for Byzantine characterization. -/
def ByzantineSafetyCompleteness
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) : Prop :=
  ByzantineSafety M → CharacterizationCondition M

/-- Relative maximality form for Byzantine characterization. -/
def ByzantineSafetyMaximality
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) : Prop :=
  ∀ C : Prop, (C → ByzantineSafety M) → (C → CharacterizationCondition M)

/-- Exact Byzantine safety characterization form. -/
def ExactByzantineSafetyCharacterization
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) : Prop :=
  ByzantineSafetySoundness M ∧
  ByzantineSafetyCompleteness M ∧
  ByzantineSafetyMaximality M

/-! ## Assumption Taxonomy -/

/-- Safety-side assumptions for Byzantine safety characterization. -/
structure SafetyAssumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  byzantineFaultModel : Prop
  evidencePrimitiveConsistent : Prop
  conflictExclusionPrimitiveConsistent : Prop
  finalizationWitnessPrimitiveConsistent : Prop
  quorumIntersectionWitnessed : Prop
  timingAuthCompatible : Prop
  adversarialBudgetBounded : Prop
  characterizationWitness : CharacterizationCondition M

/-- Liveness-side assumptions tracked separately from safety characterization. -/
structure LivenessAssumptions where
  eventualSynchrony : Prop
  fairness : Prop
  pacemakerQuality : Prop

/-- Finalization predicate selected by declared evidence-accumulation regime. -/
def finalizationPredicateFor
    (accumulation : EvidenceAccumulationModel)
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) : State → Decision → Prop :=
  match accumulation with
  | .intersection => M.committed
  | .additiveWeight => M.committed
  | .coupled => M.committed

/-- Conflict-exclusion predicate selected by declared evidence regime. -/
def conflictExclusionFor
    (accumulation : EvidenceAccumulationModel)
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) : Decision → Decision → Prop :=
  match accumulation with
  | .intersection => fun d₁ d₂ => ¬ M.conflicts d₁ d₂
  | .additiveWeight => fun d₁ d₂ => ¬ M.conflicts d₁ d₂
  | .coupled => fun d₁ d₂ => ¬ M.conflicts d₁ d₂

/-! ## Exact Characterization Theorems -/

/-- Soundness: certified-side characterization implies committed-side safety. -/
theorem byzantineSafety_sound_of_characterization
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs)
    (hChar : CharacterizationCondition M) :
    ByzantineSafety M := by
  -- Lift committed decisions to certificates, then apply the characterization premise.
  intro s d₁ d₂ hCommitted₁ hCommitted₂
  rcases M.certificateWitness hCommitted₁ with ⟨c₁, hCert₁⟩
  rcases M.certificateWitness hCommitted₂ with ⟨c₂, hCert₂⟩
  exact hChar s d₁ d₂ c₁ c₂ hCert₁ hCert₂

/-- Completeness: committed-side safety implies certified-side characterization. -/
theorem characterization_of_byzantineSafety
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs)
    (hSafe : ByzantineSafety M) :
    CharacterizationCondition M := by
  -- Project certified decisions into committed decisions and reuse safety.
  intro s d₁ d₂ c₁ c₂ hCert₁ hCert₂
  exact hSafe s d₁ d₂ (M.commitmentFromCertificate hCert₁) (M.commitmentFromCertificate hCert₂)

/-- Relative maximality follows from completeness for the chosen model. -/
theorem byzantineSafety_maximality
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) :
    ByzantineSafetyMaximality M := by
  -- Any context yielding committed-side safety also yields the characterization by completeness.
  intro C hImpliesSafety hC
  exact characterization_of_byzantineSafety M (hImpliesSafety hC)

/-- Exact Byzantine safety characterization holds for the core model interface. -/
theorem exact_byzantineSafety_characterization
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) :
    ExactByzantineSafetyCharacterization M := by
  -- Package soundness, completeness, and maximality into one theorem object.
  refine ⟨?_, ?_, ?_⟩
  · intro hChar
    exact byzantineSafety_sound_of_characterization M hChar
  · intro hSafe
    exact characterization_of_byzantineSafety M hSafe
  · exact byzantineSafety_maximality M

/-- Assumption-indexed safety corollary from the explicit safety-assumption bundle. -/
theorem byzantineSafety_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs)
    (H : SafetyAssumptions M) :
    ByzantineSafety M := by
  -- The assumption bundle carries the characterization witness used by soundness.
  exact byzantineSafety_sound_of_characterization M H.characterizationWitness

/-- Assumption-indexed exact characterization object for explicit-assumption workflows. -/
theorem exact_byzantineSafety_characterization_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs)
    (_H : SafetyAssumptions M) :
    ExactByzantineSafetyCharacterization M := by
  -- The core exactness theorem is reusable; assumptions are tracked at call sites.
  exact exact_byzantineSafety_characterization M

/-! ## Consensus-Family Regime Corollaries -/

/-- BFT-space protocols satisfy intersection-style primitive assumptions. -/
theorem intersectionPrimitive_of_inBFTSpace
    (p : ProtocolSpec) (h : inBFTSpace p = true) :
    intersectionPrimitive p = true := by
  -- The classifier definition contains this primitive as a conjunct.
  have hAll := h
  unfold inBFTSpace at hAll
  simp [Bool.and_eq_true] at hAll
  exact hAll.1.1.1.1.2

/-- Nakamoto-space protocols satisfy additive-weight primitive assumptions. -/
theorem additivePrimitive_of_inNakamotoSpace
    (p : ProtocolSpec) (h : inNakamotoSpace p = true) :
    additivePrimitive p = true := by
  -- The classifier definition contains this primitive as a conjunct.
  have hAll := h
  unfold inNakamotoSpace at hAll
  simp [Bool.and_eq_true] at hAll
  exact hAll.1.1.1.2

/-- Hybrid-space protocols satisfy coupled primitive assumptions. -/
theorem coupledPrimitive_of_inHybridSpace
    (p : ProtocolSpec) (h : inHybridSpace p = true) :
    coupledPrimitive p = true := by
  -- The classifier definition contains this primitive as a conjunct.
  have hAll := h
  unfold inHybridSpace at hAll
  simp [Bool.and_eq_true] at hAll
  exact hAll.1.1.1.1.1.1.1.2

/-! ## Specialization Bridges to Existing Families -/

/-- Quorum-geometry models embedded into the Byzantine-safety core model. -/
def modelOfQuorumGeometry
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (M : Distributed.QuorumGeometry.Model State Decision Certificate Party) :
    Model State Decision Certificate State where
  observe := fun s => s
  certified := M.certified
  committed := Distributed.QuorumGeometry.Committed M
  conflicts := M.conflicts
  certificateWitness := by
    -- Quorum-geometry commitment is definitionally an existential certificate.
    intro s d hCommitted
    exact hCommitted
  commitmentFromCertificate := by
    -- Any certificate witnesses commitment by construction.
    intro s d c hCert
    exact ⟨c, hCert⟩

/-- BFT specialization: quorum-geometry safety yields Byzantine safety. -/
theorem bft_specialization_of_quorumGeometry
    (P : Distributed.QuorumGeometry.SafetyProtocol) :
    ByzantineSafety (modelOfQuorumGeometry P.model) := by
  -- Reuse the certified no-conflicting-commits theorem directly.
  intro s d₁ d₂ hCommitted₁ hCommitted₂
  exact P.noConflictingCommits hCommitted₁ hCommitted₂

/-- BFT specialization also yields certified-side characterization. -/
theorem bft_characterization_of_quorumGeometry
    (P : Distributed.QuorumGeometry.SafetyProtocol) :
    CharacterizationCondition (modelOfQuorumGeometry P.model) := by
  -- Use completeness over the embedded model plus the BFT safety result.
  exact characterization_of_byzantineSafety _ (bft_specialization_of_quorumGeometry P)

/-- Accountable-safety packaging: a safety violation yields explicit evidence. -/
theorem accountableEvidence_of_safetyViolation
    (P : Distributed.AccountableSafety.AccountableProtocol)
    (hNotSafe : ¬ Distributed.AccountableSafety.SafetyHolds P.model) :
    Distributed.AccountableSafety.AccountableEvidenceExists P.model := by
  -- Unpack accountable safety and eliminate the safety branch.
  rcases P.accountableSafety with hSafe | hEvidence
  · exact (hNotSafe hSafe).elim
  · exact hEvidence

/-- Atomic-broadcast bridge extracted for Byzantine theorem composition. -/
theorem atomicBroadcast_bridge_of_protocol
    (P : Distributed.AtomicBroadcast.AtomicBroadcastProtocol) :
    Distributed.AtomicBroadcast.ConsensusAtomicBroadcastBridge P.model :=
  -- Reuse the protocol-level bridge theorem object.
  P.consensusAtomicBroadcastBridge

/-! ## Counterexample and Sharpness Shells -/

/-- Counterexample shell: dropping quorum-style obligations can admit conflicts. -/
structure NoQuorumCounterexample
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  witness : SafetyContradictionWitness M

/-- Counterexample shell: dropping auth/evidence validity can admit conflicts. -/
structure InvalidAuthCounterexample
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  witness : SafetyContradictionWitness M
  invalidEvidence : ByzantineEvidence
  evidenceInvalid : ¬ EvidenceValid invalidEvidence

/-- Counterexample shell: dropping threshold/budget assumptions can admit conflicts. -/
structure ThresholdBudgetCounterexample
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  witness : SafetyContradictionWitness M

/-- Counterexample shell: primitive mismatch can admit conflicting finalizations. -/
structure PrimitiveMismatchCounterexample
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  witness : SafetyContradictionWitness M

/-- Any contradiction witness refutes certified-side characterization immediately. -/
theorem contradictionWitness_refutes_characterization
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M := by
  -- Instantiating characterization on witness components yields contradiction.
  intro hChar
  exact (hChar _ _ _ _ _ w.leftCertified w.rightCertified) w.conflicts

/-! ## Counterexample Constructors by Dropped Assumption Class -/

/-- Dropping quorum/intersection obligations admits a packaged contradiction witness. -/
def noQuorumCounterexample_of_droppedAssumption
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (_hDrop : ¬ H.quorumIntersectionWitnessed)
    (w : SafetyContradictionWitness M) :
    NoQuorumCounterexample M := by
  -- The dropped assumption class is tracked by the theorem premise; the witness is canonical.
  exact { witness := w }

/-- Dropping auth/evidence validity obligations admits a packaged contradiction witness. -/
def invalidAuthCounterexample_of_droppedAssumption
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (_hDrop : ¬ H.evidencePrimitiveConsistent ∨ ¬ H.timingAuthCompatible)
    (w : SafetyContradictionWitness M)
    (invalidEvidence : ByzantineEvidence)
    (hInvalid : ¬ EvidenceValid invalidEvidence) :
    InvalidAuthCounterexample M := by
  -- Keep invalid-evidence payload explicit so converse theorems can reuse the same witness.
  exact
    { witness := w
    , invalidEvidence := invalidEvidence
    , evidenceInvalid := hInvalid
    }

/-! ### Threshold and Primitive Constructors -/

/-- Dropping threshold/adversarial-budget obligations admits a contradiction witness. -/
def thresholdBudgetCounterexample_of_droppedAssumption
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (_hDrop : ¬ H.adversarialBudgetBounded)
    (w : SafetyContradictionWitness M) :
    ThresholdBudgetCounterexample M := by
  -- The dropped-threshold class is tracked in hypotheses; the witness is reused directly.
  exact { witness := w }

/-- Dropping primitive-consistency obligations admits a contradiction witness. -/
def primitiveMismatchCounterexample_of_droppedAssumption
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (_hDrop :
      ¬ H.conflictExclusionPrimitiveConsistent ∨
        ¬ H.finalizationWitnessPrimitiveConsistent)
    (w : SafetyContradictionWitness M) :
    PrimitiveMismatchCounterexample M := by
  -- Primitive mismatch is represented at the assumption layer, with witness-level contradiction.
  exact { witness := w }

/-! ### Minimality Refuters -/

/-- Minimality form: every no-quorum counterexample refutes characterization. -/
theorem noQuorumCounterexample_minimal
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (cex : NoQuorumCounterexample M) :
    ¬ CharacterizationCondition M := by
  -- Any packaged contradiction witness immediately refutes characterization.
  exact contradictionWitness_refutes_characterization cex.witness

/-- Minimality form: every invalid-auth counterexample refutes characterization. -/
theorem invalidAuthCounterexample_minimal
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (cex : InvalidAuthCounterexample M) :
    ¬ CharacterizationCondition M := by
  -- The contradiction witness, not the payload shape, is the minimal refuter.
  exact contradictionWitness_refutes_characterization cex.witness

/-- Minimality form: every threshold-budget counterexample refutes characterization. -/
theorem thresholdBudgetCounterexample_minimal
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (cex : ThresholdBudgetCounterexample M) :
    ¬ CharacterizationCondition M := by
  -- The contradiction witness is sufficient to refute characterization.
  exact contradictionWitness_refutes_characterization cex.witness

/-- Minimality form: every primitive-mismatch counterexample refutes characterization. -/
theorem primitiveMismatchCounterexample_minimal
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (cex : PrimitiveMismatchCounterexample M) :
    ¬ CharacterizationCondition M := by
  -- The contradiction witness is sufficient to refute characterization.
  exact contradictionWitness_refutes_characterization cex.witness

/-! ## Weight-Based and Coupled Specializations -/

/-- Embed a Nakamoto model as a Byzantine-safety model over chain observations. -/
def modelOfNakamoto
    {State : Type u} {Block : Type v} {Party : Type w} :
    Distributed.Nakamoto.Model State Block Party →
      Model State (List Block) Unit (List Block)
  | M =>
      { observe := M.chain
      , certified := fun s d _ => d = M.chain s
      , committed := fun s d => d = M.chain s
      , conflicts := fun d₁ d₂ => d₁ ≠ d₂
      , certificateWitness := by
          -- Commitment is definitional equality with the observed chain.
          intro s d hCommitted
          exact ⟨(), hCommitted⟩
      , commitmentFromCertificate := by
          -- Certification stores the same equality witness as commitment.
          intro s d c hCertified
          exact hCertified
      }

/-- Nakamoto specialization: security protocol induces Byzantine committed-side safety. -/
theorem nakamoto_specialization_of_securityProtocol
    (P : Distributed.Nakamoto.SecurityProtocol) :
    ByzantineSafety (modelOfNakamoto P.model) := by
  -- Conflicts are inequality; both commitments identify the same observed chain.
  intro s d₁ d₂ hCommitted₁ hCommitted₂
  intro hConflict
  apply hConflict
  calc
    d₁ = P.model.chain s := hCommitted₁
    _ = d₂ := hCommitted₂.symm

/-- Nakamoto specialization also yields certified-side characterization. -/
theorem nakamoto_characterization_of_securityProtocol
    (P : Distributed.Nakamoto.SecurityProtocol) :
    CharacterizationCondition (modelOfNakamoto P.model) := by
  -- Reuse completeness over the embedded Nakamoto model.
  exact characterization_of_byzantineSafety _ (nakamoto_specialization_of_securityProtocol P)

/-- Coupled/hybrid specialization: characterization implies safety under hybrid-space tag. -/
theorem hybrid_specialization_of_characterization
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs)
    (p : ProtocolSpec)
    (hHybrid : inHybridSpace p = true)
    (hChar : CharacterizationCondition M) :
    ByzantineSafety M := by
  -- Hybrid-space classification pins the coupled regime; safety follows from soundness.
  have _ : coupledPrimitive p = true := coupledPrimitive_of_inHybridSpace p hHybrid
  exact byzantineSafety_sound_of_characterization M hChar

/-! ## Validator-Consistency Bridges -/

/-- Core bridge: if all byzantine checks pass, the default byzantine assumption gate passes. -/
theorem byzantineAssumptions_allPassed_of_coreChecks
    (p : ProtocolSpec)
    (hFault : p.faultModel = .byzantine)
    (hEvidence : evidencePrimitiveConsistentCheck p = true)
    (hConflict : conflictExclusionPrimitiveConsistentCheck p = true)
    (hFinality : finalizationWitnessPrimitiveConsistentCheck p = true)
    (hQuorum : quorumIntersectionWitnessedCheck p = true)
    (hTiming : timingAuthCompatibleCheck p = true)
    (hBudget : adversarialBudgetBoundedCheck p = true) :
    (runAssumptionValidation p byzantineSafetyAssumptions).allPassed = true := by
  -- Convert each check into the corresponding validator atom.
  have hByz :
      (validateAssumption p .byzantineFaultModel).passed = true := by
    exact (validateAssumption_byzantineFaultModel_passed_iff p).2 hFault
  have hEv :
      (validateAssumption p .evidencePrimitiveConsistent).passed = true := by
    exact (validateAssumption_evidencePrimitiveConsistent_passed_iff p).2 hEvidence
  have hCx :
      (validateAssumption p .conflictExclusionPrimitiveConsistent).passed = true := by
    exact (validateAssumption_conflictExclusionPrimitiveConsistent_passed_iff p).2 hConflict
  have hFin :
      (validateAssumption p .finalizationWitnessPrimitiveConsistent).passed = true := by
    exact (validateAssumption_finalizationWitnessPrimitiveConsistent_passed_iff p).2 hFinality
  have hQ :
      (validateAssumption p .quorumIntersectionWitnessed).passed = true := by
    exact (validateAssumption_quorumIntersectionWitnessed_passed_iff p).2 hQuorum
  have hT :
      (validateAssumption p .timingAuthCompatible).passed = true := by
    exact (validateAssumption_timingAuthCompatible_passed_iff p).2 hTiming
  have hB :
      (validateAssumption p .adversarialBudgetBounded).passed = true := by
    exact (validateAssumption_adversarialBudgetBounded_passed_iff p).2 hBudget
  -- Fold the pointwise checks into the list-level all-passed summary.
  simpa [runAssumptionValidation, allPassed, validateAssumptions, byzantineSafetyAssumptions] using
    And.intro hByz <|
      And.intro hEv <|
        And.intro hCx <|
          And.intro hFin <|
            And.intro hQ <|
              And.intro hT hB

/-! ### Additive-Weight Regime Bridge -/

/-- Additive-weight bridge: all required additive checks imply regime-aware gate success. -/
theorem byzantineAssumptionsFor_allPassed_of_additiveChecks
    (p : ProtocolSpec)
    (hMode : p.evidenceAccumulation = .additiveWeight)
    (hFault : p.faultModel = .byzantine)
    (hEvidence : evidencePrimitiveConsistentCheck p = true)
    (hConflict : conflictExclusionPrimitiveConsistentCheck p = true)
    (hFinality : finalizationWitnessPrimitiveConsistentCheck p = true)
    (hTiming : timingAuthCompatibleCheck p = true)
    (hBudget : adversarialBudgetBoundedCheck p = true) :
    (runAssumptionValidation p (byzantineSafetyAssumptionsFor p)).allPassed = true := by
  -- Convert each required additive check into validator atoms.
  have hByz :
      (validateAssumption p .byzantineFaultModel).passed = true := by
    exact (validateAssumption_byzantineFaultModel_passed_iff p).2 hFault
  have hEv :
      (validateAssumption p .evidencePrimitiveConsistent).passed = true := by
    exact (validateAssumption_evidencePrimitiveConsistent_passed_iff p).2 hEvidence
  have hCx :
      (validateAssumption p .conflictExclusionPrimitiveConsistent).passed = true := by
    exact (validateAssumption_conflictExclusionPrimitiveConsistent_passed_iff p).2 hConflict
  have hFin :
      (validateAssumption p .finalizationWitnessPrimitiveConsistent).passed = true := by
    exact (validateAssumption_finalizationWitnessPrimitiveConsistent_passed_iff p).2 hFinality
  have hT :
      (validateAssumption p .timingAuthCompatible).passed = true := by
    exact (validateAssumption_timingAuthCompatible_passed_iff p).2 hTiming
  have hB :
      (validateAssumption p .adversarialBudgetBounded).passed = true := by
    exact (validateAssumption_adversarialBudgetBounded_passed_iff p).2 hBudget
  -- Regime-aware assumption list removes the quorum obligation in additive mode.
  simpa [runAssumptionValidation, allPassed, validateAssumptions,
    byzantineSafetyAssumptionsFor, hMode] using
    And.intro hByz <|
      And.intro hEv <|
        And.intro hCx <|
          And.intro hFin <|
            And.intro hT hB

/-! ### Family Specialization Bundle -/

/-- Bundle exposing BFT/Nakamoto/hybrid specialization theorems in one object. -/
structure FamilySpecializationBundle where
  bftSafety :
    ∀ (P : Distributed.QuorumGeometry.SafetyProtocol),
      ByzantineSafety (modelOfQuorumGeometry P.model)
  bftCharacterization :
    ∀ (P : Distributed.QuorumGeometry.SafetyProtocol),
      CharacterizationCondition (modelOfQuorumGeometry P.model)
  nakamotoSafety :
    ∀ (P : Distributed.Nakamoto.SecurityProtocol),
      ByzantineSafety (modelOfNakamoto P.model)
  nakamotoCharacterization :
    ∀ (P : Distributed.Nakamoto.SecurityProtocol),
      CharacterizationCondition (modelOfNakamoto P.model)
  hybridSafety :
    ∀ {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x},
      (M : Model State Decision Certificate Obs) →
      (p : ProtocolSpec) →
      inHybridSpace p = true →
      CharacterizationCondition M →
      ByzantineSafety M

/-- Canonical specialization bundle built from theorems in this module. -/
def familySpecializationBundle : FamilySpecializationBundle where
  bftSafety := bft_specialization_of_quorumGeometry
  bftCharacterization := bft_characterization_of_quorumGeometry
  nakamotoSafety := nakamoto_specialization_of_securityProtocol
  nakamotoCharacterization := nakamoto_characterization_of_securityProtocol
  hybridSafety := hybrid_specialization_of_characterization

/-! ## Admission and Capability Gating -/

/-- Capability budget inferred for Byzantine envelope admission. -/
abbrev ByzantineDiffBudget := Nat

/-- Program capability inference for Byzantine safety envelopes. -/
def DProg_byz (p : ProtocolSpec) : ByzantineDiffBudget :=
  match classify p with
  | .outside => 0
  | .nakamoto => 1
  | .bft => 2
  | .hybrid => 3

/-- Canonical envelope budget associated with the current protocol class. -/
def inferredEnvelopeBudget_byz (p : ProtocolSpec) : ByzantineDiffBudget :=
  DProg_byz p

/-- Admission relation for user-requested Byzantine diff budgets. -/
def CapabilityAdmissible_byz
    (envelopeBudget requested : ByzantineDiffBudget) : Prop :=
  requested ≤ envelopeBudget

/-- Admission soundness form for Byzantine capability inference. -/
def AdmissionSoundness_byz (p : ProtocolSpec) : Prop :=
  ∀ dUser, dUser ≤ DProg_byz p →
    CapabilityAdmissible_byz (inferredEnvelopeBudget_byz p) dUser

/-- Admission completeness form for Byzantine capability inference. -/
def AdmissionCompleteness_byz (p : ProtocolSpec) : Prop :=
  ∀ dUser, dUser ≤ DProg_byz p ↔
    CapabilityAdmissible_byz (inferredEnvelopeBudget_byz p) dUser

/-- Principality form for Byzantine capability inference. -/
def AdmissionPrincipality_byz (p : ProtocolSpec) : Prop :=
  DProg_byz p = inferredEnvelopeBudget_byz p

/-! ### Admission Metatheorems -/

/-- Principality theorem for Byzantine capability inference. -/
theorem admissionPrincipality_inferred_byz (p : ProtocolSpec) :
    AdmissionPrincipality_byz p := by
  -- Inferred and certified budgets are definitionally aligned in this layer.
  rfl

/-- Admission soundness theorem for Byzantine capability inference. -/
theorem admissionSoundness_inferred_byz (p : ProtocolSpec) :
    AdmissionSoundness_byz p := by
  -- Budget containment directly implies admissibility by definition.
  intro dUser hContained
  exact hContained

/-- Admission completeness theorem for Byzantine capability inference. -/
theorem admissionCompleteness_inferred_byz (p : ProtocolSpec) :
    AdmissionCompleteness_byz p := by
  -- Both directions reduce to the same budget order relation.
  intro dUser
  constructor
  · intro hContained
    exact hContained
  · intro hAdmit
    exact hAdmit

/-! ### Admission Diagnostics -/

/-- Admission diagnostics: failed assumptions for the regime-aware Byzantine gate. -/
def byzantineAdmissionFailures (p : ProtocolSpec) : List AssumptionResult :=
  (runAssumptionValidation p (byzantineSafetyAssumptionsFor p)).results.filter
    (fun r => !r.passed)

/-- Diagnostics soundness: every listed failure corresponds to a failed check. -/
theorem byzantineAdmissionDiagnostics_sound
    (p : ProtocolSpec) {r : AssumptionResult}
    (hMem : r ∈ byzantineAdmissionFailures p) :
    r.passed = false := by
  -- Membership in the filtered list exposes the failed-predicate witness.
  unfold byzantineAdmissionFailures at hMem
  rcases List.mem_filter.1 hMem with ⟨_hIn, hFailedBool⟩
  cases hPassed : r.passed with
  | false =>
      simp
  | true =>
      simp [hPassed] at hFailedBool

/-- Diagnostics completeness: every failed check is listed by the diagnostics view. -/
theorem byzantineAdmissionDiagnostics_complete
    (p : ProtocolSpec) {r : AssumptionResult}
    (hMem : r ∈ (runAssumptionValidation p (byzantineSafetyAssumptionsFor p)).results)
    (hFailed : r.passed = false) :
    r ∈ byzantineAdmissionFailures p := by
  -- The diagnostics list is exactly the failed-result filter.
  unfold byzantineAdmissionFailures
  exact List.mem_filter.2 ⟨hMem, by simp [hFailed]⟩

end ByzantineSafety
end Distributed
