import Distributed.Model.Assumptions
import Distributed.Model.Classifier
import Distributed.Families.QuorumGeometry
import Distributed.Families.AccountableSafety
import Distributed.Families.AtomicBroadcast

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

/-- Normalization is idempotent. -/
theorem normalizeEvidence_idempotent (ev : ByzantineEvidence) :
    normalizeEvidence (normalizeEvidence ev) = normalizeEvidence ev := by
  -- The normalizer is a stable projection, so a second pass is a no-op.
  rfl

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

end ByzantineSafety
end Distributed
