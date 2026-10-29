import Distributed.Families.ByzantineSafety.Core.Counterexamples

set_option autoImplicit false

/-! # Distributed.Families.ByzantineSafety.Core.Extensions

Conflict-witness interfaces, specialization bridges, validator links, and
admission/diagnostic theorems layered on top of the Byzantine-safety core base.
-/

/-
The Problem. The extension theorem surface (counterexamples, family
specializations, validator bridges, and admission diagnostics) is large enough
to obscure the foundational model definitions when kept in one file.

Solution Structure. Keep core interfaces and exactness theorems in
`Core.Base`, and place extension theorems/packaging in this file.
-/

namespace Distributed
namespace ByzantineSafety

universe u v w x

/-! ## Conflict-Witness Interfaces

These structures are interfaces that package a caller-supplied
`SafetyContradictionWitness`, tagged by the assumption class a client intends
to blame. They prove nothing about existence. In particular, by
`safetyAssumptions_exclude_contradiction`, no witness exists for any model
that also carries a `SafetyAssumptions` record, so a "dropped label" premise
cannot be combined with a witness non-vacuously. A concrete model admitting a
witness is `unconstrainedConflictModel` in `Core.Counterexamples`.
-/

/-- Witness interface tagged "quorum obligations dropped"; packages a supplied witness. -/
structure NoQuorumConflictWitness
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  conflict : SafetyContradictionWitness M

/-- Witness interface tagged "auth/evidence validity dropped"; packages a supplied
witness. (`¬ EvidenceValid` is unsatisfiable, see `evidenceValid_always`.) -/
structure InvalidAuthConflictWitness
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  conflict : SafetyContradictionWitness M

/-- Witness interface tagged "threshold/budget dropped"; packages a supplied witness. -/
structure ThresholdBudgetConflictWitness
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  conflict : SafetyContradictionWitness M

/-- Witness interface tagged "primitive mismatch"; packages a supplied witness. -/
structure PrimitiveMismatchConflictWitness
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs) where
  conflict : SafetyContradictionWitness M

/-- Any contradiction witness refutes certified-side characterization immediately. -/
theorem contradiction_witness_refutes_characterization
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M := by
  -- Instantiating characterization on witness components yields contradiction.
  intro hChar
  exact (hChar _ _ _ _ _ w.leftCertified w.rightCertified) w.conflicts

/-! ### Interface Refuters

Each refuter only forwards the packaged witness to
`contradiction_witness_refutes_characterization`.
-/

/-- A packaged no-quorum witness refutes characterization. -/
theorem noQuorumConflictWitness_refutes
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (cex : NoQuorumConflictWitness M) : ¬ CharacterizationCondition M :=
  contradiction_witness_refutes_characterization cex.conflict

/-- A packaged invalid-auth witness refutes characterization. -/
theorem invalidAuthConflictWitness_refutes
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (cex : InvalidAuthConflictWitness M) : ¬ CharacterizationCondition M :=
  contradiction_witness_refutes_characterization cex.conflict

/-- A packaged threshold-budget witness refutes characterization. -/
theorem thresholdBudgetConflictWitness_refutes
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (cex : ThresholdBudgetConflictWitness M) : ¬ CharacterizationCondition M :=
  contradiction_witness_refutes_characterization cex.conflict

/-- A packaged primitive-mismatch witness refutes characterization. -/
theorem primitiveMismatchConflictWitness_refutes
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (cex : PrimitiveMismatchConflictWitness M) : ¬ CharacterizationCondition M :=
  contradiction_witness_refutes_characterization cex.conflict

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
      , certificateForCommit := by
          -- Commitment is definitional equality with the observed chain.
          intro s d hCommitted
          exact ⟨(), hCommitted⟩
      , commitmentFromCertificate := by
          -- Certification stores the same equality witness as commitment.
          intro s d c hCertified
          exact hCertified
      }

/-- Nakamoto specialization: security protocol induces Byzantine committed-side safety. -/
theorem nakamoto_specialization_of_security_protocol
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
theorem nakamoto_characterization_of_security_protocol
    (P : Distributed.Nakamoto.SecurityProtocol) :
    CharacterizationCondition (modelOfNakamoto P.model) := by
  -- Reuse completeness over the embedded Nakamoto model.
  exact characterization_of_byzantine_safety _ (nakamoto_specialization_of_security_protocol P)

/-- Coupled/hybrid specialization: characterization implies safety under hybrid-space tag. -/
theorem hybrid_specialization_of_characterization
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs)
    (p : ProtocolSpec)
    (hHybrid : inHybridSpace p = true)
    (hChar : CharacterizationCondition M) :
    ByzantineSafety M := by
  -- Hybrid-space classification pins the coupled regime; safety follows from soundness.
  have _ : coupledPrimitive p = true := coupled_primitive_of_in_hybrid_space p hHybrid
  exact byzantine_safety_sound_of_characterization M hChar

/-! ## Validator-Consistency Bridges -/

/-- Core bridge: if all byzantine checks pass, the default byzantine assumption gate passes. -/
theorem byzantine_assumptions_all_passed_of_core_checks
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
    exact (validate_assumption_byzantine_fault_model_passed_iff p).2 hFault
  have hEv :
      (validateAssumption p .evidencePrimitiveConsistent).passed = true := by
    exact (validate_assumption_evidence_primitive_consistent_passed_iff p).2 hEvidence
  have hCx :
      (validateAssumption p .conflictExclusionPrimitiveConsistent).passed = true := by
    exact (validate_assumption_conflict_exclusion_primitive_consistent_passed_iff p).2 hConflict
  have hFin :
      (validateAssumption p .finalizationWitnessPrimitiveConsistent).passed = true := by
    exact (validate_assumption_finalization_witness_primitive_consistent_passed_iff p).2 hFinality
  have hQ :
      (validateAssumption p .quorumIntersectionWitnessed).passed = true := by
    exact (validate_assumption_quorum_intersection_witnessed_passed_iff p).2 hQuorum
  have hT :
      (validateAssumption p .timingAuthCompatible).passed = true := by
    exact (validate_assumption_timing_auth_compatible_passed_iff p).2 hTiming
  have hB :
      (validateAssumption p .adversarialBudgetBounded).passed = true := by
    exact (validate_assumption_adversarial_budget_bounded_passed_iff p).2 hBudget
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
theorem byzantine_assumptions_for_all_passed_of_additive_checks
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
    exact (validate_assumption_byzantine_fault_model_passed_iff p).2 hFault
  have hEv :
      (validateAssumption p .evidencePrimitiveConsistent).passed = true := by
    exact (validate_assumption_evidence_primitive_consistent_passed_iff p).2 hEvidence
  have hCx :
      (validateAssumption p .conflictExclusionPrimitiveConsistent).passed = true := by
    exact (validate_assumption_conflict_exclusion_primitive_consistent_passed_iff p).2 hConflict
  have hFin :
      (validateAssumption p .finalizationWitnessPrimitiveConsistent).passed = true := by
    exact (validate_assumption_finalization_witness_primitive_consistent_passed_iff p).2 hFinality
  have hT :
      (validateAssumption p .timingAuthCompatible).passed = true := by
    exact (validate_assumption_timing_auth_compatible_passed_iff p).2 hTiming
  have hB :
      (validateAssumption p .adversarialBudgetBounded).passed = true := by
    exact (validate_assumption_adversarial_budget_bounded_passed_iff p).2 hBudget
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
    ∀ (P : Distributed.QuorumGeometry.SafetyProtocol.{u, v, w, x}),
      ByzantineSafety (modelOfQuorumGeometry P.model)
  bftCharacterization :
    ∀ (P : Distributed.QuorumGeometry.SafetyProtocol.{u, v, w, x}),
      CharacterizationCondition (modelOfQuorumGeometry P.model)
  nakamotoSafety :
    ∀ (P : Distributed.Nakamoto.SecurityProtocol.{u, v, w}),
      ByzantineSafety (modelOfNakamoto P.model)
  nakamotoCharacterization :
    ∀ (P : Distributed.Nakamoto.SecurityProtocol.{u, v, w}),
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
  bftSafety := bft_specialization_of_quorum_geometry
  bftCharacterization := bft_characterization_of_quorum_geometry
  nakamotoSafety := nakamoto_specialization_of_security_protocol
  nakamotoCharacterization := nakamoto_characterization_of_security_protocol
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
theorem admission_principality_inferred_byz (p : ProtocolSpec) :
    AdmissionPrincipality_byz p := by
  -- Inferred and certified budgets are definitionally aligned in this layer.
  rfl

/-- Admission soundness theorem for Byzantine capability inference. -/
theorem admission_soundness_inferred_byz (p : ProtocolSpec) :
    AdmissionSoundness_byz p := by
  -- Budget containment directly implies admissibility by definition.
  intro dUser hContained
  exact hContained

/-- Admission completeness theorem for Byzantine capability inference. -/
theorem admission_completeness_inferred_byz (p : ProtocolSpec) :
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
theorem byzantine_admission_diagnostics_sound
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
theorem byzantine_admission_diagnostics_complete
    (p : ProtocolSpec) {r : AssumptionResult}
    (hMem : r ∈ (runAssumptionValidation p (byzantineSafetyAssumptionsFor p)).results)
    (hFailed : r.passed = false) :
    r ∈ byzantineAdmissionFailures p := by
  -- The diagnostics list is exactly the failed-result filter.
  unfold byzantineAdmissionFailures
  exact List.mem_filter.2 ⟨hMem, by simp [hFailed]⟩


end ByzantineSafety
end Distributed
