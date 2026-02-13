
import Distributed.Families.ByzantineSafety

/- ## Structured Block 1 -/
set_option autoImplicit false

/-!
# Distributed.Tests.ByzantineConformance

Compile-time regression checks for the Byzantine characterization layer.
These theorem-style tests guard specialization, sharpness, and envelope-level
cross-target conformance under Byzantine event injections.
-/

namespace Distributed
namespace Tests
namespace ByzantineConformance

open Distributed.ByzantineSafety

universe u v w x

section PositiveProfiles

example (P : Distributed.QuorumGeometry.SafetyProtocol) :
    ByzantineSafety (modelOfQuorumGeometry P.model) :=
  bft_specialization_of_quorumGeometry P

example (P : Distributed.Nakamoto.SecurityProtocol) :
    ByzantineSafety (modelOfNakamoto P.model) :=
  nakamoto_specialization_of_securityProtocol P

example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    (M : Model State Decision Certificate Obs)
    (p : ProtocolSpec)
    (hHybrid : inHybridSpace p = true)
    (hChar : CharacterizationCondition M) :
    ByzantineSafety M :=
  hybrid_specialization_of_characterization M p hHybrid hChar

end PositiveProfiles

section CounterexampleRegression

example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (hDrop : ¬ H.quorumIntersectionWitnessed)
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M := by
  let cex := noQuorumCounterexample_of_droppedAssumption H hDrop w
  exact noQuorumCounterexample_minimal cex

example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (hDrop : ¬ H.evidencePrimitiveConsistent ∨ ¬ H.timingAuthCompatible)
    (w : SafetyContradictionWitness M)
    (bad : ByzantineEvidence)
    (hBad : ¬ EvidenceValid bad) :
    ¬ CharacterizationCondition M := by
  let cex := invalidAuthCounterexample_of_droppedAssumption H hDrop w bad hBad
  exact invalidAuthCounterexample_minimal cex

example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (hDrop : ¬ H.adversarialBudgetBounded)
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M := by
/- ## Structured Block 2 -/
  let cex := thresholdBudgetCounterexample_of_droppedAssumption H hDrop w
  exact thresholdBudgetCounterexample_minimal cex

example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (hDrop :
      ¬ H.conflictExclusionPrimitiveConsistent ∨
        ¬ H.finalizationWitnessPrimitiveConsistent)
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M := by
  let cex := primitiveMismatchCounterexample_of_droppedAssumption H hDrop w
  exact primitiveMismatchCounterexample_minimal cex

end CounterexampleRegression

section AdmissionRegression

example (p : ProtocolSpec) :
    AdmissionPrincipality_byz p :=
  admissionPrincipality_inferred_byz p

example (p : ProtocolSpec) :
    AdmissionSoundness_byz p :=
  admissionSoundness_inferred_byz p

example (p : ProtocolSpec) :
    AdmissionCompleteness_byz p :=
  admissionCompleteness_inferred_byz p

end AdmissionRegression

section InjectedConformance

abbrev InjectedState := List ByzantineEvent

def injectByzantineEvents (base injected : List ByzantineEvent) : InjectedState :=
  base ++ injected

def injectedRun (base injected : List ByzantineEvent) : Run InjectedState :=
  fun _ => injectByzantineEvents base injected

def injectedByzantineModel : Model InjectedState (List String) Unit (List String) where
  observe s := s.map eventClass
  certified s d _ := d = s.map eventClass
  committed s d := d = s.map eventClass
  conflicts d₁ d₂ := d₁ ≠ d₂
  certificateWitness := by
    intro s d hCommitted
    exact ⟨(), hCommitted⟩
  commitmentFromCertificate := by
    intro s d c hCertified
    exact hCertified

example (base injected : List ByzantineEvent) :
    Envelope_byz injectedByzantineModel
      (injectedRun base injected)
      (injectedRun base injected) := by
  intro n
  rfl

example (base injected : List ByzantineEvent) :
    Envelope_byz injectedByzantineModel
/- ## Structured Block 3 -/
      (injectedRun base injected)
      (injectedRun base injected) := by
  intro n
  rfl

end InjectedConformance

end ByzantineConformance
end Tests
end Distributed

