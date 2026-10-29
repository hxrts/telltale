
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
  bft_specialization_of_quorum_geometry P

example (P : Distributed.Nakamoto.SecurityProtocol) :
    ByzantineSafety (modelOfNakamoto P.model) :=
  nakamoto_specialization_of_security_protocol P

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
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M :=
  noQuorumConflictWitness_refutes { conflict := w }

example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M :=
  invalidAuthConflictWitness_refutes { conflict := w }

example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M :=
  thresholdBudgetConflictWitness_refutes { conflict := w }

example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (w : SafetyContradictionWitness M) :
    ¬ CharacterizationCondition M :=
  primitiveMismatchConflictWitness_refutes { conflict := w }

/- Concrete: an unconstrained model admits a conflict witness. -/
example :
    ∃ M : Model Unit Bool Unit Unit,
      Nonempty (SafetyContradictionWitness M) ∧ ¬ CharacterizationCondition M :=
  unconstrained_conflict_exists

/- Honest status: safety assumptions exclude every contradiction witness. -/
example
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M) (w : SafetyContradictionWitness M) : False :=
  safetyAssumptions_exclude_contradiction H w

end CounterexampleRegression

section AdmissionRegression

example (p : ProtocolSpec) :
    AdmissionPrincipality_byz p :=
  admission_principality_inferred_byz p

example (p : ProtocolSpec) :
    AdmissionSoundness_byz p :=
  admission_soundness_inferred_byz p

example (p : ProtocolSpec) :
    AdmissionCompleteness_byz p :=
  admission_completeness_inferred_byz p

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
  certificateForCommit := by
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
