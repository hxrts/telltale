import Distributed.Families.ByzantineSafety.Core.Base

set_option autoImplicit false

/-! # Distributed.Families.ByzantineSafety.Core.Counterexamples

Honest status facts about Byzantine-safety counterexamples.

`SafetyAssumptions M` carries a `QuorumGeometry.Assumptions` fault model
(`n + f < 2q`, at most `f` Byzantine signers, honest non-equivocation)
together with embeddings of `M.certified` and `M.conflicts` into the quorum
model. By the proved honest-quorum-intersection theorem these force
`CharacterizationCondition M`, so no `SafetyContradictionWitness M`
can coexist with any `SafetyAssumptions M`.
Consequently a "drop one label, keep the record" counterexample cannot be
constructed in this encoding. What can be shown concretely is that a model
without any quorum structure admits a contradiction witness.
-/

namespace Distributed
namespace ByzantineSafety

universe u v w x

/-! ## Safety Assumptions Force Characterization -/

/-- Any `SafetyAssumptions` record implies certified-side characterization,
via the proved no-conflicting-commits theorem of the embedded quorum model. -/
theorem characterization_of_safetyAssumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M) :
    CharacterizationCondition M := by
  intro s d₁ d₂ c₁ c₂ h₁ h₂ hConf
  exact Distributed.QuorumGeometry.no_conflicting_commits_of_assumptions H.quorumAssumptions
    ⟨_, H.certifiedToQuorum h₁⟩ ⟨_, H.certifiedToQuorum h₂⟩ (H.conflictToQuorum hConf)

/-- A contradiction witness is incompatible with every `SafetyAssumptions`
record; dropped-assumption "counterexamples" that keep the record are vacuous. -/
theorem safetyAssumptions_exclude_contradiction
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Obs : Type x}
    {M : Model State Decision Certificate Obs}
    (H : SafetyAssumptions M)
    (wit : SafetyContradictionWitness M) : False :=
  characterization_of_safetyAssumptions H _ _ _ _ _
    wit.leftCertified wit.rightCertified wit.conflicts

/-- Every evidence record is valid: `normalizeEvidence` is the identity, so
`¬ EvidenceValid ev` is never satisfiable. -/
theorem evidenceValid_always (ev : ByzantineEvidence) : EvidenceValid ev := rfl

/-! ## Concrete Unconstrained Conflict Model -/

/-- Model with no quorum structure: both Boolean decisions are certified in
the single state and distinct decisions conflict. -/
def unconstrainedConflictModel : Model Unit Bool Unit Unit where
  observe := fun _ => ()
  certified := fun _ _ _ => True
  committed := fun _ _ => True
  conflicts := fun d₁ d₂ => d₁ ≠ d₂
  certificateForCommit := fun _ => ⟨(), trivial⟩
  commitmentFromCertificate := fun _ => trivial

/-- Concrete contradiction witness: `true` and `false` are both certified. -/
def unconstrainedConflictWitness :
    SafetyContradictionWitness unconstrainedConflictModel where
  state := ()
  leftDecision := true
  rightDecision := false
  leftCert := ()
  rightCert := ()
  leftCertified := trivial
  rightCertified := trivial
  conflicts := Bool.noConfusion

/-- Concrete counterexample: some model admits conflicting certified decisions
and therefore fails characterization. -/
theorem unconstrained_conflict_exists :
    ∃ M : Model Unit Bool Unit Unit,
      Nonempty (SafetyContradictionWitness M) ∧ ¬ CharacterizationCondition M :=
  ⟨unconstrainedConflictModel, ⟨unconstrainedConflictWitness⟩, fun h =>
    h () true false () () trivial trivial Bool.noConfusion⟩

/-- The unconstrained model admits no `SafetyAssumptions` record at all. -/
theorem unconstrainedConflictModel_no_safetyAssumptions
    (H : SafetyAssumptions unconstrainedConflictModel) : False :=
  safetyAssumptions_exclude_contradiction H unconstrainedConflictWitness

end ByzantineSafety
end Distributed
