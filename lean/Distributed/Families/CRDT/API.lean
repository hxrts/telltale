import Distributed.Families.CRDT.Core

set_option autoImplicit false

/-! # Distributed.Families.CRDT.API

High-level API for automatic CRDT theorem-family certification.
-/

/-
The Problem. Downstream modules need a single certified interface bundling the
CRDT theorem-family assumptions/premises and their derived conclusions.
Solution Structure. Provide certified protocol/erasure structures, a canonical
premise constructor, and a validation convenience theorem.
-/

namespace Distributed
namespace CRDT

universe u v w x y z

/-! ## Certified Protocol Bundles -/

/-- Certified CRDT package bundling theorem-family assumptions and premises. -/
structure CRDTProtocol where
  State : Type u
  Op : Type v
  Context : Type w
  Obs : Type x
  Program : Type y
  model : Model State Op Context Obs Program
  assumptions : Assumptions model
  premises : Premises model
  exactEnvelope :
    ExactEnvelopeCharacterization model premises.RefRun premises.ImplRun :=
      exactEnvelope_of_assumptions assumptions premises
  adequacy :
    ObservationalAdequacyModuloEnvelope model premises.RefRun premises.ImplRun :=
      adequacy_of_assumptions assumptions premises
  principalCapability :
    PrincipalCapability premises.inferredBudget premises.envelopeBudget :=
      principalCapability_of_assumptions assumptions premises
  admissionSoundness :
    AdmissionSoundness premises.inferredBudget premises.envelopeBudget :=
      admissionSoundness_of_assumptions assumptions premises
  admissionCompleteness :
    AdmissionCompleteness premises.inferredBudget premises.envelopeBudget :=
      admissionCompleteness_of_assumptions assumptions premises
  opStateEquivalence :
    OpStateEquivalence model premises.opRun premises.stateRun :=
      opStateEquivalence_of_assumptions assumptions premises
  gcSafetyIffCausalDominance :
    GCSafetyIffCausalDominance premises.GCSafe premises.CausalDominanceEstablished :=
      gcSafetyIff_of_assumptions assumptions premises
  boundedApproximation :
    BoundedMetadataApproximation model premises.approxPolicy premises.horizon
      premises.epsilon premises.referenceRun premises.deployedRun :=
      boundedApproximation_of_assumptions assumptions premises
  approximationMonotonicity :
    ApproximationMonotoneUnderPolicyTightening model premises.approxPolicy premises.approxPolicy
      premises.horizon premises.epsilon premises.referenceRun premises.deployedRun :=
      approximationMonotone_of_assumptions assumptions premises
  exactSECAsLimit :
    ExactSECRecoveryAsLimit model premises.approxPolicy premises.referenceRun premises.deployedRun :=
      exactSECAsLimit_of_assumptions assumptions premises
  hcrdtCore : HcrdtCore model := hcrdtCore_of_assumptions assumptions
  hcrdtFoundation : HcrdtFoundation model := hcrdtFoundation_of_assumptions assumptions
  hcrdtDynamics : HcrdtDynamics model := hcrdtDynamics_of_assumptions assumptions
  hcrdtExtensions : HcrdtExtensions model := hcrdtExtensions_of_assumptions assumptions
  hcrdtLimits : HcrdtLimits model := hcrdtLimits_of_assumptions assumptions

/-! ## Certified Erasure Bundle -/

/-- Certified erasure package for weakest-core continuation proofs. -/
structure CRDTErasureProtocol where
  State : Type u
  Op : Type v
  Context : Type w
  Obs : Type x
  Program : Type y
  KRich : Type z
  OpTag : Type v
  Args : Type w
  Enc : Type x
  model : Model State Op Context Obs Program
  premises : ErasurePremises model KRich OpTag Args Enc
  weakestOpCoreErasure :
    WeakestOpCoreErasureTheorem model premises.evalRich premises.interp premises.erase :=
      weakestOpCoreErasure_of_premises premises
  replayStable :
    ReplayStableCoreEval premises.interp :=
      opCoreReplayStable_of_premises premises
  serializationInvariant :
    TransportSerializationInvariant premises.encode premises.decode :=
      opCoreSerializationInvariant_of_premises premises
  conformanceGateIffLowered :
    ∀ kr, conformanceGate premises.lower kr = true ↔ ∃ kc, premises.lower kr = some kc :=
      conformanceGate_of_loweringSound premises

/-! ## Canonical Premise Constructor -/

/-- Build canonical erasure premises for the core-equivalent rich fragment. -/
def coreEquivalentErasurePremises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (encode : OpCore OpTag Args → Enc)
    (decode : Enc → Option (OpCore OpTag Args))
    (hReplay : ReplayStableCoreEval interp)
    (hSerial : TransportSerializationInvariant encode decode) :
    ErasurePremises M (CoreEquivalentKRich OpTag Args) OpTag Args Enc :=
  { evalRich := evalRichCoreEquivalent interp
  , interp := interp
  , erase := eraseCoreEquivalent
  , lower := lowerCoreEquivalent
  , encode := encode
  , decode := decode
  , weakestWitness := weakestOpCoreErasure_coreEquivalent M interp
  , replayStableWitness := hReplay
  , serializationWitness := hSerial
  , lowerSound := by
      intro kr kc hk
      exact lowerCoreEquivalent_sound kr kc hk
  }

/-! ## Validation Convenience Theorem -/

/-- Core assumptions are always validated for a certified CRDT protocol. -/
theorem coreAssumptions_allPassed (P : CRDTProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end CRDT
end Distributed
