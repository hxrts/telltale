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

/-! ## Certified Protocol Extractors -/

/-- Extract exact envelope characterization from a certified CRDT bundle. -/
theorem exact_envelope_of_protocol (P : CRDTProtocol) :
    ExactEnvelopeCharacterization P.model P.premises.RefRun P.premises.ImplRun :=
  exact_envelope_of_assumptions P.assumptions P.premises

/-- Extract observational adequacy from a certified CRDT bundle. -/
theorem adequacy_of_protocol (P : CRDTProtocol) :
    ObservationalAdequacyModuloEnvelope P.model P.premises.RefRun P.premises.ImplRun :=
  adequacy_of_assumptions P.assumptions P.premises

/-- Extract principal capability from a certified CRDT bundle. -/
theorem principal_capability_of_protocol (P : CRDTProtocol) :
    PrincipalCapability P.premises.inferredBudget P.premises.envelopeBudget :=
  principal_capability_of_assumptions P.assumptions P.premises

/-- Extract admission soundness from a certified CRDT bundle. -/
theorem admission_soundness_of_protocol (P : CRDTProtocol) :
    AdmissionSoundness P.premises.inferredBudget P.premises.envelopeBudget :=
  admission_soundness_of_assumptions P.assumptions P.premises

/-- Extract admission completeness from a certified CRDT bundle. -/
theorem admission_completeness_of_protocol (P : CRDTProtocol) :
    AdmissionCompleteness P.premises.inferredBudget P.premises.envelopeBudget :=
  admission_completeness_of_assumptions P.assumptions P.premises

/-- Extract operation/state equivalence from a certified CRDT bundle. -/
theorem op_state_equivalence_of_protocol (P : CRDTProtocol) :
    OpStateEquivalence P.model P.premises.opRun P.premises.stateRun :=
  op_state_equivalence_of_assumptions P.assumptions P.premises

/-- Extract GC-safety iff causal-dominance from a certified CRDT bundle. -/
theorem gc_safety_iff_of_protocol (P : CRDTProtocol) :
    GCSafetyIffCausalDominance P.premises.GCSafe P.premises.CausalDominanceEstablished :=
  gc_safety_iff_of_assumptions P.assumptions P.premises

/-- Extract bounded metadata approximation from a certified CRDT bundle. -/
theorem bounded_approximation_of_protocol (P : CRDTProtocol) :
    BoundedMetadataApproximation P.model P.premises.approxPolicy P.premises.horizon
      P.premises.epsilon P.premises.referenceRun P.premises.deployedRun :=
  bounded_approximation_of_assumptions P.assumptions P.premises

/-- Extract approximation monotonicity from a certified CRDT bundle. -/
theorem approximation_monotone_of_protocol (P : CRDTProtocol) :
    ApproximationMonotoneUnderPolicyTightening P.model P.premises.approxPolicy
      P.premises.approxPolicy P.premises.horizon P.premises.epsilon
      P.premises.referenceRun P.premises.deployedRun :=
  approximation_monotone_of_assumptions P.assumptions P.premises

/-- Extract exact-SEC-as-limit from a certified CRDT bundle. -/
theorem exact_sec_as_limit_of_protocol (P : CRDTProtocol) :
    ExactSECRecoveryAsLimit P.model P.premises.approxPolicy
      P.premises.referenceRun P.premises.deployedRun :=
  exact_sec_as_limit_of_assumptions P.assumptions P.premises

/-- Extract the CRDT core hierarchy from a certified CRDT bundle. -/
theorem hcrdt_core_of_protocol (P : CRDTProtocol) : HcrdtCore P.model :=
  hcrdt_core_of_assumptions P.assumptions

/-- Extract the CRDT foundation hierarchy from a certified CRDT bundle. -/
theorem hcrdt_foundation_of_protocol (P : CRDTProtocol) : HcrdtFoundation P.model :=
  hcrdt_foundation_of_assumptions P.assumptions

/-- Extract the CRDT dynamics hierarchy from a certified CRDT bundle. -/
theorem hcrdt_dynamics_of_protocol (P : CRDTProtocol) : HcrdtDynamics P.model :=
  hcrdt_dynamics_of_assumptions P.assumptions

/-- Extract the CRDT extensions hierarchy from a certified CRDT bundle. -/
theorem hcrdt_extensions_of_protocol (P : CRDTProtocol) : HcrdtExtensions P.model :=
  hcrdt_extensions_of_assumptions P.assumptions

/-- Extract the CRDT limits hierarchy from a certified CRDT bundle. -/
theorem hcrdt_limits_of_protocol (P : CRDTProtocol) : HcrdtLimits P.model :=
  hcrdt_limits_of_assumptions P.assumptions

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
      weakest_op_core_erasure_of_premises premises
  replayStable :
    ReplayStableCoreEval premises.interp :=
      op_core_replay_stable_of_premises premises
  serializationInvariant :
    TransportSerializationInvariant premises.encode premises.decode :=
      op_core_serialization_invariant_of_premises premises
  conformanceGateIffLowered :
    ∀ kr, conformanceGate premises.lower kr = true ↔ ∃ kc, premises.lower kr = some kc :=
      conformance_gate_of_lowering_sound premises

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
  , erasureSound := (weakest_op_core_erasure_core_equivalent M interp).1
  , erasureComplete := (weakest_op_core_erasure_core_equivalent M interp).2.1
  , erasureMaximal := (weakest_op_core_erasure_core_equivalent M interp).2.2
  , replayStable := hReplay
  , serializationRoundTrip := hSerial
  , lowerSound := by
      intro kr kc hk
      exact lower_core_equivalent_sound kr kc hk
  }

/-! ## Validation Convenience Theorem -/

/-- Core assumptions are always validated for a certified CRDT protocol. -/
theorem core_assumptions_all_passed (P : CRDTProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end CRDT
end Distributed
