import Protocol.Deployment.Interface
import Runtime.Adequacy.EnvelopeCore.ReconfigurationBridge
import Runtime.VM.Model.SemanticObjects.TransformationLocalObligations

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.TransformationLocalObligationsLemmas

The Problem.
The transformation-local bundle layer needs theorem-facing consequences:
affected operations/effects/publications must be covered explicitly, late
results must follow an explicit policy, and each transformation kind needs a
clear local admissibility story.

Solution Structure.
This module proves direct coverage/admissibility lemmas over local bundles and
provides lightweight bridge structures to deployment-linking and
reconfiguration-Harmony theorem families.
-/

namespace Runtime.VM.Model

open Runtime.Adequacy

universe u v

/-! ## Explicit Coverage Lemmas -/

theorem affected_operation_has_local_obligation
    {bundle : TransformationLocalObligationBundle}
    (hExplicit : bundle.explicitOperationHandling)
    {operation : OperationInstance}
    (hAffected : operation.operationId ∈ bundle.obligation.affectedOperationIds) :
    ∃ entry ∈ bundle.operationObligations, entry.matchesOperation operation := by
  rcases hExplicit operation.operationId hAffected with ⟨entry, hMem, hEq⟩
  exact ⟨entry, hMem, by simpa [OperationLocalObligation.matchesOperation] using hEq⟩

theorem transported_effect_has_transport_obligation
    {bundle : TransformationLocalObligationBundle}
    (hExplicit : bundle.explicitEffectHandling)
    {effect : OutstandingEffect}
    (hTransport : effect.effectId ∈ bundle.obligation.transportedEffectIds) :
    ∃ entry ∈ bundle.effectObligations,
      entry.matchesEffect effect ∧ entry.disposition = .transport := by
  rcases hExplicit with ⟨_, hTransports, _⟩
  rcases hTransports effect.effectId hTransport with ⟨entry, hMem, hEq, hDisp⟩
  exact ⟨entry, hMem, by simpa [EffectLocalObligation.matchesEffect] using hEq, hDisp⟩

theorem invalidated_effect_has_invalidation_obligation
    {bundle : TransformationLocalObligationBundle}
    (hExplicit : bundle.explicitEffectHandling)
    {effect : OutstandingEffect}
    (hInvalidate : effect.effectId ∈ bundle.obligation.invalidatedEffectIds) :
    ∃ entry ∈ bundle.effectObligations,
      entry.matchesEffect effect ∧ entry.disposition = .invalidate := by
  rcases hExplicit with ⟨_, _, hInvalidates⟩
  rcases hInvalidates effect.effectId hInvalidate with ⟨entry, hMem, hEq, hDisp⟩
  exact ⟨entry, hMem, by simpa [EffectLocalObligation.matchesEffect] using hEq, hDisp⟩

theorem affected_publication_has_local_obligation
    {bundle : TransformationLocalObligationBundle}
    {objects : ProtocolMachineSemanticObjects}
    (hExplicit : bundle.explicitPublicationHandling objects)
    {event : PublicationEvent}
    (hMem : event ∈ objects.publicationEvents)
    (hAffected : event.operationId ∈ bundle.obligation.affectedOperationIds) :
    ∃ entry ∈ bundle.publicationObligations, entry.matchesEvent event := by
  exact hExplicit event hMem hAffected

theorem proof_backed_publication_has_witness_obligation
    {bundle : TransformationLocalObligationBundle}
    {objects : ProtocolMachineSemanticObjects}
    (hExplicit : bundle.explicitWitnessHandling objects)
    {event : PublicationEvent}
    (hMem : event ∈ objects.publicationEvents)
    (hAffected : event.operationId ∈ bundle.obligation.affectedOperationIds)
    {proofRef : String}
    (hProof : event.proofRef = some proofRef) :
    ∃ entry ∈ bundle.witnessObligations, entry.proofRef = proofRef :=
  hExplicit event hMem hAffected proofRef hProof

theorem explicit_bundle_has_nonimplicit_late_result_policy
    {bundle : TransformationLocalObligationBundle}
    (hExplicit : bundle.explicitLateResultHandling) :
    bundle.lateResultPolicy = .reject ∨
    bundle.lateResultPolicy = .transport ∨
    bundle.lateResultPolicy = .reissue :=
  hExplicit

/-! ## Kind-Specific Admissibility -/

theorem delegation_bundle_has_publication_revoke_and_activate
    {bundle : TransformationLocalObligationBundle}
    (hDelegation : bundle.delegationAdmissible)
    (hKind : bundle.kind = .delegation) :
    (∃ entry ∈ bundle.publicationObligations, entry.disposition = .revoke) ∧
    (∃ entry ∈ bundle.publicationObligations, entry.disposition = .activate) := by
  cases bundle with
  | mk kind obligation witnessObligations effectObligations operationObligations publicationObligations lateResultPolicy =>
      cases kind <;> cases hKind
      exact hDelegation.2.2.2

theorem detach_bundle_invalidates_effects_or_reissues_operations
    {bundle : TransformationLocalObligationBundle}
    (hDetach : bundle.detachAdmissible)
    (hKind : bundle.kind = .detach) :
    (∀ entry ∈ bundle.effectObligations, entry.disposition = .invalidate) ∧
    (∀ entry ∈ bundle.operationObligations,
      entry.disposition = .detach ∨ entry.disposition = .reissue) := by
  cases bundle with
  | mk kind obligation witnessObligations effectObligations operationObligations publicationObligations lateResultPolicy =>
      cases kind <;> cases hKind
      exact ⟨hDetach.1, hDetach.2.1⟩

theorem link_bundle_preserves_or_transports_affected_effects
    {bundle : TransformationLocalObligationBundle}
    (hLink : bundle.linkAdmissible)
    (hKind : bundle.kind = .link) :
    ∀ entry ∈ bundle.effectObligations,
      entry.disposition = .preserve ∨ entry.disposition = .transport := by
  cases bundle with
  | mk kind obligation witnessObligations effectObligations operationObligations publicationObligations lateResultPolicy =>
      cases kind <;> cases hKind
      simpa [TransformationLocalObligationBundle.linkAdmissible] using hLink.1

theorem reconfiguration_bundle_explicit_for_all_affected
    {bundle : TransformationLocalObligationBundle}
    {objects : ProtocolMachineSemanticObjects}
    (hExplicit : bundle.explicitLocalBundle objects)
    (hReconfig : bundle.reconfigurationAdmissible)
    (hKind : bundle.kind = .reconfiguration) :
    bundle.explicitOperationHandling ∧
    bundle.explicitEffectHandling ∧
    bundle.explicitWitnessHandling objects ∧
    bundle.explicitPublicationHandling objects := by
  exact ⟨hExplicit.1, hExplicit.2.1, hExplicit.2.2.1, hExplicit.2.2.2.1⟩

/-! ## Linking / Reconfiguration Bridges -/

structure LinkLocalObligationBridge
    (bundle : TransformationLocalObligationBundle)
    (p₁ p₂ : DeployedProtocol) where
  kindLink : bundle.kind = .link
  explicitBundle : bundle.explicitOperationHandling ∧ bundle.explicitEffectHandling
  linkOK : LinkOK p₁ p₂

theorem link_bridge_linkOK
    {bundle : TransformationLocalObligationBundle}
    {p₁ p₂ : DeployedProtocol}
    (bridge : LinkLocalObligationBridge bundle p₁ p₂) :
    LinkOK p₁ p₂ :=
  bridge.linkOK

structure ReconfigurationLocalObligationBridge
    {State : Type u} {Obs : Type v}
    (bundle : TransformationLocalObligationBundle)
    (project : State → Obs)
    (globalStep : State → State → Prop)
    (localStep : Obs → Obs → Prop) where
  kindReconfiguration : bundle.kind = .reconfiguration
  explicitBundle :
    ∀ objects, bundle.explicitLocalBundle objects
  harmony : ReconfigurationHarmony project globalStep localStep

theorem reconfiguration_bridge_harmony
    {State : Type u} {Obs : Type v}
    {bundle : TransformationLocalObligationBundle}
    {project : State → Obs}
    {globalStep : State → State → Prop}
    {localStep : Obs → Obs → Prop}
    (bridge : ReconfigurationLocalObligationBridge bundle project globalStep localStep) :
    ReconfigurationHarmony project globalStep localStep :=
  bridge.harmony

end Runtime.VM.Model
