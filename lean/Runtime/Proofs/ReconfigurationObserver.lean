import Protocol.Deployment.LinkingTheorems
import Runtime.Proofs.ObserverProjection
import Runtime.Proofs.EffectBisim.Bridge
import Runtime.Proofs.ProtocolMachine.SemanticObjects.AuthoritativeReadsPublication
import Runtime.Proofs.ProtocolMachine.SemanticObjects.CrossTargetProgressDependentWork
import Runtime.Proofs.ProtocolMachine.SemanticObjects.ReplayFailureExactness
import Runtime.Proofs.ProtocolMachine.SemanticObjects.SemanticHandoff
import Runtime.Proofs.ProtocolMachine.SemanticObjects.TransformationLocalObligations
import Runtime.Proofs.SessionLocal

set_option autoImplicit false

/-! # Runtime.Proofs.ReconfigurationObserver

Canonical proof-facing surface for reconfiguration, region layering, and
observer semantics.

This module is the intended target-facing facade for language features that need
to talk about linking, delegation, reconfiguration harmony, observer
equivalence, canonical publication paths, and replay/cross-target observer
alignment without depending on scattered lower-level theorem files.
-/

namespace Runtime
namespace Proofs

open Runtime.Adequacy
open Runtime.ProtocolMachine.Model
open Runtime.Proofs.EffectBisim

universe u v

/-! ## Region Layering -/

/-- Execution-side region facts: session-locality, delegation blindness, and
linking-preserved locality. -/
structure ExecutionRegion where
  session : SessionId
  locality : Prop
  delegationBlindness : Prop
  linkingLocality : Prop

/-- Authority-side region facts: canonical publication uniqueness, exclusivity,
and observer separation. -/
structure AuthorityRegion where
  ownerId : Option String
  canonicalPublicationPath : Prop
  canonicalPublicationExclusivity : Prop
  observerSeparation : Prop

/-- Region layering for the proof system: execution region + authority region. -/
structure Region where
  execution : ExecutionRegion
  authority : AuthorityRegion

/-- Build the execution-side region witness induced by one delegation step. -/
def executionRegionOfDelegation
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B) : ExecutionRegion :=
  { session := s
  , locality := SessionCoherent G' D' s
  , delegationBlindness :=
      ∀ sOther, sOther ≠ s →
        (∀ ep : Endpoint, ep.sid = sOther → lookupG G' ep = lookupG G ep) ∧
        (∀ e : Edge, e.sid = sOther → lookupD D' e = lookupD D e)
  , linkingLocality := ∀ sOther, sOther ≠ s → SessionCoherent G' D' sOther
  }

/-- Build the authority-side region witness induced by one commitment context. -/
def authorityRegionOfCommitment
    (objects : ProtocolMachineSemanticObjects)
    (ctx : AuthoritativeCommitmentContext) : AuthorityRegion :=
  { ownerId := ctx.ownerId
  , canonicalPublicationPath := objects.canonicalPublicationPathUnique
  , canonicalPublicationExclusivity := objects.canonicalPublicationSurfaceExclusive
  , observerSeparation := objects.observedStateCannotAuthorTruth ctx
  }

/-- Canonical region layering surface combining execution and authority facts. -/
def regionOfCommitmentAndDelegation
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B)
    (objects : ProtocolMachineSemanticObjects)
    (ctx : AuthoritativeCommitmentContext) : Region :=
  { execution := executionRegionOfDelegation hCoh hDeleg
  , authority := authorityRegionOfCommitment objects ctx
  }

theorem execution_region_locality_of_delegation
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B) :
    (executionRegionOfDelegation hCoh hDeleg).locality ∧
    (executionRegionOfDelegation hCoh hDeleg).linkingLocality := by
  constructor
  · exact (delegation_harmony_split hCoh hDeleg).1
  · intro sOther hDiff
    exact (delegation_harmony_split hCoh hDeleg).2 sOther hDiff

theorem execution_region_blindness_of_delegation
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B) :
    (executionRegionOfDelegation hCoh hDeleg).delegationBlindness := by
  intro sOther hDiff
  constructor
  · intro ep hSid
    exact delegation_blind_endpoint_lookup hDeleg hDiff ep hSid
  · intro e hSid
    exact delegation_blind_trace_lookup hDeleg hDiff e hSid

/-! ## Observer / Effect-Bisim Bridge -/

variable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

/-- Observer that exposes only coroutine-local view for a chosen coroutine id. -/
def coroutineViewObs
    (cid : CoroutineId) :
    EffectObs (ProtocolMachineState ι γ π ε ν) (Option CoroutineView) where
  observe := fun st => coroutineView st cid

/-- Silent transition relation used for observer-level bisimulation packaging. -/
def coroutineViewSilentStep : StateRel (ProtocolMachineState ι γ π ε ν) :=
  fun _ _ => False

private theorem coroutine_view_eq_postfixed (cid : CoroutineId) :
    (fun st₁ st₂ : ProtocolMachineState ι γ π ε ν => coroutineView st₁ cid = coroutineView st₂ cid) ≤
      EffectBisimF (coroutineViewObs (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid)
        (coroutineViewSilentStep (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν))
        (fun st₁ st₂ : ProtocolMachineState ι γ π ε ν => coroutineView st₁ cid = coroutineView st₂ cid) := by
  intro st₁ st₂ hEq
  refine ⟨hEq, ?_, ?_⟩
  · intro st' hStep
    cases hStep
  · intro st' hStep
    cases hStep

theorem effect_bisim_of_coroutine_view_equiv
    (cid : CoroutineId)
    {st₁ st₂ : ProtocolMachineState ι γ π ε ν}
    (hEq : CoroutineViewEquiv st₁ st₂ cid) :
    EffectBisim
      (coroutineViewObs (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid)
      (coroutineViewSilentStep (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν))
      st₁ st₂ := by
  have hLift :
      (fun a b : ProtocolMachineState ι γ π ε ν => coroutineView a cid = coroutineView b cid) ≤
      EffectBisim
        (coroutineViewObs (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid)
        (coroutineViewSilentStep (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν)) :=
    SessionCoTypes.CoinductiveRel.coind
      (F := EffectBisimF
        (coroutineViewObs (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid)
        (coroutineViewSilentStep (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν)))
      (S := fun a b : ProtocolMachineState ι γ π ε ν => coroutineView a cid = coroutineView b cid)
      (coroutine_view_eq_postfixed (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid)
  exact hLift _ _ hEq

theorem coroutine_view_equiv_of_effect_bisim
    (cid : CoroutineId)
    {st₁ st₂ : ProtocolMachineState ι γ π ε ν}
    (hBisim :
      EffectBisim
        (coroutineViewObs (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid)
        (coroutineViewSilentStep (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν))
        st₁ st₂) :
    CoroutineViewEquiv st₁ st₂ cid := by
  exact effect_bisim_implies_observational_equivalence
    (coroutineViewObs (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid)
    (coroutineViewSilentStep (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν)) hBisim

theorem topology_change_preserves_coroutine_view_equiv_via_effect_bisim
    (st : ProtocolMachineState ι γ π ε ν) (tc : TopologyChange (ι := ι)) (cid : CoroutineId) :
    CoroutineViewEquiv (applyTopologyChange st tc) st cid := by
  have hEq : CoroutineViewEquiv (applyTopologyChange st tc) st cid :=
    topology_change_preserves_coroutine_view_equiv st tc cid
  have hBisim :=
    effect_bisim_of_coroutine_view_equiv (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid hEq
  exact coroutine_view_equiv_of_effect_bisim (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) cid hBisim

/-! ## Reconfiguration / Observer Facade Theorems -/

theorem link_harmony_preserves_monitor
    (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState) :=
  link_harmony_through_link p₁ p₂ hLink hDisjG hWT₁ hWT₂

theorem delegation_preserves_composed_coherence
    (p₁ p₂ : DeployedProtocol)
    (G₁' : GEnv) (D₁' : DEnv)
    (s : SessionId) (A B : Role)
    (hLink : LinkOKFull p₁ p₂)
    (hDeleg : DelegationStep p₁.initGEnv G₁' p₁.initDEnv D₁' s A B)
    (hDisjG' : DisjointG G₁' p₂.initGEnv)
    (hCons₁' : DConsistent G₁' D₁') :
    Coherent (mergeGEnv p₁.initGEnv p₂.initGEnv) (mergeDEnv p₁.initDEnv p₂.initDEnv) ∧
      Coherent (mergeGEnv G₁' p₂.initGEnv) (mergeDEnv D₁' p₂.initDEnv) :=
  delegation_in_composed_systems p₁ p₂ G₁' D₁' s A B hLink hDeleg hDisjG' hCons₁'

theorem reconfiguration_harmony_of_local_obligation_bridge
    {State : Type u} {Obs : Type v}
    {bundle : TransformationLocalObligationBundle}
    {project : State → Obs}
    {globalStep : State → State → Prop}
    {localStep : Obs → Obs → Prop}
    (bridge : ReconfigurationLocalObligationBridge bundle project globalStep localStep) :
    ReconfigurationHarmony project globalStep localStep :=
  reconfiguration_bridge_harmony bridge

theorem audit_publication_preserves_canonical_observer_projection
    (objects : ProtocolMachineSemanticObjects)
    (event : PublicationEvent)
    (hAudit : event.observerClass = .audit) :
    ProtocolMachineSemanticObjects.observerPublicationProjection
        { objects with publicationEvents := event :: objects.publicationEvents }
        .canonical =
      objects.observerPublicationProjection .canonical :=
  audit_publication_blind_to_canonical_projection objects event hAudit

theorem replay_failure_exactness_preserves_observer_audit
    {objects : ProtocolMachineSemanticObjects}
    {ctx : ReplayFailureContext}
    (hAligned : objects.replayFailureConformanceAligned ctx) :
    objects.failureAuditAligned ctx :=
  replayFailureConformanceAligned_includes_audit_alignment hAligned

theorem cross_target_terminal_progress_preserves_canonical_publication_left
    {objects : ProtocolMachineSemanticObjects}
    {left right : RealizedProgressView}
    (hPreserved : objects.crossTargetProgressPreserved left right)
    (hTerminal : left.contract.isTerminal) :
    objects.hasCanonicalTerminalPublicationFor
      left.contract.operationId left.contract.session :=
  crossTargetProgressPreserved_left_terminal_has_canonical_publication hPreserved hTerminal

theorem cross_target_terminal_progress_preserves_canonical_publication_right
    {objects : ProtocolMachineSemanticObjects}
    {left right : RealizedProgressView}
    (hPreserved : objects.crossTargetProgressPreserved left right)
    (hTerminal : right.contract.isTerminal) :
    objects.hasCanonicalTerminalPublicationFor
      right.contract.operationId right.contract.session :=
  crossTargetProgressPreserved_right_terminal_has_canonical_publication hPreserved hTerminal

end Proofs
end Runtime
