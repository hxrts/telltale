import Protocol.Deployment.Part2
import Protocol.Typing.Part3
import Protocol.Coherence.Part9

/-! # Protocol.Deployment.Part3

Linking theorems and composition preservation results.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Linking Theorems -/

axiom mergeBufs_typed (G₁ G₂ : GEnv) (D₁ D₂ : DEnv) (B₁ B₂ : Buffers)
    (hTyped₁ : BuffersTyped G₁ D₁ B₁)
    (hTyped₂ : BuffersTyped G₂ D₂ B₂)
    (hDisjG : DisjointG G₁ G₂)
    (hConsD₂ : DConsistent G₂ D₂)
    (hConsB₁ : BConsistent G₁ B₁)
    (hDom₁ : BufsDom B₁ D₁) :
    BuffersTyped (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂)

axiom mergeLin_valid (G₁ G₂ : GEnv) (L₁ L₂ : LinCtx)
    (hValid₁ : ∀ e S, (e, S) ∈ L₁ → lookupG G₁ e = some S)
    (hValid₂ : ∀ e S, (e, S) ∈ L₂ → lookupG G₂ e = some S)
    (hDisjointG : DisjointG G₁ G₂) :
    ∀ e S, (e, S) ∈ mergeLin L₁ L₂ → lookupG (mergeGEnv G₁ G₂) e = some S

axiom mergeLin_unique (L₁ L₂ : LinCtx)
    (hUnique₁ : L₁.Pairwise (fun a b => a.1 ≠ b.1))
    (hUnique₂ : L₂.Pairwise (fun a b => a.1 ≠ b.1))
    (hDisjoint : ∀ e, (∃ S, (e, S) ∈ L₁) → ∀ S', (e, S') ∉ L₂) :
    (mergeLin L₁ L₂).Pairwise (fun a b => a.1 ≠ b.1)

axiom link_preserves_WTMon_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState)

axiom link_preserves_WTMon (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState)

axiom link_preserves_WTMon_complete (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState)

axiom link_preserves_WTMon_complete_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState)

axiom disjoint_sessions_independent (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂) :
    p₁.sessionId ≠ p₂.sessionId

axiom compose_deadlock_free (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂)
    (hDF₁ : ∀ r, r ∈ p₁.roles → ReachesComm (p₁.localTypes r))
    (hDF₂ : ∀ r, r ∈ p₂.roles → ReachesComm (p₂.localTypes r)) :
    ∀ r, r ∈ p₁.roles ++ p₂.roles →
      ReachesComm ((composeBundle (ProtocolBundle.fromDeployed p₁) (ProtocolBundle.fromDeployed p₂)).localTypes r)
