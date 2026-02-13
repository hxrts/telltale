import Runtime.Proofs.ObserverProjection
import Runtime.Proofs.EffectBisim.Bridge

/-! # Runtime.Proofs.ObserverProjectionEffectBisim

Effect-bisimulation bridge for coroutine-view observational equivalence.
-/

/-
The Problem. Observer-projection lemmas are stated in direct equality form
(`VMCEquiv`). We want a coinductive route so monitor/trace-level equivalence
arguments can be phrased as bisimulation + bridge.

Solution Structure. Define a coroutine-view observer on VM states, equip it with
a silent transition relation, and prove both directions:
`VMCEquiv -> EffectBisim` and `EffectBisim -> VMCEquiv`.
Then repackage topology-change noninterference through this bridge.
-/

set_option autoImplicit false

section

universe u

open Runtime.Proofs.EffectBisim

variable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

/-! ## Coroutine-View Observer -/

/-- Observer that exposes only coroutine-local view for a chosen coroutine id. -/
def vmViewObs (cid : CoroutineId) : EffectObs (VMState ι γ π ε ν) (Option CoroutineView) where
  observe := fun st => coroutineView st cid

/-- Silent transition relation used for observer-level bisimulation packaging. -/
def vmViewSilentStep : StateRel (VMState ι γ π ε ν) :=
  fun _ _ => False

private theorem vmViewEq_postfixed (cid : CoroutineId) :
    (fun st₁ st₂ : VMState ι γ π ε ν => coroutineView st₁ cid = coroutineView st₂ cid) ≤
      EffectBisimF (vmViewObs (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid)
        (vmViewSilentStep (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν))
        (fun st₁ st₂ : VMState ι γ π ε ν => coroutineView st₁ cid = coroutineView st₂ cid) := by
  intro st₁ st₂ hEq
  refine ⟨hEq, ?_, ?_⟩
  · intro st' hStep
    cases hStep
  · intro st' hStep
    cases hStep

/-! ## Bridge Theorems -/

/-- Any direct coroutine-view equivalence yields silent effect bisimulation. -/
theorem vmView_effectBisim_of_VMCEquiv
    (cid : CoroutineId)
    {st₁ st₂ : VMState ι γ π ε ν}
    (hEq : VMCEquiv st₁ st₂ cid) :
    EffectBisim
      (vmViewObs (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid)
      (vmViewSilentStep (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν))
      st₁ st₂ := by
  have hLift :
      (fun a b : VMState ι γ π ε ν => coroutineView a cid = coroutineView b cid) ≤
      EffectBisim
        (vmViewObs (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid)
        (vmViewSilentStep (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν)) :=
    SessionCoTypes.CoinductiveRel.coind
      (F := EffectBisimF
        (vmViewObs (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid)
        (vmViewSilentStep (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν)))
      (S := fun a b : VMState ι γ π ε ν => coroutineView a cid = coroutineView b cid)
      (vmViewEq_postfixed (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid)
  exact hLift _ _ hEq

/-- Any silent effect bisimulation at the view observer yields direct
    coroutine-view equivalence. -/
theorem vmCEquiv_of_vmView_effectBisim
    (cid : CoroutineId)
    {st₁ st₂ : VMState ι γ π ε ν}
    (hBisim :
      EffectBisim
        (vmViewObs (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid)
        (vmViewSilentStep (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν))
        st₁ st₂) :
    VMCEquiv st₁ st₂ cid := by
  exact effectBisim_implies_observationalEquivalence
    (vmViewObs (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid)
    (vmViewSilentStep (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν)) hBisim

/-! ## Topology Corollary via Bisimulation -/

/-- Topology-change noninterference restated via the effect-bisimulation bridge. -/
theorem topology_change_preserves_VMCEquiv_via_effectBisim
    (st : VMState ι γ π ε ν) (tc : TopologyChange (ι := ι)) (cid : CoroutineId) :
    VMCEquiv (applyTopologyChange st tc) st cid := by
  have hEq : VMCEquiv (applyTopologyChange st tc) st cid :=
    topology_change_preserves_VMCEquiv st tc cid
  have hBisim := vmView_effectBisim_of_VMCEquiv (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid hEq
  exact vmCEquiv_of_vmView_effectBisim (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) cid hBisim

end
