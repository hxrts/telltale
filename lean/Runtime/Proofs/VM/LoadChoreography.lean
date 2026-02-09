import Runtime.VM.Runtime.Loader

set_option autoImplicit false

universe u

private lemma loadChoreography_snd {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : VMState ι γ π ε ν) (image : CodeImage γ ε) :
    (loadChoreography st image).2 = st.nextSessionId := by
  simp [loadChoreography]

theorem loadChoreography_disjoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : VMState ι γ π ε ν) (image : CodeImage γ ε)
    (_hwf : WFVMState st) :
    let (st', sid) := loadChoreography st image
    ∀ sid' ∈ existingSessionIds st, SessionDisjoint st' sid sid' := by
  intro sid' hMem
  show (loadChoreography st image).2 ≠ sid'
  rw [loadChoreography_snd]
  simp only [existingSessionIds, List.mem_map] at hMem
  obtain ⟨⟨sid'', sess⟩, hIn, rfl⟩ := hMem
  have ⟨_, hSess⟩ := _hwf
  have hLt : sid'' < st.nextSessionId := hSess (sid'', sess) hIn
  change st.nextSessionId ≠ sid''
  exact (Nat.ne_of_lt hLt).symm
