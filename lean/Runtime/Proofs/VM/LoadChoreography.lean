import Runtime.VM.Runtime.Loader

set_option autoImplicit false

universe u

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
  change (loadChoreography st image).2 ≠ sid'
  have hGe : st.nextSessionId ≤ (loadChoreography st image).2 :=
    loadChoreography_snd_ge_nextSessionId st image
  simp only [existingSessionIds, List.mem_map] at hMem
  obtain ⟨⟨sid'', sess⟩, hIn, rfl⟩ := hMem
  have hSess : ∀ s ∈ st.sessions, s.fst < st.nextSessionId := _hwf.2.1
  have hLt : sid'' < st.nextSessionId := hSess (sid'', sess) hIn
  have hLtLoaded : sid'' < (loadChoreography st image).2 := Nat.lt_of_lt_of_le hLt hGe
  exact (Nat.ne_of_lt hLtLoaded).symm
