import Runtime.VM.Runtime.Loader

set_option autoImplicit false

universe u

private lemma foldl_max_ge_start (xs : List Nat) (start : Nat) :
    start ≤ xs.foldl Nat.max start := by
  induction xs generalizing start with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl]
      exact Nat.le_trans (Nat.le_max_left start x) (ih (Nat.max start x))

private lemma nextFreshSessionId_ge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) :
    st.nextSessionId ≤ nextFreshSessionId st := by
  unfold nextFreshSessionId
  by_cases hAvail : sessionIdAvailable st st.nextSessionId
  · simp [hAvail]
  · simp [hAvail]
    exact Nat.le_trans
      (foldl_max_ge_start (existingSessionIds st) st.nextSessionId)
      (Nat.le_succ _)

theorem loadChoreography_snd_ge_nextSessionId
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : VMState ι γ π ε ν) (image : CodeImage γ ε) :
    st.nextSessionId ≤ (loadChoreography st image).2 := by
  cases hRes : loadChoreographyResult st image with
  | ok st' sid =>
      have hFresh : st.nextSessionId ≤ sid := by
        have hRes' : loadChoreographyResult st image = ChoreographyLoadResult.ok st' sid := hRes
        unfold loadChoreographyResult at hRes'
        split at hRes'
        · cases hRes'
        · split at hRes'
          · cases hRes'
          · split at hRes'
            · cases hRes'
            · cases hRes'
              simpa using (nextFreshSessionId_ge st)
      simpa [loadChoreography, hRes] using hFresh
  | validationFailed _ =>
      simp [loadChoreography, hRes]
  | tooManySessions _ =>
      simp [loadChoreography, hRes]
  | tooManyCoroutines _ =>
      simp [loadChoreography, hRes]

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
