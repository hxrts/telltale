import Runtime.VM.Runtime.Scheduler

set_option autoImplicit false

/-!
# VM Scheduler Properties

Proofs of scheduler correctness properties: confluence, cooperative refinement,
and helper lemmas for queue operations.
-/

/-
The Problem. The VM scheduler must satisfy confluence (order of ready coroutines
doesn't affect reachable states) and cooperative scheduling must refine concurrent
semantics. These properties underpin deterministic execution guarantees.

Solution Structure. Proves `schedule_confluence_holds` showing the scheduler is
confluent, and `cooperative_refines_concurrent_holds` showing cooperative mode
refines round-robin. Helper lemmas for queue operations (takeOut, bestCandidate)
support the main proofs.
-/

universe u

/-! ## Scheduler Properties -/

theorem schedule_confluence_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : schedule_confluence st :=
  fun _ _ h1 h2 => by
    have := h1.symm.trans h2
    exact Option.some.inj this

theorem cooperative_refines_concurrent_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : cooperative_refines_concurrent st := by
  intro hcoop
  have hRound :
      pickRoundRobin { st with sched := { st.sched with policy := .roundRobin } } = pickRoundRobin st := by
    simp [pickRoundRobin, isRunnable, getCoro]
  simp [schedule, pickRunnable, hcoop, hRound]
  cases hPick : pickRoundRobin st <;> simp

private theorem takeOut_some_of_mem (queue : SchedQueue) (p : CoroutineId → Bool)
    (cid : CoroutineId) (hmem : cid ∈ queue) (hp : p cid = true) :
    ∃ cid' rest, takeOut queue p = some (cid', rest) := by
  induction queue with
  | nil => simp at hmem
  | cons hd tl ih =>
    unfold takeOut
    split
    · exact ⟨hd, tl, rfl⟩
    · next hphd =>
      cases hmem with
      | head => exact absurd hp hphd
      | tail _ hmem' =>
        obtain ⟨found, rest, heq⟩ := ih hmem'
        rw [heq]
        exact ⟨found, hd :: rest, rfl⟩

private theorem bestCandidate_some_of_exists (queue : SchedQueue) (score : CoroutineId → Nat)
    (p : CoroutineId → Bool)
    (hExists : ∃ cid, cid ∈ queue ∧ p cid = true) :
    ∃ cid, bestCandidate queue score p = some cid := by
  induction queue with
  | nil =>
    rcases hExists with ⟨cid, hmem, _⟩
    cases hmem
  | cons hd tl ih =>
    rcases hExists with ⟨cid, hmem, hp⟩
    by_cases hHd : p hd = true
    · cases hBestTl : bestCandidate tl score p with
      | none =>
        refine ⟨hd, ?_⟩
        simp [bestCandidate, hHd, hBestTl]
      | some best =>
        by_cases hScore : score hd ≥ score best
        · refine ⟨hd, ?_⟩
          simp [bestCandidate, hHd, hBestTl, hScore]
        · refine ⟨best, ?_⟩
          simp [bestCandidate, hHd, hBestTl, hScore]
    · have hmemTl : cid ∈ tl := by
        cases hmem with
        | head =>
          exfalso
          exact hHd hp
        | tail _ h => exact h
      have hExistsTl : ∃ cid, cid ∈ tl ∧ p cid = true := ⟨cid, hmemTl, hp⟩
      rcases ih hExistsTl with ⟨cid', hBestTl⟩
      refine ⟨cid', ?_⟩
      simp [bestCandidate, hHd, hBestTl]

private theorem pickBest_some_of_exists (queue : SchedQueue) (score : CoroutineId → Nat)
    (p : CoroutineId → Bool)
    (hExists : ∃ cid, cid ∈ queue ∧ p cid = true) :
    ∃ cid rest, pickBest queue score p = some (cid, rest) := by
  rcases bestCandidate_some_of_exists queue score p hExists with ⟨cid, hBest⟩
  refine ⟨cid, removeFirst cid queue, ?_⟩
  simp [pickBest, hBest]

theorem starvation_free_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : starvation_free st := by
  intro cid hmem
  match hcoro : st.coroutines[cid]? with
  | none => exact trivial
  | some c =>
    intro hstatus
    have hrun : isRunnable st cid = true := by
      simp only [isRunnable, getCoro, hcoro, runnable]
      cases hstatus with
      | inl h => rw [h]
      | inr h => rw [h]
    have hExistsRunnable : ∃ cid', cid' ∈ st.sched.readyQueue ∧ isRunnable st cid' = true :=
      ⟨cid, hmem, hrun⟩
    cases hPol : st.sched.policy with
    | roundRobin =>
      obtain ⟨found, rest, hTake⟩ :=
        takeOut_some_of_mem _ _ _ hmem hrun
      refine ⟨found, { st with sched := { st.sched with readyQueue := rest, stepCount := st.sched.stepCount + 1 } }, ?_⟩
      simp [schedule, pickRunnable, hPol, pickRoundRobin, hTake]
    | cooperative =>
      obtain ⟨found, rest, hTake⟩ :=
        takeOut_some_of_mem _ _ _ hmem hrun
      refine ⟨found, { st with sched := { st.sched with readyQueue := rest, stepCount := st.sched.stepCount + 1 } }, ?_⟩
      simp [schedule, pickRunnable, hPol, pickRoundRobin, hTake]
    | progressAware =>
      by_cases hToken :
          ∃ found rest,
            takeOut st.sched.readyQueue (fun cid' => isRunnable st cid' && hasProgress st cid') = some (found, rest)
      · rcases hToken with ⟨found, rest, hTake⟩
        refine ⟨found, { st with sched := { st.sched with readyQueue := rest, stepCount := st.sched.stepCount + 1 } }, ?_⟩
        simp [schedule, pickRunnable, hPol, pickProgress, hTake]
      · have hTokenNone :
            takeOut st.sched.readyQueue (fun cid' => isRunnable st cid' && hasProgress st cid') = none := by
          cases hTake :
              takeOut st.sched.readyQueue (fun cid' => isRunnable st cid' && hasProgress st cid') with
          | none => exact rfl
          | some v =>
            exfalso
            exact hToken ⟨v.1, v.2, hTake⟩
        obtain ⟨found, rest, hTakeRR⟩ :=
          takeOut_some_of_mem _ _ _ hmem hrun
        refine ⟨found, { st with sched := { st.sched with readyQueue := rest, stepCount := st.sched.stepCount + 1 } }, ?_⟩
        simp [schedule, pickRunnable, hPol, pickProgress, hTokenNone, pickRoundRobin, hTakeRR]
    | priority f =>
      obtain ⟨found, rest, hPickBest⟩ :=
        pickBest_some_of_exists st.sched.readyQueue f (fun cid' => isRunnable st cid') hExistsRunnable
      refine ⟨found, { st with sched := { st.sched with readyQueue := rest, stepCount := st.sched.stepCount + 1 } }, ?_⟩
      simp [schedule, pickRunnable, hPol, pickPriority, hPickBest]
