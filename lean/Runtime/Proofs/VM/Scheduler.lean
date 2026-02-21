import Runtime.VM.Runtime.Scheduler

set_option autoImplicit false

/-! # VM Scheduler Properties

Proofs of scheduler correctness properties: confluence, cooperative refinement,
and helper lemmas for queue operations. -/

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

/-! ## Cooperative Refinement -/

theorem cooperative_refines_concurrent_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : cooperative_refines_concurrent st := by
  intro hcoop
  let st' : VMState ι γ π ε ν := { st with sched := syncLaneViews st.sched }
  have hPolicy : st'.sched.policy = .cooperative := by
    simpa [st', syncLaneViews] using hcoop
  have hEq :
      pickRunnableInQueue st'.sched.policy st' st'.sched.readyQueue =
        pickRunnableInQueue .cooperative st' st'.sched.readyQueue := by
    simp [hPolicy]
  rw [hEq]
  simp [st', pickRunnableInQueue]

theorem single_lane_schedule_compat_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (laneOf' : LaneOfMap)
    (laneQueues' : LaneQueueMap)
    (laneBlocked' : LaneBlockedMap γ)
    (handoffs' : List CrossLaneHandoff)
    (hLaneOf : laneOf' = st.sched.laneOf)
    (hLaneQueues : laneQueues' = st.sched.laneQueues)
    (hLaneBlocked : laneBlocked' = st.sched.laneBlocked)
    (hHandoffs : handoffs' = st.sched.crossLaneHandoffs) :
    single_lane_schedule_compat st laneOf' laneQueues' laneBlocked' handoffs' := by
  subst hLaneOf
  subst hLaneQueues
  subst hLaneBlocked
  subst hHandoffs
  rfl

theorem policy_selection_deterministic_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : VMState ι γ π ε ν) :
    policy_selection_deterministic policy st := by
  intro _ st1 st2 h1 h2
  exact Option.some.inj (h1.symm.trans h2)

/-! ## Queue Extraction Helpers -/

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

/-! ## Best-Candidate Helpers -/

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

/-! ## Priority Pick Helpers -/

private theorem pickBest_some_of_exists (queue : SchedQueue) (score : CoroutineId → Nat)
    (p : CoroutineId → Bool)
    (hExists : ∃ cid, cid ∈ queue ∧ p cid = true) :
    ∃ cid rest, pickBest queue score p = some (cid, rest) := by
  rcases bestCandidate_some_of_exists queue score p hExists with ⟨cid, hBest⟩
  refine ⟨cid, removeFirst cid queue, ?_⟩
  simp [pickBest, hBest]

/-! ## Runnable Pick In Queue -/

private theorem pickRunnableInQueue_some_of_mem_runnable
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : VMState ι γ π ε ν) (queue : SchedQueue)
    (cid : CoroutineId) (hmem : cid ∈ queue) (hrun : isRunnable st cid = true) :
    ∃ found rest, pickRunnableInQueue policy st queue = some (found, rest) := by
  cases policy with
  | roundRobin =>
      simpa [pickRunnableInQueue, pickRoundRobinInQueue] using
        takeOut_some_of_mem queue (fun cid' => isRunnable st cid') cid hmem hrun
  | cooperative =>
      simpa [pickRunnableInQueue, pickRoundRobinInQueue] using
        takeOut_some_of_mem queue (fun cid' => isRunnable st cid') cid hmem hrun
  | priority f =>
      have hExists : ∃ cid', cid' ∈ queue ∧ isRunnable st cid' = true := ⟨cid, hmem, hrun⟩
      simpa [pickRunnableInQueue, pickPriorityInQueue] using
        pickBest_some_of_exists queue f (fun cid' => isRunnable st cid') hExists
  | progressAware =>
      cases hTok : takeOut queue (fun cid' => isRunnable st cid' && hasProgress st cid') with
      | none =>
          obtain ⟨found, rest, hRR⟩ :=
            takeOut_some_of_mem queue (fun cid' => isRunnable st cid') cid hmem hrun
          refine ⟨found, rest, ?_⟩
          simp [pickRunnableInQueue, pickProgressInQueue, hTok, hRR, pickRoundRobinInQueue]
      | some pair =>
          refine ⟨pair.1, pair.2, ?_⟩
          simp [pickRunnableInQueue, pickProgressInQueue, hTok]

/-! ## Runnable Pick From Scheduler -/

private theorem pickRunnableFromSched_some_of_mem_runnable
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (policy : SchedPolicy) (st : VMState ι γ π ε ν) (sched : SchedState γ)
    (cid : CoroutineId) (hmem : cid ∈ sched.readyQueue) (hrun : isRunnable st cid = true) :
    ∃ found rest, pickRunnableFromSched policy st sched = some (found, rest) := by
  have hQueue :
      ∃ found rest, pickRunnableInQueue policy st sched.readyQueue = some (found, rest) :=
    pickRunnableInQueue_some_of_mem_runnable policy st sched.readyQueue cid hmem hrun
  unfold pickRunnableFromSched
  set lanes : List LaneId := orderedLaneIds sched
  set start : Nat := if lanes.isEmpty then 0 else (sched.stepCount + 1) % lanes.length
  cases hLane : pickLaneAux policy st sched lanes start 0 lanes.length with
  | none =>
      rcases hQueue with ⟨found, rest, hQueueSome⟩
      refine ⟨found, removeFirst found sched.readyQueue, ?_⟩
      change
        (match pickLaneAux policy st sched lanes start 0 lanes.length with
        | some cid => some (cid, removeFirst cid sched.readyQueue)
        | none =>
            match pickRunnableInQueue policy st sched.readyQueue with
            | some (cid, _) => some (cid, removeFirst cid sched.readyQueue)
            | none => none) = some (found, removeFirst found sched.readyQueue)
      simp [hLane, hQueueSome]
  | some picked =>
      refine ⟨picked, removeFirst picked sched.readyQueue, ?_⟩
      change
        (match pickLaneAux policy st sched lanes start 0 lanes.length with
        | some cid => some (cid, removeFirst cid sched.readyQueue)
        | none =>
            match pickRunnableInQueue policy st sched.readyQueue with
            | some (cid, _) => some (cid, removeFirst cid sched.readyQueue)
            | none => none) = some (picked, removeFirst picked sched.readyQueue)
      simp [hLane]

/-! ## Runnable Pick From VM State -/

private theorem pickRunnable_some_of_mem_runnable
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId)
    (hmem : cid ∈ st.sched.readyQueue) (hrun : isRunnable st cid = true) :
    ∃ found rest, pickRunnable st = some (found, rest) := by
  let sched : SchedState γ := syncLaneViews st.sched
  let st' : VMState ι γ π ε ν := { st with sched := sched }
  have hmem' : cid ∈ sched.readyQueue := by
    simpa [sched, syncLaneViews] using hmem
  have hrun' : isRunnable st' cid = true := by
    simp [st', isRunnable, getCoro] at hrun ⊢
    exact hrun
  obtain ⟨found, rest, hFromSched⟩ :=
    pickRunnableFromSched_some_of_mem_runnable st'.sched.policy st' sched cid hmem' hrun'
  refine ⟨found, rest, ?_⟩
  unfold pickRunnable
  simpa [sched, st'] using hFromSched

/-! ## Starvation Freedom -/

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
    let stNorm : VMState ι γ π ε ν := { st with sched := syncLaneViews st.sched }
    have hmemNorm : cid ∈ stNorm.sched.readyQueue := by
      simpa [stNorm, syncLaneViews] using hmem
    have hrunNorm : isRunnable stNorm cid = true := by
      simpa [stNorm, isRunnable, getCoro] using hrun
    obtain ⟨found, rest, hPick⟩ := pickRunnable_some_of_mem_runnable stNorm cid hmemNorm hrunNorm
    have hsched : ∃ st', schedule st = some (found, st') := by
      unfold schedule
      simp [stNorm, hPick]
    rcases hsched with ⟨st', hs⟩
    exact ⟨found, st', hs⟩
