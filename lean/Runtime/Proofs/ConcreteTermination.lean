import Runtime.Proofs.ProgressTheorems
import Runtime.ProtocolMachine.Semantics.ExecHelpers

/-! # Runtime.Proofs.ConcreteTermination

A concrete, role-indexed session-store step and its fair-termination ranking.

`frontierAction store ep` performs the frontier action of endpoint `ep` on the
store exactly as the machine's commit stages do at the type level: a `send`
advances the type and appends `T` to the outgoing trace; a `recv` with a
matching trace head advances the type and pops the head; a `select` offers its
first branch and appends `.string`; a `branch` whose buffer head is a known
label advances to that branch, pops the trace head and dequeues the buffer.
`roleStep roles store r` runs the first enabled endpoint of role `roles[r]`.

Measure: `protocolMachineTypeMeasure` (sum of `progressMeasure` over all
endpoint types). Every frontier action strictly decreases it and nothing else
changes it, so the `FairRanking` obligations `nonincreasing`,
`enabled_decreases` and `enabled_stable` are discharged outright
(`concreteRanking`). The one residual obligation is `progress`;
`concreteRanking_of_frontier` takes it as the explicit hypothesis
`∀ s, ¬ AllSessionsComplete s → FrontierEnabled s` together with role coverage.
That hypothesis is false for arbitrary stores; it is discharged for projected
straight-line stores in `ProjectedProgress.lean` (`progress_of_projected`) and
the resulting hypothesis-free termination theorem is
`concrete_termination_of_projected` in `ProjectedTermination.lean`.

Why not `ProtocolMachineTerminationModel` (stated honestly): that structure
fixes the measure to `protocolMachineMeasure = types + traces`. A `send` or
`select` step lowers the type component by exactly one and raises the trace
component by one, so it does not strictly decrease that measure, while any
`Enabled` excluding outputs makes `progress` false for a store whose only
pending actions are outputs. The structure's measure is therefore unsuitable
for the asynchronous step; the ranking below uses the type component alone,
which `FairRanking.fair_termination` accepts directly.
-/

/-
The Problem. `ProgressTheorems` leaves the termination model uninstantiated.

Solution Structure. Express the type measure as a per-session sum, prove the
`updateG` sum identity, lift it through `updateType`/`updateTrace`, and derive
the ranking fields from "every step is the identity or strictly decreasing".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

section

universe u
variable {ν : Type u} [VerificationModel ν]

/-! ## Concrete step -/

/-- Dequeue the head of `edge`'s signed buffer inside its session (no-op if empty). -/
def SessionStore.dequeueBuffer : SessionStore ν → Edge → SessionStore ν
  | [], _ => []
  | (sid, s) :: rest, edge =>
      if sid = edge.sid then
        (sid, { s with buffers := match bufDequeue s.buffers edge with
          | some (_, b') => b'
          | none => s.buffers }) :: rest
      else (sid, s) :: SessionStore.dequeueBuffer rest edge

/-- The frontier action of endpoint `ep` on the store, if enabled. -/
def frontierAction (store : SessionStore ν) (ep : Endpoint) : Option (SessionStore ν) :=
  match SessionStore.lookupType store ep with
  | some (.send target T L') =>
      let edge : Edge := { sid := ep.sid, sender := ep.role, receiver := target }
      some ((store.updateType ep L').updateTrace edge (SessionStore.lookupTrace store edge ++ [T]))
  | some (.recv source T L') =>
      let edge : Edge := { sid := ep.sid, sender := source, receiver := ep.role }
      match SessionStore.lookupTrace store edge with
      | T' :: rest => if T' = T then some ((store.updateType ep L').updateTrace edge rest) else none
      | [] => none
  | some (.select target bs) =>
      match bs with
      | (_, L') :: _ =>
          let edge : Edge := { sid := ep.sid, sender := ep.role, receiver := target }
          some ((store.updateType ep L').updateTrace edge
            (SessionStore.lookupTrace store edge ++ [.string]))
      | [] => none
  | some (.branch source bs) =>
      let edge : Edge := { sid := ep.sid, sender := source, receiver := ep.role }
      match SessionStore.lookupBuffer store edge with
      | .string ℓ :: _ =>
          match bs.find? (fun b => b.1 == ℓ) with
          | some (_, L') =>
              some (((store.updateType ep L').updateTrace edge
                (SessionStore.lookupTrace store edge).tail).dequeueBuffer edge)
          | none => none
      | _ => none
  | _ => none

/-- Role-indexed step: the first enabled endpoint of role `roles[r]`, scanning
sessions in store order; identity when nothing is enabled. -/
def roleStep (roles : List Role) (store : SessionStore ν) (r : Nat) : SessionStore ν :=
  match roles[r]? with
  | none => store
  | some role =>
      match (store.map (·.1)).findSome? (fun sid => frontierAction store ⟨sid, role⟩) with
      | some store' => store'
      | none => store

/-! ## The type measure as a per-session sum -/

/-- Type measure of one session. -/
def sessionTypeSum (s : SessionState ν) : Nat :=
  (s.localTypes.map (fun p => p.2.progressMeasure)).sum

/-- Type measure of a store as a sum over sessions. -/
def storeTypeSum (store : SessionStore ν) : Nat :=
  (store.map (fun p => sessionTypeSum p.2)).sum

/-- `foldl (· + ·)` from an accumulator is the accumulator plus the sum. -/
theorem foldl_add_eq_add_sum (l : List Nat) : ∀ a, l.foldl (· + ·) a = a + l.sum := by
  induction l with
  | nil => intro a; simp
  | cons x xs ih => intro a; simp only [List.foldl, List.sum_cons, ih]; omega

/-- Flattening the sessions' type lists sums their per-session sums. -/
theorem sum_map_foldl_append (store : SessionStore ν) :
    ∀ init : GEnv,
      ((store.foldl (fun acc p => acc ++ p.2.localTypes) init).map
        (fun p => p.2.progressMeasure)).sum = (init.map (fun p => p.2.progressMeasure)).sum +
        storeTypeSum store := by
  induction store with
  | nil => intro init; simp [storeTypeSum]
  | cons p rest ih =>
    intro init
    simp only [List.foldl, storeTypeSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, List.map_append, List.sum_append]
    simp only [storeTypeSum, sessionTypeSum]
    omega

/-- `protocolMachineTypeMeasure` is the per-session sum. -/
theorem typeMeasure_eq_storeTypeSum (store : SessionStore ν) :
    protocolMachineTypeMeasure store = storeTypeSum store := by
  unfold protocolMachineTypeMeasure SessionStore.toGEnv
  rw [foldl_add_eq_add_sum, sum_map_foldl_append]
  simp

/-! ## Sum identities for updates -/

/-- `storeTypeSum` on a cons. -/
theorem storeTypeSum_cons (p : SessionId × SessionState ν) (rest : SessionStore ν) :
    storeTypeSum (p :: rest) = sessionTypeSum p.2 + storeTypeSum rest := by
  simp [storeTypeSum]

/-- Updating an existing entry of a `GEnv` exchanges its measure. -/
theorem sum_updateG_some (env : GEnv) (e : Endpoint) (L old : LocalType)
    (h : lookupG env e = some old) :
    ((updateG env e L).map (fun p => p.2.progressMeasure)).sum + old.progressMeasure =
      (env.map (fun p => p.2.progressMeasure)).sum + L.progressMeasure := by
  induction env with
  | nil => simp [lookupG] at h
  | cons q rest ih =>
    obtain ⟨e', L'⟩ := q
    by_cases he : e = e'
    · subst he
      have hold : L' = old := by simpa [lookupG] using h
      subst hold
      simp only [updateG, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · have hb : (e == e') = false := beq_false_of_ne he
      have h' : lookupG rest e = some old := by simpa [lookupG, List.lookup_cons, hb] using h
      have := ih h'
      simp only [updateG, he, ↓reduceIte, List.map_cons, List.sum_cons]
      omega

/-- A session type update exchanges the measure of the looked-up type. -/
theorem storeTypeSum_updateType {store : SessionStore ν} {ep : Endpoint} {L old : LocalType}
    (h : SessionStore.lookupType store ep = some old) :
    storeTypeSum (store.updateType ep L) + old.progressMeasure =
      storeTypeSum store + L.progressMeasure := by
  induction store with
  | nil => simp [SessionStore.lookupType] at h
  | cons p rest ih =>
    obtain ⟨sid, s⟩ := p
    by_cases hs : sid = ep.sid
    · subst hs
      have h' : lookupG s.localTypes ep = some old := by
        simpa [SessionStore.lookupType, SessionState.lookupType, lookupG] using h
      have := sum_updateG_some s.localTypes ep L old h'
      simp only [SessionStore.updateType, if_pos rfl, storeTypeSum_cons]
      show ((updateG s.localTypes ep L).map (fun p => p.2.progressMeasure)).sum +
        storeTypeSum rest + old.progressMeasure =
        (s.localTypes.map (fun p => p.2.progressMeasure)).sum + storeTypeSum rest +
          L.progressMeasure
      omega
    · simp only [SessionStore.lookupType, dif_neg hs] at h
      have := ih h
      simp only [SessionStore.updateType, if_neg hs, storeTypeSum_cons]
      omega

/-- Trace updates do not change the type measure. -/
theorem storeTypeSum_updateTrace (store : SessionStore ν) (edge : Edge) (ts : List ValType) :
    storeTypeSum (store.updateTrace edge ts) = storeTypeSum store := by
  induction store with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨sid, s⟩ := p
    by_cases hs : sid = edge.sid
    · simp only [SessionStore.updateTrace, if_pos hs]; rfl
    · simp only [SessionStore.updateTrace, if_neg hs, storeTypeSum_cons, ih]

/-- Buffer dequeues do not change the type measure. -/
theorem storeTypeSum_dequeueBuffer (store : SessionStore ν) (edge : Edge) :
    storeTypeSum (store.dequeueBuffer edge) = storeTypeSum store := by
  induction store with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨sid, s⟩ := p
    by_cases hs : sid = edge.sid
    · simp only [SessionStore.dequeueBuffer, if_pos hs]; rfl
    · simp only [SessionStore.dequeueBuffer, if_neg hs, storeTypeSum_cons, ih]

/-! ## Every frontier action strictly decreases the type measure -/

/-- Advancing `ep` from `old` to `L'` with `L'.progressMeasure < old.progressMeasure`
(then touching traces/buffers) strictly decreases the type measure. -/
theorem typeMeasure_advance_lt {store : SessionStore ν} {ep : Endpoint} {old L' : LocalType}
    (h : SessionStore.lookupType store ep = some old) (hlt : L'.progressMeasure < old.progressMeasure)
    (edge : Edge) (ts : List ValType) :
    protocolMachineTypeMeasure ((store.updateType ep L').updateTrace edge ts) <
      protocolMachineTypeMeasure store := by
  rw [typeMeasure_eq_storeTypeSum, typeMeasure_eq_storeTypeSum, storeTypeSum_updateTrace]
  have := storeTypeSum_updateType (L := L') h
  omega

/-- A branch whose label is found has measure below the branch type. -/
theorem progress_measure_lt_branch {bs : List (Label × LocalType)} {ℓ ℓ' : Label}
    {L' : LocalType} (source : Role)
    (hf : bs.find? (fun b => b.1 == ℓ) = some (ℓ', L')) :
    L'.progressMeasure < (LocalType.branch source bs).progressMeasure := by
  have hmem := List.mem_of_find?_eq_some hf
  have := sum_branches_mem_le ℓ' L' bs hmem
  show _ < 1 + LocalType.progressMeasure.sumBranches bs
  omega

/-- The first select branch has measure below the select type. -/
theorem progress_measure_lt_select_head {bs : List (Label × LocalType)} {ℓ : Label}
    {L' : LocalType} (target : Role) :
    L'.progressMeasure < (LocalType.select target ((ℓ, L') :: bs)).progressMeasure := by
  show _ < 1 + (L'.progressMeasure + LocalType.progressMeasure.sumBranches bs)
  omega

/-- **Every enabled frontier action strictly decreases the type measure.** -/
theorem frontierAction_decreases {store store' : SessionStore ν} {ep : Endpoint}
    (h : frontierAction store ep = some store') :
    protocolMachineTypeMeasure store' < protocolMachineTypeMeasure store := by
  unfold frontierAction at h
  split at h
  · next target T L' hTy =>
    cases h
    exact typeMeasure_advance_lt hTy (progress_measure_advance_send target T L') _ _
  · next source T L' hTy =>
    dsimp only at h
    split at h
    · split at h
      · cases h
        exact typeMeasure_advance_lt hTy (progress_measure_advance_recv source T L') _ _
      · cases h
    · cases h
  · next target bs hTy =>
    cases bs with
    | nil => cases h
    | cons b rest =>
      obtain ⟨ℓ, L'⟩ := b
      simp only at h
      cases h
      exact typeMeasure_advance_lt hTy (progress_measure_lt_select_head target) _ _
  · next source bs hTy =>
    dsimp only at h
    split at h
    · split at h
      · next ℓ' L' hf =>
        cases h
        rw [typeMeasure_eq_storeTypeSum, typeMeasure_eq_storeTypeSum, storeTypeSum_dequeueBuffer,
          storeTypeSum_updateTrace]
        have := storeTypeSum_updateType (L := L') hTy
        have := progress_measure_lt_branch source hf
        omega
      · cases h
    · cases h
  · cases h

/-- A role step is the identity or strictly decreases the type measure. -/
theorem roleStep_eq_or_lt (roles : List Role) (store : SessionStore ν) (r : Nat) :
    roleStep roles store r = store ∨
      protocolMachineTypeMeasure (roleStep roles store r) < protocolMachineTypeMeasure store := by
  unfold roleStep
  split
  · exact Or.inl rfl
  · split
    · next store' hfs =>
      obtain ⟨sid, _, hact⟩ := List.exists_of_findSome?_eq_some hfs
      exact Or.inr (frontierAction_decreases hact)
    · exact Or.inl rfl

/-! ## The concrete fair ranking -/

/-- **concreteRanking.** The fair-termination ranking of the concrete role step
with measure `protocolMachineTypeMeasure`. `nonincreasing`, `enabled_decreases`
and `enabled_stable` are proved outright; `progress` is the explicit hypothesis
`hProg` (global progress for the scheduled roles). -/
def concreteRanking (roles : List Role)
    (hProg : ∀ s : SessionStore ν, ¬ AllSessionsComplete s → ∃ r, r < roles.length ∧
      protocolMachineTypeMeasure (roleStep roles s r) < protocolMachineTypeMeasure s) :
    Runtime.Proofs.FairTermination.FairRanking (SessionStore ν) where
  numRoles := roles.length
  step := roleStep roles
  measure := protocolMachineTypeMeasure
  Done := AllSessionsComplete
  Enabled s r := protocolMachineTypeMeasure (roleStep roles s r) < protocolMachineTypeMeasure s
  nonincreasing s r := by
    rcases roleStep_eq_or_lt roles s r with h | h
    · rw [h]
    · exact Nat.le_of_lt h
  enabled_decreases _ _ h := h
  enabled_stable s r r' hEn hEq := by
    rcases roleStep_eq_or_lt roles s r' with h | h
    · rw [h]; exact hEn
    · omega
  progress := hProg

/-- Fair termination of the concrete role step: completion within
`k * protocolMachineTypeMeasure store₀` steps under a `k`-fair scheduler. -/
theorem concrete_termination_under_fairness (roles : List Role)
    (hProg : ∀ s : SessionStore ν, ¬ AllSessionsComplete s → ∃ r, r < roles.length ∧
      protocolMachineTypeMeasure (roleStep roles s r) < protocolMachineTypeMeasure s)
    (store₀ : SessionStore ν) {sched : Nat → Nat} {k : Nat}
    (hFair : FairScheduler roles.length k sched) :
    ∃ n, n ≤ k * protocolMachineTypeMeasure store₀ ∧
      AllSessionsComplete (executeSchedule (roleStep roles) store₀ sched n) :=
  (concreteRanking roles hProg).fair_termination store₀ sched hFair

/-! ## Progress from the frontier -/

/-- A looked-up endpoint's session is in the store. -/
theorem sid_mem_of_lookupType {store : SessionStore ν} {ep : Endpoint} {L : LocalType}
    (h : SessionStore.lookupType store ep = some L) : ep.sid ∈ store.map (·.1) := by
  induction store with
  | nil => simp [SessionStore.lookupType] at h
  | cons p rest ih =>
    obtain ⟨sid, s⟩ := p
    by_cases hs : sid = ep.sid
    · simp [hs]
    · simp only [SessionStore.lookupType, dif_neg hs] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- An enabled frontier yields an endpoint with an enabled frontier action. -/
theorem frontierAction_isSome_of_frontier {store : SessionStore ν}
    (hF : FrontierEnabled store) : ∃ ep, (frontierAction store ep).isSome := by
  rcases hF with ⟨ep, t, T, L', hTy⟩ | ⟨ep, s, T, L', rest, hTy, hTr⟩ |
    ⟨ep, t, ℓ, bs, L', hTy, hf⟩ | ⟨ep, s, bs, ℓ, L', rest, hTy, hBuf, hf⟩
  · exact ⟨ep, by simp [frontierAction, hTy]⟩
  · exact ⟨ep, by simp [frontierAction, hTy, hTr]⟩
  · refine ⟨ep, ?_⟩
    cases bs with
    | nil => simp at hf
    | cons b bs' => obtain ⟨_, _⟩ := b; simp [frontierAction, hTy]
  · exact ⟨ep, by simp [frontierAction, hTy, hBuf, hf]⟩

/-- An enabled frontier at a covered role gives a decreasing role step. -/
theorem progress_of_frontier (roles : List Role) {store : SessionStore ν}
    (hCover : ∀ ep L, SessionStore.lookupType store ep = some L → ep.role ∈ roles)
    (hF : FrontierEnabled store) :
    ∃ r, r < roles.length ∧
      protocolMachineTypeMeasure (roleStep roles store r) < protocolMachineTypeMeasure store := by
  obtain ⟨ep, hAct⟩ := frontierAction_isSome_of_frontier hF
  obtain ⟨store', hAct⟩ := Option.isSome_iff_exists.mp hAct
  have hTy : ∃ L, SessionStore.lookupType store ep = some L := by
    unfold frontierAction at hAct
    split at hAct <;> first | exact ⟨_, by assumption⟩ | cases hAct
  obtain ⟨L, hTy⟩ := hTy
  obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp (hCover ep L hTy)
  refine ⟨i, hi, ?_⟩
  have hroles : roles[i]? = some ep.role := by rw [List.getElem?_eq_getElem hi, hri]
  unfold roleStep
  simp only [hroles]
  split
  · next store'' hfs =>
    obtain ⟨sid, _, hact⟩ := List.exists_of_findSome?_eq_some hfs
    exact frontierAction_decreases hact
  · next hnone =>
    exfalso
    have := List.findSome?_eq_none_iff.mp hnone ep.sid (sid_mem_of_lookupType hTy)
    have hep : (⟨ep.sid, ep.role⟩ : Endpoint) = ep := rfl
    rw [hep, hAct] at this
    cases this

/-- **concreteRanking_of_frontier.** The concrete ranking whose `progress`
field is derived from the frontier hypothesis
`∀ s, ¬ AllSessionsComplete s → FrontierEnabled s` (see `progress_of_projected`)
and role coverage of all stored endpoints. -/
def concreteRanking_of_frontier (roles : List Role)
    (hFront : ∀ s : SessionStore ν, ¬ AllSessionsComplete s → FrontierEnabled s)
    (hCover : ∀ (s : SessionStore ν) ep L, SessionStore.lookupType s ep = some L → ep.role ∈ roles) :
    Runtime.Proofs.FairTermination.FairRanking (SessionStore ν) :=
  concreteRanking roles (fun s hs => progress_of_frontier roles (hCover s) (hFront s hs))

end
