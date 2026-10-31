import Runtime.Proofs.ProjectedProgress

/-! # Runtime.Proofs.ProjectedTermination

Preservation of `StoreProjects` by `frontierAction`/`roleStep`, and fair
termination of the concrete role step from projected stores with no
progress/frontier hypothesis (`concrete_termination_of_projected`).

The ranking is `ConcreteTermination.concreteRanking` restricted to the subtype
of stores satisfying `StoreProjects ∧ RolesCover roles`; its `progress` field is
discharged by `progress_of_projected` and `progress_of_frontier`.
-/

/-
The Problem. `concreteRanking` takes progress over *all* stores as a hypothesis,
which is false in general.

Solution Structure. Show the invariant is preserved by every role step, run the
ranking on the invariant subtype, and transport the run back to stores.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical
open Runtime.Proofs.Projected

section

universe u
variable {ν : Type u} [VerificationModel ν]

/-! ## No choices in projected stores -/

/-- Projected stores contain no `select`/`branch` types. -/
theorem projected_no_choice {store : SessionStore ν} (hP : StoreProjects store) {ep : Endpoint}
    {L : LocalType} (hTy : SessionStore.lookupType store ep = some L) (t : Role)
    (bs : List (Label × LocalType)) : L ≠ .select t bs ∧ L ≠ .branch t bs := by
  obtain ⟨g, roles, -, -, rfl⟩ := lookup_projects hP hTy
  rcases projP_cases ep.role g with h | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
    rw [h] <;> exact ⟨by simp, by simp⟩

/-- Advancing an endpoint keeps role coverage. -/
theorem rolesCover_advance {roles : List Role} {store : SessionStore ν} {ep : Endpoint}
    {edge : Edge} {L L' : LocalType} {ts : List ValType} (hC : RolesCover roles store)
    (hTy : SessionStore.lookupType store ep = some L) :
    RolesCover roles ((store.updateType ep L').updateTrace edge ts) := by
  intro e L2 h
  rw [SessionStore.lookup_type_update_trace] at h
  by_cases he : e = ep
  · subst he; exact hC _ _ hTy
  · rw [SessionStore.lookup_type_update_type_ne he] at h; exact hC _ _ h

/-! ## Send and receive specs -/

/-- The send step of `ep` satisfies the advance spec with `markFirst`. -/
theorem advance_send {ep : Endpoint} {target : Role} {T : ValType} {L' : LocalType}
    {g : List PMsg} (hC : SentClosed g) (hsend : projP ep.role g = .send target T L') :
    AdvanceSpec ep ⟨ep.sid, ep.role, target⟩ g (markFirst ep.role g) L'
      (traceP ep.role target g ++ [T]) where
  closed := sentClosed_markFirst _ hC
  sub b hb := by obtain ⟨a, ha, h1, h2, -⟩ := mem_markFirst hb; exact ⟨a, ha, h1, h2⟩
  self := projP_markFirst_self hsend
  other r hr := projP_markFirst_other hr g
  edge_tr := traceP_markFirst_self hC hsend
  other_tr _ _ h := traceP_markFirst_other h hsend

/-- The receive step of `ep` satisfies the advance spec with `recvFirst`. -/
theorem advance_recv {ep : Endpoint} {source : Role} {T T' : ValType} {L' : LocalType}
    {rest : List ValType} {g : List PMsg} (hC : SentClosed g)
    (hrecv : projP ep.role g = .recv source T L') (htr : traceP source ep.role g = T' :: rest) :
    AdvanceSpec ep ⟨ep.sid, source, ep.role⟩ g (recvFirst ep.role g) L' rest := by
  have hne : traceP source ep.role g ≠ [] := by rw [htr]; simp
  exact {
    closed := sentClosed_recvFirst _ hC
    sub := fun b hb => ⟨b, (recvFirst_sublist _ g).subset hb, rfl, rfl⟩
    self := projP_recvFirst_self hrecv
    other := fun r hr => projP_recvFirst_other hr hC hrecv hne
    edge_tr := by
      show traceP source ep.role (recvFirst ep.role g) = rest
      rw [traceP_recvFirst_self hC hrecv hne, htr]; rfl
    other_tr := fun _ _ h => traceP_recvFirst_other h hC hrecv hne }

/-! ## Preservation -/

/-- **frontierAction_preserves_projected.** Every enabled frontier action keeps
`StoreProjects` and role coverage. -/
theorem frontierAction_preserves_projected {roles : List Role} {store store' : SessionStore ν}
    {ep : Endpoint} (hP : StoreProjects store) (hC : RolesCover roles store)
    (h : frontierAction store ep = some store') :
    StoreProjects store' ∧ RolesCover roles store' := by
  unfold frontierAction at h
  split at h
  · next target T L' hTy =>
    cases h
    refine ⟨storeProjects_advance hP hTy rfl fun g roles hS _ hL => ?_, rolesCover_advance hC hTy⟩
    have hA := advance_send hS.closed hL.symm
    rw [← hS.traces] at hA
    exact ⟨_, hA⟩
  · next source T L' hTy =>
    dsimp only at h
    split at h
    · next T' rest hTr =>
      split at h
      · cases h
        refine ⟨storeProjects_advance hP hTy rfl fun g roles hS _ hL => ?_,
          rolesCover_advance hC hTy⟩
        exact ⟨_, advance_recv hS.closed hL.symm ((hS.traces _ _).symm.trans hTr)⟩
      · cases h
    · cases h
  · next target bs hTy => exact absurd rfl (projected_no_choice hP hTy target bs).1
  · next source bs hTy => exact absurd rfl (projected_no_choice hP hTy source bs).2
  · cases h

/-- **roleStep_preserves_projected.** The concrete role step keeps the invariant. -/
theorem roleStep_preserves_projected (roles : List Role) {store : SessionStore ν}
    (hP : StoreProjects store) (hC : RolesCover roles store) (r : Nat) :
    StoreProjects (roleStep roles store r) ∧ RolesCover roles (roleStep roles store r) := by
  unfold roleStep
  split
  · exact ⟨hP, hC⟩
  · split
    · next store' hfs =>
      obtain ⟨sid, _, hact⟩ := List.exists_of_findSome?_eq_some hfs
      exact frontierAction_preserves_projected hP hC hact
    · exact ⟨hP, hC⟩

/-! ## Fair termination -/

/-- Stores satisfying the projected invariant with roles covered by `roles`. -/
abbrev ProjectedStore (ν : Type u) [VerificationModel ν] (roles : List Role) :=
  {s : SessionStore ν // StoreProjects s ∧ RolesCover roles s}

/-- The role step on invariant stores. -/
def projectedStep (roles : List Role) (x : ProjectedStore ν roles) (r : Nat) :
    ProjectedStore ν roles :=
  ⟨roleStep roles x.1 r, roleStep_preserves_projected roles x.2.1 x.2.2 r⟩

/-- **projectedRanking.** The concrete ranking on invariant stores; every field,
including `progress`, is proved. -/
def projectedRanking (roles : List Role) :
    Runtime.Proofs.FairTermination.FairRanking (ProjectedStore ν roles) where
  numRoles := roles.length
  step := projectedStep roles
  measure x := protocolMachineTypeMeasure x.1
  Done x := AllSessionsComplete x.1
  Enabled x r := protocolMachineTypeMeasure (roleStep roles x.1 r) < protocolMachineTypeMeasure x.1
  nonincreasing x r := by
    show protocolMachineTypeMeasure (roleStep roles x.1 r) ≤ _
    rcases roleStep_eq_or_lt roles x.1 r with h | h
    · rw [h]
    · exact Nat.le_of_lt h
  enabled_decreases _ _ h := h
  enabled_stable x r r' hEn hEq := by
    show protocolMachineTypeMeasure (roleStep roles (roleStep roles x.1 r') r) <
      protocolMachineTypeMeasure (roleStep roles x.1 r')
    rcases roleStep_eq_or_lt roles x.1 r' with h | h
    · rw [h]; exact hEn
    · exact absurd hEq (Nat.ne_of_lt h)
  progress x hx := progress_of_frontier roles x.2.2 (progress_of_projected x.2.1 hx)

/-- Runs on invariant stores project to runs of `roleStep`. -/
theorem projected_run_val (roles : List Role) (x : ProjectedStore ν roles) (sched : Nat → Nat) :
    ∀ n, (Runtime.Proofs.FairTermination.run (projectedStep roles) x sched n).1 =
      executeSchedule (roleStep roles) x.1 sched n
  | 0 => rfl
  | n + 1 => by
    show roleStep roles (Runtime.Proofs.FairTermination.run (projectedStep roles) x sched n).1
        (sched n) = roleStep roles (executeSchedule (roleStep roles) x.1 sched n) (sched n)
    rw [projected_run_val roles x sched n]

/-- **concrete_termination_of_projected.** From any projected store whose
endpoint roles are covered by `roles`, every `k`-fair schedule of `roleStep`
completes all sessions within `k * protocolMachineTypeMeasure store₀` steps.
No progress or frontier hypothesis. -/
theorem concrete_termination_of_projected (roles : List Role) {store₀ : SessionStore ν}
    (hP : StoreProjects store₀) (hC : RolesCover roles store₀) {sched : Nat → Nat} {k : Nat}
    (hFair : FairScheduler roles.length k sched) :
    ∃ n, n ≤ k * protocolMachineTypeMeasure store₀ ∧
      AllSessionsComplete (executeSchedule (roleStep roles) store₀ sched n) := by
  obtain ⟨n, hn, hd⟩ :=
    (projectedRanking (ν := ν) roles).fair_termination ⟨store₀, hP, hC⟩ sched hFair
  refine ⟨n, hn, ?_⟩
  rw [← projected_run_val roles ⟨store₀, hP, hC⟩ sched n]
  exact hd

end
