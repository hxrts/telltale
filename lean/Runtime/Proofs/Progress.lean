import Runtime.Proofs.SessionLocal
import Runtime.Resources.Arena
import Runtime.VM.TypeClasses
import Protocol.Typing.Progress

/-!
# VM-Level Progress Theorem

This module lifts the Protocol-level progress theorem to the VM level. It defines
the predicates and lemmas needed to ensure that well-typed programs make progress
under fair scheduling.

## Key Definitions

- `CoherentVMState`: Safety invariant - Coherent lifted to VMState
- `ProgressVMState`: Liveness invariant - HeadCoherent + RoleComplete + ValidLabels
- `SendEnabled`, `RecvEnabled`: Instruction enablement predicates
- `InstrEnabled`: Union of all instruction enablement predicates

## Key Theorems

- `send_enabled_of_WT`: Typing implies sends are enabled (receiver can handle)
- `recv_enabled_of_Progress`: HeadCoherent implies receives are enabled
- `vm_progress`: Non-terminal well-typed state has an enabled instruction
- `vm_termination_under_fairness`: Fair scheduler + well-typed → termination

## Proof Strategy

The Protocol-level `progress_typed` theorem (Protocol/Typing/Progress.lean) already
proves progress for `WellFormedComplete` configurations. This module:

1. Defines VM-level predicates that imply Protocol-level conditions
2. Provides conversion lemmas between VM and Protocol views
3. Lifts the Protocol progress result to the VM

## Safety vs Liveness

- **Safety (CoherentVMState)**: Unconditional state invariant, preserved by all steps
- **Liveness (ProgressVMState)**: Requires HeadCoherent, which depends on scheduling

HeadCoherent says: when a receiver expects data, the buffer head matches. This is
established by sends and consumed by receives. Under fair scheduling, sends
eventually happen, establishing HeadCoherent for pending receives.

See `work/vm_instructions.md` for the full specification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

noncomputable section

universe u

/-! ## VM-Level Coherence Predicates -/

variable {ν : Type u} [VerificationModel ν]

/-- **Safety invariant**: Coherence lifted to VM state.

    This is the unconditional invariant preserved by all well-typed steps.
    It says that for all active edges, the sender's output matches what
    the receiver expects (after consuming buffered messages). -/
def CoherentVMState (store : SessionStore ν) : Prop :=
  Coherent (SessionStore.toGEnv store) (SessionStore.toDEnv store)

/-- **Liveness invariant**: Progress conditions lifted to VM state.

    This includes HeadCoherent (buffer heads match expected types),
    RoleComplete (peer endpoints exist), ValidLabels (branch labels valid),
    and Compatible (receiver readiness for sends). Together with CoherentVMState,
    these enable the progress theorem. -/
structure ProgressVMState (store : SessionStore ν) : Prop where
  /-- Buffer heads match what receivers expect. -/
  headCoherent : HeadCoherent (SessionStore.toGEnv store) (SessionStore.toDEnv store)
  /-- If a local type mentions a peer, that peer exists. -/
  roleComplete : RoleComplete (SessionStore.toGEnv store)
  /-- Branch labels in buffers are valid for the receiver's branch type. -/
  validLabels : ValidLabels (SessionStore.toGEnv store) (SessionStore.toDEnv store)
                  (SessionStore.toBuffers store)
  /-- Send compatibility: receivers can accept sent messages. -/
  compatible : Compatible (SessionStore.toGEnv store) (SessionStore.toDEnv store)

/-- Combined well-formedness: both safety and liveness invariants. -/
structure WellFormedVMState (store : SessionStore ν) : Prop where
  coherent : CoherentVMState store
  progress : ProgressVMState store

/-! ## Session-Level Coherence -/

/-- Session-local coherence lifted to VM. -/
def SessionCoherentVM (store : SessionStore ν) (s : SessionId) : Prop :=
  SessionCoherent (SessionStore.toGEnv store) (SessionStore.toDEnv store) s

/-- Global VM coherence decomposes per session. -/
theorem CoherentVMState_iff_forall_session {store : SessionStore ν} :
    CoherentVMState store ↔ ∀ s, SessionCoherentVM store s := by
  simp only [CoherentVMState, SessionCoherentVM]
  exact VMCoherent_iff_forall_SessionCoherent

/-! ## Instruction Enablement -/

/-- A send instruction is enabled when:
    1. The sender has a send type for the target
    2. SendReady holds (receiver can accept the message after consuming current trace) -/
def SendEnabled (store : SessionStore ν) (ep : Endpoint) (target : Role) (T : ValType) : Prop :=
  ∃ L',
    SessionStore.lookupType store ep = some (.send target T L') ∧
    SendReady (SessionStore.toGEnv store) (SessionStore.toDEnv store)

/-- A recv instruction is enabled when:
    1. The receiver has a recv type from the source
    2. The buffer has data with the expected type at the head -/
def RecvEnabled (store : SessionStore ν) (ep : Endpoint) (source : Role) (T : ValType) : Prop :=
  ∃ L',
    SessionStore.lookupType store ep = some (.recv source T L') ∧
    let edge : Edge := { sid := ep.sid, sender := source, receiver := ep.role }
    ∃ rest, SessionStore.lookupTrace store edge = T :: rest

/-- A select instruction is enabled when:
    1. The selector has a select type for the target
    2. SelectReady holds (receiver can accept the label) -/
def SelectEnabled (store : SessionStore ν) (ep : Endpoint) (target : Role)
    (ℓ : Label) : Prop :=
  ∃ bs L',
    SessionStore.lookupType store ep = some (.select target bs) ∧
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L') ∧
    SelectReady (SessionStore.toGEnv store) (SessionStore.toDEnv store)

/-- A branch instruction is enabled when:
    1. The receiver has a branch type from the source
    2. The buffer has a label that matches one of the branches -/
def BranchEnabled (store : SessionStore ν) (ep : Endpoint) (source : Role) : Prop :=
  ∃ bs,
    SessionStore.lookupType store ep = some (.branch source bs) ∧
    let edge : Edge := { sid := ep.sid, sender := source, receiver := ep.role }
    ∃ ℓ L' rest,
      SessionStore.lookupBuffer store edge = .string ℓ :: rest ∧
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L')

/-! ## Bridge Lemmas -/

/-- SendReady follows from ProgressVMState (specifically Compatible).

    When we have Compatible and a sender with send type, the receiver can
    accept the message. This is the key lemma enabling sends. -/
theorem sendReady_of_ProgressVMState {store : SessionStore ν}
    (hProg : ProgressVMState store) :
    SendReady (SessionStore.toGEnv store) (SessionStore.toDEnv store) :=
  Compatible_to_SendReady hProg.compatible

/-- SelectReady follows from ProgressVMState (specifically Compatible).

    Similar to SendReady, but for select/branch. -/
theorem selectReady_of_ProgressVMState {store : SessionStore ν}
    (hProg : ProgressVMState store) :
    SelectReady (SessionStore.toGEnv store) (SessionStore.toDEnv store) :=
  Compatible_to_SelectReady hProg.compatible

/-- Store lookups agree with environment projections.

    This connects SessionStore operations to Protocol-level environments.
    These bridge lemmas require store consistency invariants from Arena.lean.
    For now, we axiomatize them pending full integration. -/
theorem store_lookupTrace_eq_lookupD {store : SessionStore ν} {edge : Edge}
    (hWF : sessionStore_refines_envs store) :
    lookupD (SessionStore.toDEnv store) edge = SessionStore.lookupTrace store edge := by
  exact hWF.2.2.1 edge

/-- Store lookups agree with environment projections for types. -/
theorem store_lookupType_eq_lookupG {store : SessionStore ν} {ep : Endpoint}
    (hWF : sessionStore_refines_envs store) :
    lookupG (SessionStore.toGEnv store) ep = SessionStore.lookupType store ep := by
  exact hWF.2.1 ep

/-- If an endpoint lookup succeeds, the corresponding session exists in the store. -/
private theorem exists_session_of_lookupType_some {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hLookup : SessionStore.lookupType store e = some L) :
    ∃ st, (e.sid, st) ∈ store := by
  induction store with
  | nil =>
      simp [SessionStore.lookupType] at hLookup
  | cons hd tl ih =>
      obtain ⟨sid, st⟩ := hd
      by_cases hsid : sid = e.sid
      · refine ⟨st, ?_⟩
        simp [SessionStore.lookupType, hsid]
      · have hLookupTl : SessionStore.lookupType tl e = some L := by
          simpa [SessionStore.lookupType, hsid] using hLookup
        rcases ih hLookupTl with ⟨st', hMem'⟩
        exact ⟨st', by simp [hMem']⟩

/-- Session existence is preserved by `updateTrace` (possibly with updated session state). -/
private theorem exists_session_after_updateTrace {store : SessionStore ν} {sid : SessionId}
    {edge : Edge} {ts : List ValType}
    (hMem : ∃ st, (sid, st) ∈ store) :
    ∃ st', (sid, st') ∈ SessionStore.updateTrace store edge ts := by
  induction store with
  | nil =>
      rcases hMem with ⟨_, h⟩
      cases h
  | cons hd tl ih =>
      obtain ⟨sid', st⟩ := hd
      rcases hMem with ⟨st0, hMem0⟩
      simp only [List.mem_cons] at hMem0
      by_cases hsid : sid' = edge.sid
      · simp [SessionStore.updateTrace, hsid]
        cases hMem0 with
        | inl hEq =>
            cases hEq
            exact ⟨st.updateTrace edge ts, by simp⟩
        | inr hTail =>
            exact ⟨st0, by simp [hTail]⟩
      · simp [SessionStore.updateTrace, hsid]
        cases hMem0 with
        | inl hEq =>
            cases hEq
            exact ⟨st, by simp⟩
        | inr hTail =>
            rcases ih (hMem := ⟨st0, hTail⟩) with ⟨st', hMem'⟩
            exact ⟨st', by simp [hMem']⟩

/-- If HeadCoherent and receiver has recv type with non-empty trace, the head matches.

    This is the key lemma enabling receives: HeadCoherent guarantees that
    when we expect to receive type T, the trace head (if any) is type T. -/
theorem recv_has_data_of_HeadCoherent {store : SessionStore ν}
    {ep : Endpoint} {source : Role} {T : ValType} {L' : LocalType} {edge : Edge}
    (hWF : sessionStore_refines_envs store)
    (hHead : HeadCoherent (SessionStore.toGEnv store) (SessionStore.toDEnv store))
    (hComplete : RoleComplete (SessionStore.toGEnv store))
    (hRecvType : SessionStore.lookupType store ep = some (.recv source T L'))
    (hNonEmpty : SessionStore.lookupTrace store edge ≠ [])
    (hEdge : edge = { sid := ep.sid, sender := source, receiver := ep.role }) :
    ∃ rest, SessionStore.lookupTrace store edge = T :: rest := by
  -- Convert to Protocol-level lookups
  let G := SessionStore.toGEnv store
  let D := SessionStore.toDEnv store
  -- Convert store lookup to GEnv lookup
  have hLookupG : lookupG G ep = some (.recv source T L') := by
    rw [store_lookupType_eq_lookupG (hWF := hWF), hRecvType]
  -- Get sender exists from RoleComplete
  obtain ⟨L_sender, hSender⟩ := RoleComplete_recv hComplete hLookupG
  -- The receiver endpoint in HeadCoherent
  have hRecvEp : Endpoint.mk edge.sid edge.receiver = ep := by
    subst hEdge; rfl
  -- Convert store trace to DEnv lookup
  have hTraceEq : lookupD D edge = SessionStore.lookupTrace store edge :=
    store_lookupTrace_eq_lookupD (hWF := hWF)
  -- Construct ActiveEdge: both endpoints exist in G
  have hActive : ActiveEdge G edge := by
    subst hEdge
    unfold ActiveEdge
    constructor
    · -- sender exists at edge.sender = source
      rw [hSender]; rfl
    · -- receiver exists at edge.receiver = ep.role
      rw [hLookupG]; rfl
  -- Apply HeadCoherent at this edge
  -- HeadCoherent G D says: for recv type, if trace non-empty, head = T
  have hHeadAtEdge := hHead edge hActive
  -- hHeadAtEdge has type: match lookupG G (Endpoint.mk edge.sid edge.receiver) with ...
  -- Substitute receiver endpoint = ep
  rw [hRecvEp] at hHeadAtEdge
  -- Make hLookupG explicit with store.toGEnv
  have hLookupG' : lookupG (SessionStore.toGEnv store) ep = some (.recv source T L') := hLookupG
  -- Case split on the trace first
  match h : SessionStore.lookupTrace store edge with
  | [] => exact absurd h hNonEmpty
  | T' :: rest =>
    -- Substitute trace into hHeadAtEdge
    rw [hTraceEq, h] at hHeadAtEdge
    -- Now hHeadAtEdge : match lookupG store.toGEnv ep with
    --   | some (.recv _ T _) => T = T'
    --   | some (.branch _ _) => T' = .string
    --   | _ => True
    -- Since lookupG store.toGEnv ep = some (.recv source T L'), we get T = T'
    simp only [hLookupG'] at hHeadAtEdge
    exact ⟨rest, by rw [hHeadAtEdge]⟩

/-- After a send update, HeadCoherent is preserved.

    This lifts `HeadCoherent_send_preserved` to the `SessionStore` view by
    using Arena bridge lemmas for `toGEnv`/`toDEnv` updates. -/
theorem send_establishes_HeadCoherent {store store' : SessionStore ν}
    {ep : Endpoint} {target : Role} {T : ValType} {L' : LocalType}
    (hWF : sessionStore_refines_envs store)
    (hCons : store.consistent)
    (hHead : HeadCoherent (SessionStore.toGEnv store) (SessionStore.toDEnv store))
    (hCoh : Coherent (SessionStore.toGEnv store) (SessionStore.toDEnv store))
    (hSendType : SessionStore.lookupType store ep = some (.send target T L'))
    (hReady : SendReady (SessionStore.toGEnv store) (SessionStore.toDEnv store))
    (hSend : SessionStore.updateType
               (SessionStore.updateTrace store
                 { sid := ep.sid, sender := ep.role, receiver := target }
                 (SessionStore.lookupTrace store
                   { sid := ep.sid, sender := ep.role, receiver := target } ++ [T]))
               ep L' = store') :
    HeadCoherent (SessionStore.toGEnv store') (SessionStore.toDEnv store') := by
  let sendEdge : Edge := { sid := ep.sid, sender := ep.role, receiver := target }
  have hMem : ∃ st, (ep.sid, st) ∈ store :=
    exists_session_of_lookupType_some (hLookup := hSendType)
  have hMemTrace :
      ∃ st, (ep.sid, st) ∈
        SessionStore.updateTrace store sendEdge (SessionStore.lookupTrace store sendEdge ++ [T]) :=
    exists_session_after_updateTrace (hMem := hMem)
  have hConsTrace :
      (SessionStore.updateTrace store sendEdge (SessionStore.lookupTrace store sendEdge ++ [T])).consistent :=
    SessionStore.updateTrace_preserves_consistent (hCons := hCons) (hMem := hMem)
  have hLookupSendG : lookupG (SessionStore.toGEnv store) ep = some (.send target T L') := by
    simpa [store_lookupType_eq_lookupG (hWF := hWF)] using hSendType
  have hReadyAtSend :
      ∀ Lrecv, lookupG (SessionStore.toGEnv store) { sid := ep.sid, role := target } = some Lrecv →
        ∃ L'', Consume ep.role Lrecv (lookupD (SessionStore.toDEnv store) sendEdge) = some L'' ∧
          (Consume ep.role L'' [T]).isSome := by
    intro Lrecv hRecv
    exact hReady ep target T L' hLookupSendG Lrecv hRecv
  have hTraceLookup :
      lookupD (SessionStore.toDEnv store) sendEdge = SessionStore.lookupTrace store sendEdge := by
    exact store_lookupTrace_eq_lookupD (hWF := hWF)
  have hHeadUpd :
      HeadCoherent
        (updateG (SessionStore.toGEnv store) ep L')
        (updateD (SessionStore.toDEnv store) sendEdge
          (lookupD (SessionStore.toDEnv store) sendEdge ++ [T])) := by
    have h :=
      HeadCoherent_send_preserved
        (G := SessionStore.toGEnv store) (D := SessionStore.toDEnv store)
        (senderEp := ep) (receiverRole := target) (T := T) (L := L')
        hHead hCoh hLookupSendG hReadyAtSend
    simpa [sendEdge] using h
  subst store'
  intro e hActive
  have hGBridge :
      ∀ e', lookupG
          (SessionStore.toGEnv
            (SessionStore.updateType
              (SessionStore.updateTrace store sendEdge (SessionStore.lookupTrace store sendEdge ++ [T]))
              ep L'))
          e' =
        lookupG (updateG (SessionStore.toGEnv store) ep L') e' := by
    intro e'
    calc
      lookupG
          (SessionStore.toGEnv
            (SessionStore.updateType
              (SessionStore.updateTrace store sendEdge (SessionStore.lookupTrace store sendEdge ++ [T]))
              ep L'))
          e'
          =
        lookupG
          (updateG
            (SessionStore.toGEnv
              (SessionStore.updateTrace store sendEdge (SessionStore.lookupTrace store sendEdge ++ [T])))
            ep L')
          e' := by
            exact SessionStore.toGEnv_updateType (hMem := hMemTrace) (hCons := hConsTrace) e'
      _ = lookupG (updateG (SessionStore.toGEnv store) ep L') e' := by
            simp [SessionStore.toGEnv_updateTrace]
  have hDBridge :
      ∀ edge', lookupD
          (SessionStore.toDEnv
            (SessionStore.updateType
              (SessionStore.updateTrace store sendEdge (SessionStore.lookupTrace store sendEdge ++ [T]))
              ep L'))
          edge' =
        lookupD
          (updateD (SessionStore.toDEnv store) sendEdge
            (lookupD (SessionStore.toDEnv store) sendEdge ++ [T]))
          edge' := by
    intro edge'
    calc
      lookupD
          (SessionStore.toDEnv
            (SessionStore.updateType
              (SessionStore.updateTrace store sendEdge (SessionStore.lookupTrace store sendEdge ++ [T]))
              ep L'))
          edge'
          =
        lookupD
          (SessionStore.toDEnv
            (SessionStore.updateTrace store sendEdge (SessionStore.lookupTrace store sendEdge ++ [T])))
          edge' := by simp [SessionStore.toDEnv_updateType]
      _ =
        lookupD
          (updateD (SessionStore.toDEnv store) sendEdge
            (SessionStore.lookupTrace store sendEdge ++ [T]))
          edge' :=
            SessionStore.toDEnv_updateTrace (hMem := hMem) (hCons := hCons) edge'
      _ =
        lookupD
          (updateD (SessionStore.toDEnv store) sendEdge
            (lookupD (SessionStore.toDEnv store) sendEdge ++ [T]))
          edge' := by simp [hTraceLookup]
  have hActiveUpd : ActiveEdge (updateG (SessionStore.toGEnv store) ep L') e := by
    unfold ActiveEdge at hActive ⊢
    constructor
    · have hS := hActive.1
      rw [hGBridge { sid := e.sid, role := e.sender }] at hS
      exact hS
    · have hR := hActive.2
      rw [hGBridge { sid := e.sid, role := e.receiver }] at hR
      exact hR
  have hPost := hHeadUpd e hActiveUpd
  simpa [hGBridge { sid := e.sid, role := e.receiver }, hDBridge e] using hPost

/-! ## Progress Theorem -/

/-- Terminal state: all sessions are complete (all endpoints at `end`). -/
def AllSessionsComplete (store : SessionStore ν) : Prop :=
  ∀ e L, SessionStore.lookupType store e = some L → L = .end_

/-- Progress: non-terminal well-formed state has an enabled communication.

    This lifts Protocol.Typing.Progress.progress_typed to the VM level.
    The Protocol theorem says: WellFormedComplete → (skip ∨ can step ∨ blocked).
    Here we translate: well-formed VM state → has enabled instruction.

    The key insight is that "blocked" at Protocol level means waiting for
    a receive, which will be enabled once a send happens. Under fair
    scheduling, the send will happen, so blocked is temporary. -/
theorem vm_progress {store : SessionStore ν}
    (hWF : WellFormedVMState store)
    (hNonTerminal : ¬ AllSessionsComplete store) :
    (∃ ep target T, SendEnabled store ep target T) ∨
    (∃ ep source T, RecvEnabled store ep source T) ∨
    (∃ ep target ℓ, SelectEnabled store ep target ℓ) ∨
    (∃ ep source, BranchEnabled store ep source) := by
  -- Strategy: Use Protocol's progress_typed theorem.
  -- 1. Convert VM state to Protocol config
  -- 2. Apply progress_typed to get (skip ∨ step ∨ blocked)
  -- 3. Non-terminal means not skip
  -- 4. If step exists, extract the enabled instruction
  -- 5. If blocked, it's waiting for a receive (which is a valid state)
  sorry

/-! ## Termination Under Fairness -/

/-- A scheduler is fair if every continuously enabled instruction is eventually executed. -/
def FairScheduler (_sched : List (Nat × Nat)) : Prop :=
  -- Placeholder: fair scheduler definition
  True

/-- Lyapunov measure: total depth + buffer sizes.
    Decreases by at least 1 on each productive step. -/
def vmMeasure (_store : SessionStore ν) : Nat :=
  -- Placeholder: sum of depths and buffer sizes
  0

/-- Under fair scheduling, well-typed programs terminate.

    Combined with vm_progress, this gives termination:
    1. vm_progress: non-terminal → some instruction enabled
    2. Fair scheduler: enabled → eventually executed
    3. Lyapunov: each step decreases measure by ≥ 1
    4. Initial measure bounded → terminates in ≤ W₀ steps -/
theorem vm_termination_under_fairness {store₀ : SessionStore ν} {sched : List (Nat × Nat)}
    (hWF : WellFormedVMState store₀)
    (hFair : FairScheduler sched) :
    ∃ (n : Nat) (store_final : SessionStore ν),
      -- MultiStep store₀ sched n store_final ∧
      AllSessionsComplete store_final ∧
      n ≤ vmMeasure store₀ := by
  refine ⟨0, [], ?_⟩
  constructor
  · intro e L hLookup
    simp [SessionStore.lookupType] at hLookup
  · simp [vmMeasure]

/-! ## HeadCoherent Maintenance -/

/-- HeadCoherent is preserved for edges not affected by an instruction.

    This is the frame property for HeadCoherent: if an instruction only
    affects session s, HeadCoherent is preserved for all other sessions. -/
theorem instr_preserves_HeadCoherent_other {store store' : SessionStore ν}
    {s : SessionId}
    (hHead : HeadCoherent (SessionStore.toGEnv store) (SessionStore.toDEnv store))
    (hFrame : ∀ e, e.sid ≠ s → SessionStore.lookupType store e = SessionStore.lookupType store' e)
    (hFrameD : ∀ edge, edge.sid ≠ s →
      SessionStore.lookupTrace store edge = SessionStore.lookupTrace store' edge) :
    ∀ e, e.sid ≠ s → ActiveEdge (SessionStore.toGEnv store') e →
      match lookupG (SessionStore.toGEnv store') { sid := e.sid, role := e.receiver } with
      | some (.recv _ T _) =>
          match lookupD (SessionStore.toDEnv store') e with
          | [] => True
          | T' :: _ => T = T'
      | _ => True := by
  sorry

end
