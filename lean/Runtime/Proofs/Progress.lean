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

    This connects SessionStore operations to Protocol-level environments. -/
theorem store_lookupTrace_eq_lookupD {store : SessionStore ν} {edge : Edge} :
    lookupD (SessionStore.toDEnv store) edge = SessionStore.lookupTrace store edge := by
  -- By induction on store structure, toDEnv accumulates traces consistently.
  induction store with
  | nil => simp [SessionStore.toDEnv, SessionStore.lookupTrace, lookupD]
  | cons hd tl ih =>
    simp only [SessionStore.toDEnv, SessionStore.lookupTrace, List.foldl]
    by_cases h : hd.1 = edge.sid
    · -- Edge is in this session
      simp [h]
      sorry -- Need to show foldl accumulation preserves lookup
    · -- Edge is in another session
      simp [h]
      sorry -- Need ih and that hd doesn't affect this edge

/-- Store lookups agree with environment projections for types. -/
theorem store_lookupType_eq_lookupG {store : SessionStore ν} {ep : Endpoint} :
    lookupG (SessionStore.toGEnv store) ep = SessionStore.lookupType store ep := by
  induction store with
  | nil => simp [SessionStore.toGEnv, SessionStore.lookupType, lookupG]
  | cons hd tl ih =>
    simp only [SessionStore.toGEnv, SessionStore.lookupType, List.foldl]
    by_cases h : hd.1 = ep.sid
    · simp [h]
      sorry -- Similar accumulation argument
    · simp [h]
      sorry

/-- If HeadCoherent and receiver has recv type with non-empty trace, the head matches.

    This is the key lemma enabling receives: HeadCoherent guarantees that
    when we expect to receive type T, the trace head (if any) is type T. -/
theorem recv_has_data_of_HeadCoherent {store : SessionStore ν}
    {ep : Endpoint} {source : Role} {T : ValType} {L' : LocalType} {edge : Edge}
    (hHead : HeadCoherent (SessionStore.toGEnv store) (SessionStore.toDEnv store))
    (hRecvType : SessionStore.lookupType store ep = some (.recv source T L'))
    (hNonEmpty : SessionStore.lookupTrace store edge ≠ [])
    (hEdge : edge = { sid := ep.sid, sender := source, receiver := ep.role }) :
    ∃ rest, SessionStore.lookupTrace store edge = T :: rest := by
  -- 1. Convert to Protocol-level lookups
  let G := SessionStore.toGEnv store
  let D := SessionStore.toDEnv store
  -- 2. Get ActiveEdge from the fact that receiver exists
  have hRecvEp : ep = { sid := edge.sid, role := edge.receiver } := by
    simp [hEdge]
  -- 3. Apply HeadCoherent
  -- HeadCoherent says: for recv type, if trace non-empty, head = T
  have hLookupG : lookupG G ep = some (.recv source T L') := by
    simpa [G, store_lookupType_eq_lookupG] using hRecvType
  have hLookupD : lookupD D edge = SessionStore.lookupTrace store edge := by
    exact store_lookupTrace_eq_lookupD
  -- HeadCoherent at this edge gives us the result
  -- But we need to show ActiveEdge first
  sorry

/-- After a send, HeadCoherent holds for the corresponding edge.

    This is how sends "enable" receives: the sent data appears at the
    head of the buffer with the correct type. -/
theorem send_establishes_HeadCoherent {store store' : SessionStore ν}
    {ep : Endpoint} {target : Role} {T : ValType} {L' : LocalType}
    (hSend : SessionStore.updateType
               (SessionStore.updateTrace store
                 { sid := ep.sid, sender := ep.role, receiver := target }
                 (SessionStore.lookupTrace store
                   { sid := ep.sid, sender := ep.role, receiver := target } ++ [T]))
               ep L' = store') :
    let edge := { sid := ep.sid, sender := ep.role, receiver := target }
    let G' := SessionStore.toGEnv store'
    let D' := SessionStore.toDEnv store'
    ActiveEdge G' edge →
    match lookupG G' { sid := edge.sid, role := edge.receiver } with
    | some (.recv _ T' _) =>
        match lookupD D' edge with
        | [] => True
        | T'' :: _ => T' = T''
    | _ => True := by
  sorry

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
  sorry

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
