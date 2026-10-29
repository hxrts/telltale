import Runtime.Adequacy.CommTraceAdequacy
import Runtime.ProtocolMachine.Semantics.ExecComm

/-! # Runtime.Adequacy.CommTraceMachine

Ties `CommStep` to the real protocol-machine send/receive instructions:
`stepSend` and `stepReceive` (from `Semantics/ExecComm.lean`), followed by the
machine's own `appendEvent`, preserve `CommReachable` of the
(observable trace, signed buffers) pair, provided every edge's buffer is in
FIFO mode. Consequently trace adequacy holds for every state reached from a
communication-reachable state by such steps.

Exclusions (stated honestly): `latestValue` buffer mode overwrites in-flight
messages so FIFO fails there (hence the `AllFifo` hypothesis); speculation
rollback (`ExecSpeculation`) truncates the trace and loader resets replace
buffers, so neither is covered; offer/choose and the remaining instructions
are not yet shown to refine `CommStep`.
-/

/-
The Problem. `comm_trace_adequacy` was proved over an abstract `CommStep`
relation; nothing related it to the real instruction semantics.

Solution Structure. Define `CommPres st p` (a pack `p` produced from `st`
preserves reachability) and prove it stage by stage through the send and
receive pipelines.
-/

set_option autoImplicit false

universe u

section

variable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν]
    [AccumulatedSet ν] [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]

/-! ## Preservation predicate -/

/-- Every edge's buffer runs in FIFO mode. -/
def AllFifo (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  ∀ e, (st.config.bufferConfig e).mode = .fifo

/-- A step pack produced from `st` preserves communication reachability once
its event is appended to the trace. -/
def CommPres (st : ProtocolMachineState ι γ π ε ν) (p : StepPack ι γ π ε ν) : Prop :=
  CommReachable ((st.obsTrace, st.buffers) : CommConfig ε ν) →
    CommReachable (((appendEvent p.st p.res.event).obsTrace, p.st.buffers) : CommConfig ε ν)

/-- Fault packs over a state with the same trace and buffers preserve reachability. -/
theorem commPres_fault {st st' : ProtocolMachineState ι γ π ε ν} {coro : CoroutineState γ ε}
    {err : Fault γ} {msg : String} (ho : st'.obsTrace = st.obsTrace)
    (hb : st'.buffers = st.buffers) : CommPres st (faultPack st' coro err msg) := by
  intro h; simpa [faultPack, pack, mkRes, appendEvent, ho, hb] using h

/-- Block packs preserve reachability. -/
theorem commPres_block {st : ProtocolMachineState ι γ π ε ν} {coro : CoroutineState γ ε}
    {r : BlockReason γ} : CommPres st (blockPack st coro r) := by
  intro h; simpa [blockPack, pack, mkRes, appendEvent] using h

/-! ## Send pipeline -/

/-- Committing an enqueued send emits `sent` and matches `CommStep.send`. -/
theorem commPres_sendCommit {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {sv : SignedValue ν} {seqNo : Nat}
    (ho : st.obsTrace = st0.obsTrace) (hb : st.buffers = st0.buffers) :
    CommPres st0 (sendCommit st coro ep edge
      (signedBufferSet st.buffers edge (signedBufferLookup st.buffers edge ++ [sv]))
      T L' sv.payload seqNo) := by
  intro h
  simp only [sendCommit, continuePack, pack, mkRes, appendEvent]
  rw [ho, hb]
  exact CommReachable.step h (CommStep.send _ _ _ _ _ _)

/-- The enqueue-result dispatch preserves reachability in FIFO mode. -/
theorem commPres_sendAfterEnqueue {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {hd : HandlerId} {seqNo : Nat} {sv : SignedValue ν}
    {res : SignedEnqueueResult} {bufs' : SignedBuffers ν}
    (ho : st.obsTrace = st0.obsTrace) (hb : st.buffers = st0.buffers)
    (hm : (st.config.bufferConfig edge).mode = .fifo)
    (hres : bufEnqueue (st.config.bufferConfig edge) st.buffers edge sv = (res, bufs')) :
    CommPres st0 (sendAfterEnqueue st coro ep edge T L' sv.payload hd seqNo res bufs') := by
  cases res with
  | ok =>
    have hbf := bufEnqueue_fifo_ok hm hres
    subst hbf
    simp only [sendAfterEnqueue]
    split
    · exact commPres_fault ho hb
    · exact commPres_sendCommit ho hb
  | blocked =>
    intro h; simpa [sendAfterEnqueue, blockPack, pack, mkRes, appendEvent, ho, hb] using h
  | dropped => simp only [sendAfterEnqueue]; exact commPres_fault ho hb
  | error => simp only [sendAfterEnqueue]; exact commPres_fault ho hb

/-- The handler stage of send preserves reachability in FIFO mode. -/
theorem commPres_sendOnHandler {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {v : Value} {hd : HandlerId} (hf : AllFifo st) :
    CommPres st (sendOnHandler st coro ep edge T L' v hd) := by
  unfold sendOnHandler
  exact commPres_sendAfterEnqueue (sv := signValueWithSeq _ v _) rfl rfl (hf edge) rfl

/-- Send edge dispatch preserves reachability in FIFO mode. -/
theorem commPres_sendOnEdge {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {v : Value} (hf : AllFifo st) :
    CommPres st (sendOnEdge st coro ep edge T L' v) := by
  unfold sendOnEdge
  repeat' split
  all_goals first
    | exact commPres_block
    | exact commPres_fault rfl rfl
    | exact commPres_sendOnHandler hf

/-- **`stepSend` refines `CommStep`** (FIFO mode): the real send instruction,
followed by `appendEvent`, preserves communication reachability. -/
theorem commPres_stepSend {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan val : Reg} (hf : AllFifo st) :
    CommPres st (stepSend st coro chan val) := by
  unfold stepSend sendWithEndpoint sendWithType
  repeat' split
  all_goals first
    | exact commPres_fault rfl rfl
    | exact commPres_sendOnEdge hf

/-! ## Receive pipeline -/

/-- Replay-consumption only touches replay bookkeeping. -/
theorem commConsume_preserves {st st' : ProtocolMachineState ι γ π ε ν} {tick : Nat}
    {ident : CommunicationIdentity} {a : CommunicationConsumeArtifact}
    (h : commConsumeReceiveIdentity st tick ident = .ok (a, st')) :
    st'.obsTrace = st.obsTrace ∧ st'.buffers = st.buffers := by
  simp only [commConsumeReceiveIdentity] at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  all_goals (split at h <;> first | (cases h; done) | (cases h; exact ⟨rfl, rfl⟩))

/-- Committing a dequeued receive emits `received` and matches `CommStep.recv`. -/
theorem commPres_recvCommit {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {L' : LocalType}
    {sv : SignedValue ν} {bufs' : SignedBuffers ν} {tokens' : List ProgressToken}
    {dst : Reg} (ho : st.obsTrace = st0.obsTrace) (hb : st.buffers = st0.buffers)
    (hd : bufDequeue st0.buffers edge = some (sv, bufs')) :
    CommPres st0 (recvCommit st coro ep edge bufs' L' sv.payload tokens' dst sv.seqNo) := by
  unfold recvCommit
  split
  · exact commPres_fault ho hb
  · intro h
    simp only [continuePack, pack, mkRes, appendEvent]
    rw [ho]
    exact CommReachable.step h (CommStep.recv _ _ _ _ _ _ _ hd)

/-- Post-dequeue validation preserves reachability. -/
theorem commPres_recvAfterDequeue {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {dst : Reg} {hd : HandlerId} {tokens' : List ProgressToken}
    {sv : SignedValue ν} {bufs' : SignedBuffers ν}
    (hdq : bufDequeue st.buffers edge = some (sv, bufs')) :
    CommPres st (recvAfterDequeue st coro ep edge T L' dst hd tokens' sv bufs') := by
  unfold recvAfterDequeue
  split
  · exact commPres_fault rfl rfl
  split
  · exact commPres_fault rfl rfl
  dsimp only
  split
  · split
    · exact commPres_fault rfl rfl
    · next _ st' hc =>
      have hp := commConsume_preserves hc
      split
      · exact commPres_recvCommit hp.1 hp.2 hdq
      · exact commPres_fault hp.1 hp.2
  · exact commPres_fault rfl rfl

/-- Receive handler stage preserves reachability. -/
theorem commPres_recvWithHandler {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {dst : Reg} {hd : HandlerId} {tokens' : List ProgressToken} :
    CommPres st (recvWithHandler st coro ep edge T L' dst hd tokens') := by
  unfold recvWithHandler
  cases hdq : bufDequeue st.buffers edge with
  | none => exact commPres_block (st := st)
  | some r => obtain ⟨sv, bufs'⟩ := r; exact commPres_recvAfterDequeue hdq

/-- **`stepReceive` refines `CommStep`**: the real receive instruction, followed
by `appendEvent`, preserves communication reachability (in any buffer mode). -/
theorem commPres_stepReceive {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan dst : Reg} :
    CommPres st (stepReceive st coro chan dst) := by
  unfold stepReceive recvWithEndpoint recvOnEdge
  dsimp only
  repeat' split
  all_goals first
    | exact commPres_block
    | exact commPres_fault rfl rfl
    | exact commPres_recvWithHandler (st := st)

/-! ## Adequacy and conservation for real steps -/

/-- Trace adequacy after a real `stepSend` from a reachable FIFO state. -/
theorem stepSend_trace_adequacy {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan val : Reg} (hf : AllFifo st)
    (h : CommReachable ((st.obsTrace, st.buffers) : CommConfig ε ν)) :
    let p := stepSend st coro chan val
    CausallyConsistent (obsTraceOf (appendEvent p.st p.res.event).obsTrace) ∧
      FIFOConsistent (obsTraceOf (appendEvent p.st p.res.event).obsTrace) :=
  comm_trace_adequacy (commPres_stepSend hf h)

/-- Trace adequacy after a real `stepReceive` from a reachable state. -/
theorem stepReceive_trace_adequacy {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan dst : Reg}
    (h : CommReachable ((st.obsTrace, st.buffers) : CommConfig ε ν)) :
    let p := stepReceive st coro chan dst
    CausallyConsistent (obsTraceOf (appendEvent p.st p.res.event).obsTrace) ∧
      FIFOConsistent (obsTraceOf (appendEvent p.st p.res.event).obsTrace) :=
  comm_trace_adequacy (commPres_stepReceive h)

/-- Per-edge message conservation (sent = received ++ in-flight) holds after a
real `stepSend` (FIFO) from a reachable state. -/
theorem stepSend_conservation {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan val : Reg} (hf : AllFifo st)
    (h : CommReachable ((st.obsTrace, st.buffers) : CommConfig ε ν)) :
    let p := stepSend st coro chan val
    CommInv (((appendEvent p.st p.res.event).obsTrace, p.st.buffers) : CommConfig ε ν) :=
  (commReachable_inv (commPres_stepSend hf h)).1

/-- Per-edge message conservation holds after a real `stepReceive`. -/
theorem stepReceive_conservation {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan dst : Reg}
    (h : CommReachable ((st.obsTrace, st.buffers) : CommConfig ε ν)) :
    let p := stepReceive st coro chan dst
    CommInv (((appendEvent p.st p.res.event).obsTrace, p.st.buffers) : CommConfig ε ν) :=
  (commReachable_inv (commPres_stepReceive h)).1

end
