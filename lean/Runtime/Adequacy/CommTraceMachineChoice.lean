import Runtime.Adequacy.CommTraceChoice
import Runtime.Adequacy.CommTraceMachine
import Runtime.ProtocolMachine.Semantics.ExecChoice

/-! # Runtime.Adequacy.CommTraceMachineChoice

Ties the extended step relation `CommStepC` to the real protocol-machine
instructions `stepSend`, `stepReceive`, `stepOffer` and `stepChoose`
(`Semantics/ExecComm.lean`): each, followed by `appendEvent`, preserves
`CommReachableC` of the (observable trace, signed buffers) pair, provided every
edge's buffer is in FIFO mode for the enqueueing instructions.

Exclusions (stated honestly): `latestValue` buffer mode overwrites in-flight
messages so FIFO fails there (hence `AllFifo`); speculation rollback and loader
resets are not covered. For `stepChoose`, the two fault branches of
`chooseAfterDequeue` ("unknown label", "bad label payload") drop the dequeued
message without emitting a consuming event, so conservation genuinely does not
hold across them; the theorem therefore concludes `CommPresC ∨ IsFaultPack`.
-/

/-
The Problem. `CommTraceMachine.lean` covers send/receive only; offer/choose
emit `offered`/`chose` events that `CommStep` cannot absorb.

Solution Structure. Define `CommPresC`, re-run the send/receive pipeline
proofs against `CommStepC`, then handle the offer and choose pipelines stage
by stage.
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

/-- A step pack produced from `st` preserves extended communication
reachability once its event is appended to the trace. -/
def CommPresC (st : ProtocolMachineState ι γ π ε ν) (p : StepPack ι γ π ε ν) : Prop :=
  CommReachableC ((st.obsTrace, st.buffers) : CommConfig ε ν) →
    CommReachableC (((appendEvent p.st p.res.event).obsTrace, p.st.buffers) : CommConfig ε ν)

/-- The pack reports a fault. -/
def IsFaultPack (p : StepPack ι γ π ε ν) : Prop :=
  ∃ err, p.res.status = .faulted err

/-- The pack preserves extended reachability or reports a fault. -/
def CommPresOrFault (st : ProtocolMachineState ι γ π ε ν) (p : StepPack ι γ π ε ν) : Prop :=
  CommPresC st p ∨ IsFaultPack p

/-- Fault packs over a state with the same trace and buffers preserve reachability. -/
theorem commPresC_fault {st st' : ProtocolMachineState ι γ π ε ν} {coro : CoroutineState γ ε}
    {err : Fault γ} {msg : String} (ho : st'.obsTrace = st.obsTrace)
    (hb : st'.buffers = st.buffers) : CommPresC st (faultPack st' coro err msg) := by
  intro h; simpa [faultPack, pack, mkRes, appendEvent, ho, hb] using h

/-- Every `faultPack` is a fault pack. -/
theorem isFaultPack_faultPack {st : ProtocolMachineState ι γ π ε ν} {coro : CoroutineState γ ε}
    {err : Fault γ} {msg : String} : IsFaultPack (faultPack st coro err msg) :=
  ⟨err, rfl⟩

/-- Block packs preserve reachability. -/
theorem commPresC_block {st : ProtocolMachineState ι γ π ε ν} {coro : CoroutineState γ ε}
    {r : BlockReason γ} : CommPresC st (blockPack st coro r) := by
  intro h; simpa [blockPack, pack, mkRes, appendEvent] using h

/-! ## Send pipeline -/

/-- Committing an enqueued send matches `CommStepC.send`. -/
theorem commPresC_sendCommit {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {lbl : Option Label} {sv : SignedValue ν} {seqNo : Nat}
    (ho : st.obsTrace = st0.obsTrace) (hb : st.buffers = st0.buffers) :
    CommPresC st0 (sendCommit st coro ep edge
      (signedBufferSet st.buffers edge (signedBufferLookup st.buffers edge ++ [sv]))
      T L' sv.payload seqNo lbl) := by
  intro h
  simp only [sendCommit, continuePack, pack, mkRes, appendEvent]
  rw [ho, hb]
  exact CommReachableC.step h (CommStepC.send _ _ _ _ _ _ _)

/-- The enqueue-result dispatch of send preserves reachability in FIFO mode. -/
theorem commPresC_sendAfterEnqueue {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {lbl : Option Label} {hd : HandlerId} {seqNo : Nat} {sv : SignedValue ν}
    {res : SignedEnqueueResult} {bufs' : SignedBuffers ν}
    (ho : st.obsTrace = st0.obsTrace) (hb : st.buffers = st0.buffers)
    (hm : (st.config.bufferConfig edge).mode = .fifo)
    (hres : bufEnqueue (st.config.bufferConfig edge) st.buffers edge sv = (res, bufs')) :
    CommPresC st0 (sendAfterEnqueue st coro ep edge T L' sv.payload hd seqNo res bufs' lbl) := by
  cases res with
  | ok =>
    have hbf := bufEnqueue_fifo_ok hm hres
    subst hbf
    simp only [sendAfterEnqueue]
    split
    · exact commPresC_fault ho hb
    · exact commPresC_sendCommit ho hb
  | blocked =>
    intro h; simpa [sendAfterEnqueue, blockPack, pack, mkRes, appendEvent, ho, hb] using h
  | dropped => simp only [sendAfterEnqueue]; exact commPresC_fault ho hb
  | error => simp only [sendAfterEnqueue]; exact commPresC_fault ho hb

/-- The handler stage of send preserves reachability in FIFO mode. -/
theorem commPresC_sendOnHandler {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {lbl : Option Label} {v : Value} {hd : HandlerId} (hf : AllFifo st) :
    CommPresC st (sendOnHandler st coro ep edge T L' v hd lbl) := by
  unfold sendOnHandler
  exact commPresC_sendAfterEnqueue (sv := signValueWithSeq _ v _) rfl rfl (hf edge) rfl

/-- Send edge dispatch preserves reachability in FIFO mode. -/
theorem commPresC_sendOnEdge {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {lbl : Option Label} {v : Value} (hf : AllFifo st) :
    CommPresC st (sendOnEdge st coro ep edge T L' v lbl) := by
  unfold sendOnEdge
  repeat' split
  all_goals first
    | exact commPresC_block
    | exact commPresC_fault rfl rfl
    | exact commPresC_sendOnHandler hf

/-- **`stepSend` refines `CommStepC`** (FIFO mode). -/
theorem commPresC_stepSend {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan val : Reg} (hf : AllFifo st) :
    CommPresC st (stepSend st coro chan val) := by
  unfold stepSend sendWithEndpoint sendWithType
  repeat' split
  all_goals first
    | exact commPresC_fault rfl rfl
    | exact commPresC_sendOnEdge hf

/-! ## Receive pipeline -/

/-- Committing a dequeued receive matches `CommStepC.recv`. -/
theorem commPresC_recvCommit {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {L' : LocalType} {lbl : Option Label}
    {sv : SignedValue ν} {bufs' : SignedBuffers ν} {tokens' : List ProgressToken}
    {dst : Reg} (ho : st.obsTrace = st0.obsTrace) (hb : st.buffers = st0.buffers)
    (hd : bufDequeue st0.buffers edge = some (sv, bufs')) :
    CommPresC st0 (recvCommit st coro ep edge bufs' L' sv.payload tokens' dst sv.seqNo lbl) := by
  unfold recvCommit
  split
  · exact commPresC_fault ho hb
  · intro h
    simp only [continuePack, pack, mkRes, appendEvent]
    rw [ho]
    exact CommReachableC.step h (CommStepC.recv _ _ _ _ _ _ _ _ hd)

/-- Post-dequeue validation of receive preserves reachability. -/
theorem commPresC_recvAfterDequeue {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {lbl : Option Label} {dst : Reg} {hd : HandlerId} {tokens' : List ProgressToken}
    {sv : SignedValue ν} {bufs' : SignedBuffers ν}
    (hdq : bufDequeue st.buffers edge = some (sv, bufs')) :
    CommPresC st (recvAfterDequeue st coro ep edge T L' dst hd tokens' sv bufs' lbl) := by
  unfold recvAfterDequeue
  split
  · exact commPresC_fault rfl rfl
  split
  · exact commPresC_fault rfl rfl
  dsimp only
  split
  · split
    · exact commPresC_fault rfl rfl
    · next _ st' hc =>
      have hp := commConsume_preserves hc
      split
      · exact commPresC_recvCommit hp.1 hp.2 hdq
      · exact commPresC_fault hp.1 hp.2
  · exact commPresC_fault rfl rfl

/-- Receive handler stage preserves reachability. -/
theorem commPresC_recvWithHandler {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {T : ValType}
    {L' : LocalType} {lbl : Option Label} {dst : Reg} {hd : HandlerId} {tokens' : List ProgressToken} :
    CommPresC st (recvWithHandler st coro ep edge T L' dst hd tokens' lbl) := by
  unfold recvWithHandler
  cases hdq : bufDequeue st.buffers edge with
  | none => exact commPresC_block (st := st)
  | some r => obtain ⟨sv, bufs'⟩ := r; exact commPresC_recvAfterDequeue hdq

/-- **`stepReceive` refines `CommStepC`** (any buffer mode). -/
theorem commPresC_stepReceive {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan dst : Reg} :
    CommPresC st (stepReceive st coro chan dst) := by
  unfold stepReceive recvWithEndpoint recvOnEdge
  dsimp only
  repeat' split
  all_goals first
    | exact commPresC_block
    | exact commPresC_fault rfl rfl
    | exact commPresC_recvWithHandler (st := st)

/-! ## Offer pipeline -/

/-- Committing an enqueued offer matches `CommStepC.offer`. -/
theorem commPresC_offerCommit {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {L' : LocalType}
    {sv : SignedValue ν} {lbl : Label}
    (ho : st.obsTrace = st0.obsTrace) (hb : st.buffers = st0.buffers)
    (hp : sv.payload = .string lbl) :
    CommPresC st0 (offerCommit st coro ep edge
      (signedBufferSet st.buffers edge (signedBufferLookup st.buffers edge ++ [sv])) L' lbl) := by
  intro h
  simp only [offerCommit, continuePack, pack, mkRes, appendEvent]
  rw [ho, hb]
  exact CommReachableC.step h (CommStepC.offer _ _ _ _ _ _ hp)

/-- The enqueue-result dispatch of offer preserves reachability in FIFO mode. -/
theorem commPresC_offerAfterEnqueue {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {L' : LocalType}
    {lbl : Label} {hd : HandlerId} {sv : SignedValue ν}
    {res : SignedEnqueueResult} {bufs' : SignedBuffers ν}
    (ho : st.obsTrace = st0.obsTrace) (hb : st.buffers = st0.buffers)
    (hm : (st.config.bufferConfig edge).mode = .fifo)
    (hres : bufEnqueue (st.config.bufferConfig edge) st.buffers edge sv = (res, bufs'))
    (hp : sv.payload = .string lbl) :
    CommPresC st0 (offerAfterEnqueue st coro ep edge L' lbl hd res bufs') := by
  cases res with
  | ok =>
    have hbf := bufEnqueue_fifo_ok hm hres
    subst hbf
    simp only [offerAfterEnqueue]
    split
    · exact commPresC_fault ho hb
    · exact commPresC_offerCommit ho hb hp
  | blocked =>
    intro h; simpa [offerAfterEnqueue, blockPack, pack, mkRes, appendEvent, ho, hb] using h
  | dropped => simp only [offerAfterEnqueue]; exact commPresC_fault ho hb
  | error => simp only [offerAfterEnqueue]; exact commPresC_fault ho hb

/-- The handler stage of offer preserves reachability in FIFO mode. -/
theorem commPresC_offerOnHandler {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {L' : LocalType}
    {lbl : Label} {hd : HandlerId} (hf : AllFifo st) :
    CommPresC st (offerOnHandler st coro ep edge L' lbl hd) := by
  unfold offerOnHandler
  exact commPresC_offerAfterEnqueue (sv := signValue _ (.string lbl)) rfl rfl (hf edge) rfl rfl

/-- **`stepOffer` refines `CommStepC`** (FIFO mode): the real offer instruction,
followed by `appendEvent`, preserves extended communication reachability. -/
theorem commPresC_stepOffer {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan : Reg} {lbl : Label} (hf : AllFifo st) :
    CommPresC st (stepOffer st coro chan lbl) := by
  unfold stepOffer offerWithEndpoint offerOnEdge
  repeat' split
  all_goals first
    | exact commPresC_block
    | exact commPresC_fault rfl rfl
    | exact commPresC_offerOnHandler hf

/-! ## Choose pipeline -/

/-- Committing a dequeued choice matches `CommStepC.choose`. -/
theorem commPresC_chooseCommit {st st0 : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge} {L' : LocalType}
    {sv : SignedValue ν} {bufs' : SignedBuffers ν} {pc' : PC} {lbl : Label}
    (ho : st.obsTrace = st0.obsTrace) (hd : bufDequeue st0.buffers edge = some (sv, bufs'))
    (hp : sv.payload = .string lbl) :
    CommPresC st0 (chooseCommit st coro ep edge bufs' L' pc' lbl) := by
  intro h
  simp only [chooseCommit, pack, mkRes, appendEvent]
  rw [ho]
  exact CommReachableC.step h (CommStepC.choose _ _ _ _ _ _ _ hd hp)

/-- Post-dequeue validation of choose: either reachability is preserved, or
the pack is a fault (the dequeued message is dropped on an unknown label or a
non-string payload). -/
theorem commPresC_chooseAfterDequeue {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge}
    {choices : List (Label × LocalType)} {table : List (Label × PC)} {hd : HandlerId}
    {sv : SignedValue ν} {bufs' : SignedBuffers ν}
    (hdq : bufDequeue st.buffers edge = some (sv, bufs')) :
    CommPresOrFault st (chooseAfterDequeue st coro ep edge choices table hd sv bufs') := by
  unfold chooseAfterDequeue
  split
  · exact Or.inl (commPresC_fault rfl rfl)
  dsimp only
  split
  · split
    · next lbl hpay =>
      split
      · exact Or.inl (commPresC_chooseCommit rfl hdq hpay)
      · exact Or.inr isFaultPack_faultPack
    · exact Or.inr isFaultPack_faultPack
  · exact Or.inl (commPresC_fault rfl rfl)

/-- Choose handler stage: preserved or faulted. -/
theorem commPresC_chooseWithHandler {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {ep : Endpoint} {edge : Edge}
    {choices : List (Label × LocalType)} {table : List (Label × PC)} {hd : HandlerId}
    {token : ProgressToken} :
    CommPresOrFault st (chooseWithHandler st coro ep edge choices table hd token) := by
  unfold chooseWithHandler
  cases hdq : bufDequeue st.buffers edge with
  | none => exact Or.inl (commPresC_block (st := st))
  | some r => obtain ⟨sv, bufs'⟩ := r; exact commPresC_chooseAfterDequeue hdq

/-- **`stepChoose` refines `CommStepC` or faults**: the real choose instruction,
followed by `appendEvent`, preserves extended communication reachability unless
it reports a fault after dequeueing. -/
theorem commPresC_stepChoose {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan : Reg} {table : List (Label × PC)} :
    CommPresOrFault st (stepChoose st coro chan table) := by
  unfold stepChoose chooseWithEndpoint chooseOnEdge
  dsimp only
  repeat' split
  all_goals first
    | exact Or.inl commPresC_block
    | exact Or.inl (commPresC_fault rfl rfl)
    | exact commPresC_chooseWithHandler (st := st)

/-! ## Adequacy for real steps -/

/-- Extended conservation and combined FIFO after a real `stepOffer` (FIFO)
from an extended-reachable state. -/
theorem stepOffer_trace_adequacy {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan : Reg} {lbl : Label} (hf : AllFifo st)
    (h : CommReachableC ((st.obsTrace, st.buffers) : CommConfig ε ν)) :
    let p := stepOffer st coro chan lbl
    CommInvC (((appendEvent p.st p.res.event).obsTrace, p.st.buffers) : CommConfig ε ν) ∧
      RawFIFOC (appendEvent p.st p.res.event).obsTrace :=
  commReachableC_inv (commPresC_stepOffer hf h)

/-- Extended conservation and combined FIFO after a real `stepChoose` from an
extended-reachable state, unless the step faults. -/
theorem stepChoose_trace_adequacy {st : ProtocolMachineState ι γ π ε ν}
    {coro : CoroutineState γ ε} {chan : Reg} {table : List (Label × PC)}
    (h : CommReachableC ((st.obsTrace, st.buffers) : CommConfig ε ν)) :
    let p := stepChoose st coro chan table
    (CommInvC (((appendEvent p.st p.res.event).obsTrace, p.st.buffers) : CommConfig ε ν) ∧
      RawFIFOC (appendEvent p.st p.res.event).obsTrace) ∨ IsFaultPack p := by
  have hc : CommPresC st (stepChoose st coro chan table) ∨
      IsFaultPack (stepChoose st coro chan table) := commPresC_stepChoose
  rcases hc with hp | hf
  · exact Or.inl (commReachableC_inv (hp h))
  · exact Or.inr hf

end
