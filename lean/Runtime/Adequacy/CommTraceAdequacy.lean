import Runtime.Adequacy.Adequacy
import Runtime.ProtocolMachine.Semantics.ExecHelpers

/-! # Runtime.Adequacy.CommTraceAdequacy

Reachability-based trace adequacy for the communication fragment of the
protocol machine: every configuration reachable from empty buffers and an empty
observable trace, via FIFO-mode enqueue-at-send and dequeue-head-at-receive
steps (using the machine's own `signedBufferSet`/`signedBufferLookup`/
`bufDequeue`), has a causally and per-edge FIFO consistent observable trace.

Scope (stated honestly): the step relation `CommStep` models the buffer and
trace effect of a committed send/receive and of any non-communication event that
leaves buffers untouched. It does not cover `latestValue` buffer mode (which
overwrites in-flight messages, so FIFO genuinely fails there), speculation
rollback (trace truncation), loader-side buffer resets, or failure injection.
`bufEnqueue_fifo_ok` ties the send step to the machine's real `bufEnqueue`.
-/

/-
The Problem. The previous adequacy theorem took its own conclusion as
hypotheses. `WFVMState` does not constrain the observable trace at all, so
adequacy must come from the communication semantics.

Solution Structure. Define a reachability relation over (trace, buffers), prove
the conservation invariant "sent = received ++ buffered" per edge, and derive
FIFO and causality.
-/

set_option autoImplicit false

universe u

section

variable {ε ν : Type u} [EffectRuntime ε] [VerificationModel ν]

/-! ## Raw per-edge projections -/

/-- Payloads sent on `e` in a raw machine trace. -/
def rawSent (e : Edge) (t : List (TickedObsEvent ε)) : List Value :=
  t.filterMap fun ev => match ev.event with
    | .sent e' v _ _ => if e' = e then some v else none
    | _ => none

/-- Payloads received on `e` in a raw machine trace. -/
def rawRecv (e : Edge) (t : List (TickedObsEvent ε)) : List Value :=
  t.filterMap fun ev => match ev.event with
    | .received e' v _ _ => if e' = e then some v else none
    | _ => none

/-- `rawSent` distributes over append. -/
theorem rawSent_append (e : Edge) (a b : List (TickedObsEvent ε)) :
    rawSent e (a ++ b) = rawSent e a ++ rawSent e b := List.filterMap_append

/-- `rawRecv` distributes over append. -/
theorem rawRecv_append (e : Edge) (a b : List (TickedObsEvent ε)) :
    rawRecv e (a ++ b) = rawRecv e a ++ rawRecv e b := List.filterMap_append

/-! ## Relating raw and observed traces -/

/-- Observation commutes with `take`. -/
theorem obsTraceOf_go_take (t : List (TickedObsEvent ε)) (idx k : Nat) :
    (obsTraceOf.go idx t).take k = obsTraceOf.go idx (t.take k) := by
  induction t generalizing idx k with
  | nil => simp [obsTraceOf.go]
  | cons hd tl ih =>
    cases k with
    | zero => simp [obsTraceOf.go]
    | succ k =>
      show ((idx, observeAt idx hd) :: obsTraceOf.go (idx + 1) tl).take (k + 1) =
        (idx, observeAt idx hd) :: obsTraceOf.go (idx + 1) (tl.take k)
      rw [List.take_succ_cons, ih]

/-- Observed sends coincide with raw sends. -/
theorem sentOn_go (e : Edge) (t : List (TickedObsEvent ε)) (idx : Nat) :
    sentOn e (obsTraceOf.go idx t) = rawSent e t := by
  induction t generalizing idx with
  | nil => simp [obsTraceOf.go, sentOn, rawSent]
  | cons hd tl ih =>
    have hdef : obsTraceOf.go idx (hd :: tl) =
      (idx, observeAt idx hd) :: obsTraceOf.go (idx + 1) tl := rfl
    have ih' := ih (idx + 1)
    simp only [sentOn, rawSent] at ih' ⊢
    rw [hdef, List.filterMap_cons, List.filterMap_cons, ih']
    obtain ⟨tk, ev⟩ := hd
    cases ev <;> simp [observeAt, obsWithSeqNo]

/-- Observed receives coincide with raw receives. -/
theorem recvOn_go (e : Edge) (t : List (TickedObsEvent ε)) (idx : Nat) :
    recvOn e (obsTraceOf.go idx t) = rawRecv e t := by
  induction t generalizing idx with
  | nil => simp [obsTraceOf.go, recvOn, rawRecv]
  | cons hd tl ih =>
    have hdef : obsTraceOf.go idx (hd :: tl) =
      (idx, observeAt idx hd) :: obsTraceOf.go (idx + 1) tl := rfl
    have ih' := ih (idx + 1)
    simp only [recvOn, rawRecv] at ih' ⊢
    rw [hdef, List.filterMap_cons, List.filterMap_cons, ih']
    obtain ⟨tk, ev⟩ := hd
    cases ev <;> simp [observeAt, obsWithSeqNo]

/-! ## Buffer lemmas over the machine's signed buffers -/

/-- Setting an edge's buffer then looking it up returns the new contents. -/
theorem lookup_set_same (bufs : SignedBuffers ν) (e : Edge) (l : SignedBuffer ν) :
    signedBufferLookup (signedBufferSet bufs e l) e = l := by
  induction bufs with
  | nil => simp [signedBufferSet, signedBufferLookup]
  | cons p rest ih =>
    obtain ⟨x, vs⟩ := p
    by_cases hx : x = e <;> simp [signedBufferSet, signedBufferLookup, hx, ih]

/-- Setting an edge's buffer leaves other edges unchanged. -/
theorem lookup_set_other (bufs : SignedBuffers ν) {e e' : Edge} (l : SignedBuffer ν)
    (hne : e' ≠ e) :
    signedBufferLookup (signedBufferSet bufs e l) e' = signedBufferLookup bufs e' := by
  induction bufs with
  | nil => simp [signedBufferSet, signedBufferLookup, Ne.symm hne]
  | cons p rest ih =>
    obtain ⟨x, vs⟩ := p
    by_cases hx : x = e
    · subst hx; simp [signedBufferSet, signedBufferLookup, Ne.symm hne]
    · simp [signedBufferSet, signedBufferLookup, hx, ih]

/-- `bufDequeue` removes exactly the head of the edge's buffer. -/
theorem bufDequeue_spec {e : Edge} {sv : SignedValue ν} :
    ∀ {bufs bufs' : SignedBuffers ν}, bufDequeue bufs e = some (sv, bufs') →
      signedBufferLookup bufs e = sv :: signedBufferLookup bufs' e ∧
      ∀ e', e' ≠ e → signedBufferLookup bufs' e' = signedBufferLookup bufs e'
  | [], _, h => by simp [bufDequeue] at h
  | (x, vs) :: rest, bufs', h => by
    by_cases hx : x = e
    · subst hx
      cases vs with
      | nil => simp [bufDequeue] at h
      | cons v vs' =>
        simp [bufDequeue] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp [signedBufferLookup],
          fun e' hne => by simp [signedBufferLookup, Ne.symm hne]⟩
    · cases hd : bufDequeue rest e with
      | none => simp [bufDequeue, hx, hd] at h
      | some r =>
        obtain ⟨v, rest'⟩ := r
        simp [bufDequeue, hx, hd] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := bufDequeue_spec hd
        refine ⟨by simp [signedBufferLookup, hx, h1], fun e' hne => ?_⟩
        by_cases hx' : x = e' <;> simp [signedBufferLookup, hx', h2 e' hne]

/-- A successful FIFO-mode `bufEnqueue` appends at the tail of the edge buffer. -/
theorem bufEnqueue_fifo_ok {cfg : BufferConfig} {bufs bufs' : SignedBuffers ν}
    {e : Edge} {v : SignedValue ν} (hm : cfg.mode = .fifo)
    (h : bufEnqueue cfg bufs e v = (.ok, bufs')) :
    bufs' = signedBufferSet bufs e (signedBufferLookup bufs e ++ [v]) := by
  unfold bufEnqueue at h
  rw [hm] at h
  simp only at h
  split at h
  · exact (Prod.mk.inj h).2.symm
  · split at h <;> simp at h

/-! ## Communication reachability -/

/-- Communication configuration: raw observable trace and signed buffers. -/
abbrev CommConfig (ε ν : Type u) [EffectRuntime ε] [VerificationModel ν] :=
  List (TickedObsEvent ε) × SignedBuffers ν

/-- One committed communication-relevant machine step. -/
inductive CommStep : CommConfig ε ν → CommConfig ε ν → Prop
  /-- FIFO send: enqueue at tail, emit `sent`. -/
  | send (t : List (TickedObsEvent ε)) (bufs : SignedBuffers ν) (e : Edge)
      (sv : SignedValue ν) (tick seq : Nat) (lbl : Option Label) :
      CommStep (t, bufs) (t ++ [⟨tick, .sent e sv.payload seq lbl⟩],
        signedBufferSet bufs e (signedBufferLookup bufs e ++ [sv]))
  /-- Receive: dequeue head, emit `received` of that payload. -/
  | recv (t : List (TickedObsEvent ε)) (bufs bufs' : SignedBuffers ν) (e : Edge)
      (sv : SignedValue ν) (tick seq : Nat) (lbl : Option Label) (h : bufDequeue bufs e = some (sv, bufs')) :
      CommStep (t, bufs) (t ++ [⟨tick, .received e sv.payload seq lbl⟩], bufs')
  /-- Any non-send/receive event, buffers untouched. -/
  | other (t : List (TickedObsEvent ε)) (bufs : SignedBuffers ν) (ev : TickedObsEvent ε)
      (hs : ∀ e, rawSent e [ev] = []) (hr : ∀ e, rawRecv e [ev] = []) :
      CommStep (t, bufs) (t ++ [ev], bufs)

/-- Configurations reachable from an empty trace and empty buffers. -/
inductive CommReachable : CommConfig ε ν → Prop
  | init (bufs : SignedBuffers ν) (h : ∀ e, signedBufferLookup bufs e = []) :
      CommReachable ([], bufs)
  | step {c c' : CommConfig ε ν} : CommReachable c → CommStep c c' → CommReachable c'

/-- Per-edge conservation: sent = received ++ in-flight. -/
def CommInv (c : CommConfig ε ν) : Prop :=
  ∀ e, rawSent e c.1 = rawRecv e c.1 ++ (signedBufferLookup c.2 e).map (·.payload)

/-! ## Invariant preservation -/

/-- Raw send projection of a single `sent` event. -/
theorem rawSent_single_sent (e e' : Edge) (v : Value) (tick seq : Nat) (lbl : Option Label) :
    rawSent (ε:=ε) e' [⟨tick, .sent e v seq lbl⟩] = if e = e' then [v] else [] := by
  by_cases h : e = e' <;> simp [rawSent, h]

/-- Raw receive projection of a single `sent` event. -/
theorem rawRecv_single_sent (e e' : Edge) (v : Value) (tick seq : Nat) (lbl : Option Label) :
    rawRecv (ε:=ε) e' [⟨tick, .sent e v seq lbl⟩] = [] := by
  simp [rawRecv]

/-- Raw send projection of a single `received` event. -/
theorem rawSent_single_recv (e e' : Edge) (v : Value) (tick seq : Nat) (lbl : Option Label) :
    rawSent (ε:=ε) e' [⟨tick, .received e v seq lbl⟩] = [] := by
  simp [rawSent]

/-- Raw receive projection of a single `received` event. -/
theorem rawRecv_single_recv (e e' : Edge) (v : Value) (tick seq : Nat) (lbl : Option Label) :
    rawRecv (ε:=ε) e' [⟨tick, .received e v seq lbl⟩] = if e = e' then [v] else [] := by
  by_cases h : e = e' <;> simp [rawRecv, h]

/-- A FIFO send preserves conservation. -/
theorem commInv_send {t : List (TickedObsEvent ε)} {bufs : SignedBuffers ν} {e : Edge}
    {sv : SignedValue ν} {tick seq : Nat} {lbl : Option Label} (hI : CommInv (t, bufs)) :
    CommInv ((t ++ [⟨tick, .sent e sv.payload seq lbl⟩],
      signedBufferSet bufs e (signedBufferLookup bufs e ++ [sv])) : CommConfig ε ν) := by
  intro e'
  have h := hI e'
  simp only at h ⊢
  rw [rawSent_append, rawRecv_append, h, rawSent_single_sent, rawRecv_single_sent]
  by_cases he : e = e'
  · subst he; simp [lookup_set_same]
  · simp [he, lookup_set_other _ _ (Ne.symm he)]

/-- A head-dequeuing receive preserves conservation. -/
theorem commInv_recv {t : List (TickedObsEvent ε)} {bufs bufs' : SignedBuffers ν} {e : Edge}
    {sv : SignedValue ν} {tick seq : Nat} {lbl : Option Label} (hd : bufDequeue bufs e = some (sv, bufs'))
    (hI : CommInv (t, bufs)) :
    CommInv ((t ++ [⟨tick, .received e sv.payload seq lbl⟩], bufs') : CommConfig ε ν) := by
  intro e'
  have h := hI e'
  obtain ⟨h1, h2⟩ := bufDequeue_spec hd
  simp only at h ⊢
  rw [rawSent_append, rawRecv_append, h, rawSent_single_recv, rawRecv_single_recv]
  by_cases he : e = e'
  · subst he; simp [h1]
  · simp [he, h2 e' (Ne.symm he)]

/-- Non-communication events preserve conservation. -/
theorem commInv_other {t : List (TickedObsEvent ε)} {bufs : SignedBuffers ν}
    {ev : TickedObsEvent ε} (hs : ∀ e, rawSent e [ev] = []) (hr : ∀ e, rawRecv e [ev] = [])
    (hI : CommInv (t, bufs)) : CommInv ((t ++ [ev], bufs) : CommConfig ε ν) := by
  intro e
  have h := hI e
  simp only at h ⊢
  rw [rawSent_append, rawRecv_append, hs e, hr e, h]
  simp

/-- Every step preserves conservation. -/
theorem commInv_step {c c' : CommConfig ε ν} (hs : CommStep c c') (hI : CommInv c) :
    CommInv c' := by
  cases hs with
  | send => exact commInv_send hI
  | recv _ _ _ _ _ _ _ _ hd => exact commInv_recv hd hI
  | other _ _ _ hs' hr' => exact commInv_other hs' hr' hI

/-- Every step appends exactly one event to the trace. -/
theorem commStep_append {c c' : CommConfig ε ν} (hs : CommStep c c') :
    ∃ x, c'.1 = c.1 ++ [x] := by
  cases hs <;> exact ⟨_, rfl⟩

/-! ## Reachable traces are FIFO and causal -/

/-- Raw per-edge FIFO at every prefix. -/
def RawFIFO (t : List (TickedObsEvent ε)) : Prop :=
  ∀ k e, rawRecv e (t.take k) <+: rawSent e (t.take k)

/-- Extending a raw-FIFO trace by one event that satisfies conservation keeps
raw FIFO at every prefix. -/
theorem rawFIFO_snoc {t : List (TickedObsEvent ε)} {x : TickedObsEvent ε}
    (hF : RawFIFO t) (hE : ∀ e, rawRecv e (t ++ [x]) <+: rawSent e (t ++ [x])) :
    RawFIFO (t ++ [x]) := by
  intro k e
  by_cases hk : k ≤ t.length
  · rw [List.take_append_of_le_length hk]; exact hF k e
  · rw [List.take_of_length_le (by simp; omega)]; exact hE e

/-- Reachable configurations satisfy conservation and raw FIFO. -/
theorem commReachable_inv {c : CommConfig ε ν} (h : CommReachable c) :
    CommInv c ∧ RawFIFO c.1 := by
  induction h with
  | init bufs hb =>
    exact ⟨fun e => by simp [rawSent, rawRecv, hb], fun k e => by simp [rawSent, rawRecv]⟩
  | @step c c' _ hs ih =>
    have hI := commInv_step hs ih.1
    obtain ⟨x, hx⟩ := commStep_append hs
    refine ⟨hI, ?_⟩
    have hE : ∀ e, rawRecv e c'.1 <+: rawSent e c'.1 := fun e => ⟨_, (hI e).symm⟩
    rw [hx] at hE ⊢
    exact rawFIFO_snoc ih.2 hE

/-- Observed FIFO consistency follows from raw FIFO. -/
theorem fifo_of_rawFIFO {t : List (TickedObsEvent ε)} (h : RawFIFO t) :
    FIFOConsistent (obsTraceOf t) := by
  intro k e
  show recvOn e ((obsTraceOf.go 0 t).take k) <+: sentOn e ((obsTraceOf.go 0 t).take k)
  rw [obsTraceOf_go_take, sentOn_go, recvOn_go]
  exact h k e

/-- **Adequacy (communication fragment).** Every configuration reachable from an
empty trace and empty buffers via FIFO send / head-dequeue receive / buffer-neutral
steps has a causally and per-edge FIFO consistent observable trace. -/
theorem comm_trace_adequacy {c : CommConfig ε ν} (h : CommReachable c) :
    CausallyConsistent (obsTraceOf c.1) ∧ FIFOConsistent (obsTraceOf c.1) := by
  have hF := fifo_of_rawFIFO (commReachable_inv h).2
  exact ⟨causallyConsistent_of_fifo hF, hF⟩

end

/-! ## Machine-state statement -/

/-- protocol machine adequacy: a machine state whose (trace, buffers) pair is
communication-reachable has a causally and FIFO consistent observable trace. -/
theorem protocol_machine_adequacy {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν]
    [AccumulatedSet ν] [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν)
    (h : CommReachable ((st.obsTrace, st.buffers) : CommConfig ε ν)) :
    CausallyConsistent (obsTraceOf st.obsTrace) ∧ FIFOConsistent (obsTraceOf st.obsTrace) :=
  comm_trace_adequacy h
