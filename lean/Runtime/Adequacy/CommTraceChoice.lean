import Runtime.Adequacy.CommTraceAdequacy

/-! # Runtime.Adequacy.CommTraceChoice

Communication reachability extended with label traffic. `offer` enqueues the
label `.string lbl` on the edge buffer and emits `offered`; `choose` dequeues
the buffer head and emits `chose`. Neither is a `sent`/`received` event, so the
value-only conservation law `CommInv` of `CommTraceAdequacy.lean` does not
survive them. This file generalises the per-edge projections to count both
kinds of traffic (`rawSentC`, `rawRecvC`), defines the extended step relation
`CommStepC`, and proves the extended conservation law `CommInvC` and the
extended raw FIFO property `RawFIFOC` for every `CommReachableC` configuration.

Scope (stated honestly): the observed FIFO property over `sent`/`received`
events alone (`FIFOConsistent`) is *not* derivable in the mixed setting from
the trace alone: a `received` event may consume an `offered` label (and a
`chose` event a `sent` string) when the endpoint types are inconsistent, which
only type-directed reasoning excludes. The conclusions here are therefore over
the combined label-and-value streams. `latestValue` buffer mode remains out of
scope (it overwrites in-flight messages), as do speculation rollback and loader
buffer resets.
-/

/-
The Problem. `CommStep.other` requires buffers untouched, so `offer`/`choose`
have no model in `CommReachable`.

Solution Structure. Generalise the projections, re-run the conservation and
FIFO arguments of `CommTraceAdequacy.lean` with the two extra constructors.
-/

set_option autoImplicit false

universe u

section

variable {ε ν : Type u} [EffectRuntime ε] [VerificationModel ν]

/-! ## Combined per-edge projections -/

/-- Values sent on `e`: `sent` payloads and `offered` labels (as strings). -/
def rawSentC (e : Edge) (t : List (TickedObsEvent ε)) : List Value :=
  t.filterMap fun ev => match ev.event with
    | .sent e' v _ _ => if e' = e then some v else none
    | .offered e' l => if e' = e then some (.string l) else none
    | _ => none

/-- Values consumed on `e`: `received` payloads and `chose` labels (as strings). -/
def rawRecvC (e : Edge) (t : List (TickedObsEvent ε)) : List Value :=
  t.filterMap fun ev => match ev.event with
    | .received e' v _ _ => if e' = e then some v else none
    | .chose e' l => if e' = e then some (.string l) else none
    | _ => none

/-- `rawSentC` distributes over append. -/
theorem rawSentC_append (e : Edge) (a b : List (TickedObsEvent ε)) :
    rawSentC e (a ++ b) = rawSentC e a ++ rawSentC e b := List.filterMap_append

/-- `rawRecvC` distributes over append. -/
theorem rawRecvC_append (e : Edge) (a b : List (TickedObsEvent ε)) :
    rawRecvC e (a ++ b) = rawRecvC e a ++ rawRecvC e b := List.filterMap_append

/-! ## Single-event projections -/

/-- Combined send projection of a `sent` event. -/
theorem rawSentC_single_sent (e e' : Edge) (v : Value) (tick seq : Nat) (lbl : Option Label) :
    rawSentC (ε:=ε) e' [⟨tick, .sent e v seq lbl⟩] = if e = e' then [v] else [] := by
  by_cases h : e = e' <;> simp [rawSentC, h]

/-- Combined receive projection of a `sent` event. -/
theorem rawRecvC_single_sent (e e' : Edge) (v : Value) (tick seq : Nat) (lbl : Option Label) :
    rawRecvC (ε:=ε) e' [⟨tick, .sent e v seq lbl⟩] = [] := by simp [rawRecvC]

/-- Combined send projection of a `received` event. -/
theorem rawSentC_single_recv (e e' : Edge) (v : Value) (tick seq : Nat) (lbl : Option Label) :
    rawSentC (ε:=ε) e' [⟨tick, .received e v seq lbl⟩] = [] := by simp [rawSentC]

/-- Combined receive projection of a `received` event. -/
theorem rawRecvC_single_recv (e e' : Edge) (v : Value) (tick seq : Nat) (lbl : Option Label) :
    rawRecvC (ε:=ε) e' [⟨tick, .received e v seq lbl⟩] = if e = e' then [v] else [] := by
  by_cases h : e = e' <;> simp [rawRecvC, h]

/-- Combined send projection of an `offered` event. -/
theorem rawSentC_single_offered (e e' : Edge) (l : Label) (tick : Nat) :
    rawSentC (ε:=ε) e' [⟨tick, .offered e l⟩] = if e = e' then [.string l] else [] := by
  by_cases h : e = e' <;> simp [rawSentC, h]

/-- Combined receive projection of an `offered` event. -/
theorem rawRecvC_single_offered (e e' : Edge) (l : Label) (tick : Nat) :
    rawRecvC (ε:=ε) e' [⟨tick, .offered e l⟩] = [] := by simp [rawRecvC]

/-- Combined send projection of a `chose` event. -/
theorem rawSentC_single_chose (e e' : Edge) (l : Label) (tick : Nat) :
    rawSentC (ε:=ε) e' [⟨tick, .chose e l⟩] = [] := by simp [rawSentC]

/-- Combined receive projection of a `chose` event. -/
theorem rawRecvC_single_chose (e e' : Edge) (l : Label) (tick : Nat) :
    rawRecvC (ε:=ε) e' [⟨tick, .chose e l⟩] = if e = e' then [.string l] else [] := by
  by_cases h : e = e' <;> simp [rawRecvC, h]

/-! ## Extended step relation -/

/-- One committed communication step, including label traffic. -/
inductive CommStepC : CommConfig ε ν → CommConfig ε ν → Prop
  /-- FIFO send: enqueue at tail, emit `sent`. -/
  | send (t : List (TickedObsEvent ε)) (bufs : SignedBuffers ν) (e : Edge)
      (sv : SignedValue ν) (tick seq : Nat) (lbl : Option Label) :
      CommStepC (t, bufs) (t ++ [⟨tick, .sent e sv.payload seq lbl⟩],
        signedBufferSet bufs e (signedBufferLookup bufs e ++ [sv]))
  /-- Receive: dequeue head, emit `received`. -/
  | recv (t : List (TickedObsEvent ε)) (bufs bufs' : SignedBuffers ν) (e : Edge)
      (sv : SignedValue ν) (tick seq : Nat) (lbl : Option Label) (h : bufDequeue bufs e = some (sv, bufs')) :
      CommStepC (t, bufs) (t ++ [⟨tick, .received e sv.payload seq lbl⟩], bufs')
  /-- FIFO offer: enqueue the label at the tail, emit `offered`. -/
  | offer (t : List (TickedObsEvent ε)) (bufs : SignedBuffers ν) (e : Edge)
      (sv : SignedValue ν) (lbl : Label) (tick : Nat) (hp : sv.payload = .string lbl) :
      CommStepC (t, bufs) (t ++ [⟨tick, .offered e lbl⟩],
        signedBufferSet bufs e (signedBufferLookup bufs e ++ [sv]))
  /-- Choose: dequeue the head label, emit `chose`. -/
  | choose (t : List (TickedObsEvent ε)) (bufs bufs' : SignedBuffers ν) (e : Edge)
      (sv : SignedValue ν) (lbl : Label) (tick : Nat)
      (h : bufDequeue bufs e = some (sv, bufs')) (hp : sv.payload = .string lbl) :
      CommStepC (t, bufs) (t ++ [⟨tick, .chose e lbl⟩], bufs')
  /-- Any non-communication event, buffers untouched. -/
  | other (t : List (TickedObsEvent ε)) (bufs : SignedBuffers ν) (ev : TickedObsEvent ε)
      (hs : ∀ e, rawSentC e [ev] = []) (hr : ∀ e, rawRecvC e [ev] = []) :
      CommStepC (t, bufs) (t ++ [ev], bufs)

/-- Configurations reachable from an empty trace and empty buffers by
`CommStepC` steps. -/
inductive CommReachableC : CommConfig ε ν → Prop
  | init (bufs : SignedBuffers ν) (h : ∀ e, signedBufferLookup bufs e = []) :
      CommReachableC ([], bufs)
  | step {c c' : CommConfig ε ν} : CommReachableC c → CommStepC c c' → CommReachableC c'

/-- Per-edge conservation including labels: sent-or-offered = received-or-chosen ++ in-flight. -/
def CommInvC (c : CommConfig ε ν) : Prop :=
  ∀ e, rawSentC e c.1 = rawRecvC e c.1 ++ (signedBufferLookup c.2 e).map (·.payload)

/-! ## Invariant preservation -/

/-- Enqueueing one value whose only projection is a single send on `e` preserves
conservation. -/
theorem commInvC_enqueue {t : List (TickedObsEvent ε)} {bufs : SignedBuffers ν} {e : Edge}
    {sv : SignedValue ν} {ev : TickedObsEvent ε}
    (hs : ∀ e', rawSentC e' [ev] = if e = e' then [sv.payload] else [])
    (hr : ∀ e', rawRecvC e' [ev] = []) (hI : CommInvC (t, bufs)) :
    CommInvC ((t ++ [ev], signedBufferSet bufs e (signedBufferLookup bufs e ++ [sv])) :
      CommConfig ε ν) := by
  intro e'
  have h := hI e'
  simp only at h ⊢
  rw [rawSentC_append, rawRecvC_append, h, hs e', hr e']
  by_cases he : e = e'
  · subst he; simp [lookup_set_same]
  · simp [he, lookup_set_other _ _ (Ne.symm he)]

/-- Dequeueing the head with a single receive projection on `e` preserves conservation. -/
theorem commInvC_dequeue {t : List (TickedObsEvent ε)} {bufs bufs' : SignedBuffers ν} {e : Edge}
    {sv : SignedValue ν} {ev : TickedObsEvent ε} (hd : bufDequeue bufs e = some (sv, bufs'))
    (hs : ∀ e', rawSentC e' [ev] = [])
    (hr : ∀ e', rawRecvC e' [ev] = if e = e' then [sv.payload] else [])
    (hI : CommInvC (t, bufs)) : CommInvC ((t ++ [ev], bufs') : CommConfig ε ν) := by
  intro e'
  have h := hI e'
  obtain ⟨h1, h2⟩ := bufDequeue_spec hd
  simp only at h ⊢
  rw [rawSentC_append, rawRecvC_append, h, hs e', hr e']
  by_cases he : e = e'
  · subst he; simp [h1]
  · simp [he, h2 e' (Ne.symm he)]

/-- Non-communication events preserve conservation. -/
theorem commInvC_other {t : List (TickedObsEvent ε)} {bufs : SignedBuffers ν}
    {ev : TickedObsEvent ε} (hs : ∀ e, rawSentC e [ev] = []) (hr : ∀ e, rawRecvC e [ev] = [])
    (hI : CommInvC (t, bufs)) : CommInvC ((t ++ [ev], bufs) : CommConfig ε ν) := by
  intro e
  have h := hI e
  simp only at h ⊢
  rw [rawSentC_append, rawRecvC_append, hs e, hr e, h]
  simp

/-- Every extended step preserves conservation. -/
theorem commInvC_step {c c' : CommConfig ε ν} (hs : CommStepC c c') (hI : CommInvC c) :
    CommInvC c' := by
  cases hs with
  | send t bufs e sv tick seq lbl =>
    exact commInvC_enqueue (fun e' => rawSentC_single_sent e e' _ tick seq lbl)
      (fun e' => rawRecvC_single_sent e e' _ tick seq lbl) hI
  | recv t bufs bufs' e sv tick seq lbl hd =>
    exact commInvC_dequeue hd (fun e' => rawSentC_single_recv e e' _ tick seq lbl)
      (fun e' => rawRecvC_single_recv e e' _ tick seq lbl) hI
  | offer t bufs e sv lbl tick hp =>
    exact commInvC_enqueue (fun e' => by rw [hp]; exact rawSentC_single_offered e e' lbl tick)
      (fun e' => rawRecvC_single_offered e e' lbl tick) hI
  | choose t bufs bufs' e sv lbl tick hd hp =>
    exact commInvC_dequeue hd (fun e' => rawSentC_single_chose e e' lbl tick)
      (fun e' => by rw [hp]; exact rawRecvC_single_chose e e' lbl tick) hI
  | other _ _ _ hs' hr' => exact commInvC_other hs' hr' hI

/-- Every extended step appends exactly one event. -/
theorem commStepC_append {c c' : CommConfig ε ν} (hs : CommStepC c c') :
    ∃ x, c'.1 = c.1 ++ [x] := by
  cases hs <;> exact ⟨_, rfl⟩

/-! ## Combined FIFO -/

/-- Combined per-edge FIFO at every prefix. -/
def RawFIFOC (t : List (TickedObsEvent ε)) : Prop :=
  ∀ k e, rawRecvC e (t.take k) <+: rawSentC e (t.take k)

/-- Extending a combined-FIFO trace by one conserving event keeps combined FIFO. -/
theorem rawFIFOC_snoc {t : List (TickedObsEvent ε)} {x : TickedObsEvent ε}
    (hF : RawFIFOC t) (hE : ∀ e, rawRecvC e (t ++ [x]) <+: rawSentC e (t ++ [x])) :
    RawFIFOC (t ++ [x]) := by
  intro k e
  by_cases hk : k ≤ t.length
  · rw [List.take_append_of_le_length hk]; exact hF k e
  · rw [List.take_of_length_le (by simp; omega)]; exact hE e

/-- **Extended trace adequacy.** Every `CommReachableC` configuration satisfies
combined conservation and combined raw FIFO. -/
theorem commReachableC_inv {c : CommConfig ε ν} (h : CommReachableC c) :
    CommInvC c ∧ RawFIFOC c.1 := by
  induction h with
  | init bufs hb =>
    exact ⟨fun e => by simp [rawSentC, rawRecvC, hb], fun k e => by simp [rawSentC, rawRecvC]⟩
  | @step c c' _ hs ih =>
    have hI := commInvC_step hs ih.1
    obtain ⟨x, hx⟩ := commStepC_append hs
    refine ⟨hI, ?_⟩
    have hE : ∀ e, rawRecvC e c'.1 <+: rawSentC e c'.1 := fun e => ⟨_, (hI e).symm⟩
    rw [hx] at hE ⊢
    exact rawFIFOC_snoc ih.2 hE

end
