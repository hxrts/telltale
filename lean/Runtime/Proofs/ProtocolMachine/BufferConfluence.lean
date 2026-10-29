import Runtime.Proofs.ProtocolMachine.Scheduler
import Runtime.Adequacy.CommTraceAdequacy

/-! # Buffer-level confluence of the real machine's send/receive effects

Instantiates `LocalStepSystem` for the machine's signed buffers, viewed
per-edge through `signedBufferLookup`. A FIFO enqueue (`bufEnqueue` in FIFO
mode, as used by `stepSend`) and a head dequeue (`bufDequeue`, as used by
`stepReceive`) are each footprint-local to their edge, so by
`LocalStepSystem.independent_steps_commute` buffer effects on distinct edges
commute.

Scope (stated honestly): this is confluence of the *buffer* component only.
Whole-state confluence of `execInstr` is false as stated: the observable trace,
clock, and replay/sequence bookkeeping record the order in which steps run, so
two interleavings differ in `obsTrace` (they agree only up to a permutation of
independent events). Register/session-store locality is not covered here.
-/

set_option autoImplicit false

universe u

section

variable {ν : Type u} [VerificationModel ν]

/-- A buffer operation on one edge. -/
inductive BufOp (ν : Type u) [VerificationModel ν]
  /-- FIFO enqueue of a signed value. -/
  | enq (e : Edge) (sv : SignedValue ν)
  /-- Head dequeue. -/
  | deq (e : Edge)

/-- The edge an operation touches. -/
def BufOp.edge : BufOp ν → Edge
  | .enq e _ => e
  | .deq e => e

/-- Per-edge view of the machine's signed buffers. -/
def bufView (bufs : SignedBuffers ν) : Edge → SignedBuffer ν :=
  fun e => signedBufferLookup bufs e

/-- The buffer step system: footprint = the operation's edge. -/
def bufStepSystem : LocalStepSystem Edge (SignedBuffer ν) (BufOp ν) where
  footprint c l := decide (l = c.edge)
  effect c s l := match c with
    | .enq _ sv => s l ++ [sv]
    | .deq _ => (s l).tail
  effect_local c s s' h l hl := by
    have := h l hl
    cases c <;> simp [this]

/-- A FIFO enqueue on the real buffers is the `enq` step on the per-edge view. -/
theorem bufView_enq (bufs : SignedBuffers ν) (e : Edge) (sv : SignedValue ν) :
    bufView (signedBufferSet bufs e (signedBufferLookup bufs e ++ [sv])) =
      bufStepSystem.step (.enq e sv) (bufView bufs) := by
  funext l
  by_cases h : l = e
  · subst h; simp [bufView, LocalStepSystem.step, bufStepSystem, BufOp.edge, lookup_set_same]
  · simp [bufView, LocalStepSystem.step, bufStepSystem, BufOp.edge, h, lookup_set_other _ _ h]

/-- A successful real `bufDequeue` is the `deq` step on the per-edge view. -/
theorem bufView_deq {bufs bufs' : SignedBuffers ν} {e : Edge} {sv : SignedValue ν}
    (hd : bufDequeue bufs e = some (sv, bufs')) :
    bufView bufs' = bufStepSystem.step (.deq e) (bufView bufs) := by
  obtain ⟨h1, h2⟩ := bufDequeue_spec hd
  funext l
  by_cases h : l = e
  · subst h; simp [bufView, LocalStepSystem.step, bufStepSystem, BufOp.edge, h1]
  · simp [bufView, LocalStepSystem.step, bufStepSystem, BufOp.edge, h, h2 l h]

/-- Operations on distinct edges are independent. -/
theorem bufOp_independent {c₁ c₂ : BufOp ν} (h : c₁.edge ≠ c₂.edge) :
    bufStepSystem.Independent c₁ c₂ := by
  intro l ⟨h₁, h₂⟩
  simp [bufStepSystem] at h₁ h₂
  exact h (h₁ ▸ h₂)

/-- **Confluence of real buffer effects.** Machine buffer operations on
distinct edges commute on the per-edge buffer view. -/
theorem buffer_ops_commute {c₁ c₂ : BufOp ν} (h : c₁.edge ≠ c₂.edge)
    (bufs : SignedBuffers ν) :
    bufStepSystem.step c₂ (bufStepSystem.step c₁ (bufView bufs)) =
      bufStepSystem.step c₁ (bufStepSystem.step c₂ (bufView bufs)) :=
  bufStepSystem.independent_steps_commute (bufOp_independent h) _

/-- Two real FIFO enqueues on distinct edges commute on the buffer view. -/
theorem fifo_enqueues_commute (bufs : SignedBuffers ν) {e₁ e₂ : Edge}
    (sv₁ sv₂ : SignedValue ν) (h : e₁ ≠ e₂) :
    let b₁ := signedBufferSet bufs e₁ (signedBufferLookup bufs e₁ ++ [sv₁])
    let b₂ := signedBufferSet bufs e₂ (signedBufferLookup bufs e₂ ++ [sv₂])
    bufView (signedBufferSet b₁ e₂ (signedBufferLookup b₁ e₂ ++ [sv₂])) =
      bufView (signedBufferSet b₂ e₁ (signedBufferLookup b₂ e₁ ++ [sv₁])) := by
  simp only [bufView_enq]
  exact buffer_ops_commute (c₁ := .enq e₁ sv₁) (c₂ := .enq e₂ sv₂) h bufs

end
