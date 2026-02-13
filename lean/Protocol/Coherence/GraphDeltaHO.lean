import Protocol.Coherence.GraphDeltaCore

/-! # Protocol.Coherence.GraphDeltaHO

Higher-order coherence and realizability results layered on top of
`GraphDeltaCore` consume/delta definitions.
-/

/-
The Problem. Higher-order consume introduces graph deltas when channel values
are delegated, so we need realizability preservation and coherence bridge
results that show this extension remains conservative over channel-free traces.

Solution Structure. First prove realizability composition/preservation, then
package higher-order edge/global coherence, and finally prove the HO↔FO
conservative-extension bridge under no-channel assumptions.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section
/-! ## Realizability Preservation -/

/-- Realizability is preserved under composition. -/
theorem GraphDelta_realizable_compose (d1 d2 : GraphDelta) (env : SessionEnv) :
    d1.realizable env → d2.realizable env → (d1.compose d2).realizable env := by
  intro h1 h2
  constructor
  · -- Added edges from either delta are realizable
    intro e he
    simp [GraphDelta.compose] at he
    cases he with
    | inl he1 => exact h1.1 e he1
    | inr he2 => exact h2.1 e he2
  · -- Removed edges from either delta are realizable
    intro e he
    simp [GraphDelta.compose] at he
    cases he with
    | inl he1 => exact h1.2 e he1
    | inr he2 => exact h2.2 e he2

/-- consumeOneHO produces realizable deltas when the channel is well-formed. -/
lemma consumeOneHO_realizable (from_ receiver : Role) (T : ValType) (L : LocalType)
    (env : SessionEnv)
    (hT : match T with
      | .chan sid role => env.hasRole sid role ∧ env.hasRole sid receiver
      | _ => True)
    (res : ConsumeResult)
    (h : consumeOneHO from_ receiver T L = some res) :
    res.delta.realizable env := by
  cases L with
  | recv r T' L' =>
    by_cases hEq : from_ == r && T == T'
    · cases T with
      | chan sid role =>
        simp [consumeOneHO, hEq] at h
        cases h
        rcases hT with ⟨hRole, hReceiver⟩
        constructor
        · intro e he
          simp at he
          rcases he with rfl | rfl
          · exact ⟨hRole, hReceiver⟩
          · exact ⟨hReceiver, hRole⟩
        · intro e he
          simp at he
      | unit | bool | nat | string | prod _ _ =>
        simp [consumeOneHO, hEq] at h
        cases h
        simp [GraphDelta.realizable, GraphDelta.empty]
    · simp [consumeOneHO, hEq] at h
  | _ =>
    simp [consumeOneHO] at h

/-! ## ConsumeHO Realizability over Traces -/

/-- If ConsumeHO succeeds and the session environment is well-formed,
    the resulting delta is realizable. -/
theorem ConsumeHO_realizable (from_ receiver : Role) (L : LocalType)
    (ts : List ValType) (env : SessionEnv)
    (hWF : ∀ T ∈ ts, match T with
      | .chan sid role => env.hasRole sid role ∧ env.hasRole sid receiver
      | _ => True)
    (L' : LocalType) (delta : GraphDelta)
    (h : ConsumeHO from_ receiver L ts = some (L', delta)) :
    delta.realizable env := by
  induction ts generalizing L L' delta with
  | nil =>
    -- Empty trace: delta is empty, trivially realizable
    simp only [ConsumeHO] at h
    cases h
    constructor <;> intro e he <;> simp [GraphDelta.empty] at he
  | cons t ts ih =>
    -- Decompose into one step + rest
    simp only [ConsumeHO] at h
    cases hOne : consumeOneHO from_ receiver t L with
    | none => simp [hOne] at h
    | some res =>
      simp only [hOne] at h
      cases hRest : ConsumeHO from_ receiver res.residual ts with
      | none => simp [hRest] at h
      | some p =>
        simp only [hRest] at h
        cases h
        -- Compose realizability of head delta and tail delta
        apply GraphDelta_realizable_compose
        · exact consumeOneHO_realizable from_ receiver t L env
            (hWF t (List.mem_cons_self)) res hOne
        · exact ih res.residual (fun T hT => hWF T (List.mem_cons_of_mem t hT))
            p.1 p.2 hRest

/-! ## Higher-Order Edge Coherence -/

/-- Higher-order coherence for a single directed edge.
    Like EdgeCoherent, but uses ConsumeHO and requires the resulting
    graph delta to be realizable w.r.t. the session environment.

    This captures safe delegation: consuming channel types produces
    valid edge additions that reference existing roles. -/
def EdgeCoherentHO (G : GEnv) (D : DEnv) (env : SessionEnv) (e : Edge) : Prop :=
  let senderEp := { sid := e.sid, role := e.sender : Endpoint }
  let receiverEp := { sid := e.sid, role := e.receiver : Endpoint }
  let trace := lookupD D e
  ∀ Lrecv,
    lookupG G receiverEp = some Lrecv →
    ∃ Lsender L' delta,
      lookupG G senderEp = some Lsender ∧
      ConsumeHO e.sender e.receiver Lrecv trace = some (L', delta) ∧
      delta.realizable env

/-- Full higher-order coherence: HO edge-coherent for all active edges. -/
def CoherentHO (G : GEnv) (D : DEnv) (env : SessionEnv) : Prop :=
  ∀ e, ActiveEdge G e → EdgeCoherentHO G D env e

/-! ## Conservative Extension: HO Collapses to FO -/

/-- When the trace has no channel types, EdgeCoherentHO implies EdgeCoherent.
    This is the "collapse" direction of the conservative extension. -/
theorem EdgeCoherentHO_implies_EdgeCoherent_no_channels
    (G : GEnv) (D : DEnv) (env : SessionEnv) (e : Edge)
    (hNoChans : hasNoChannels (lookupD D e) = true)
    (hHO : EdgeCoherentHO G D env e) :
    EdgeCoherent G D e := by
  intro Lrecv hGrecv
  -- Apply HO coherence to get the sender and consumption result
  obtain ⟨Lsender, L', delta, hGsender, hConsume, _⟩ := hHO Lrecv hGrecv
  refine ⟨Lsender, hGsender, ?_⟩
  -- ConsumeHO agrees with Consume when no channels
  have hConservative := ConsumeHO_conservative e.sender e.receiver Lrecv (lookupD D e) hNoChans
  -- Extract that Consume succeeds from HO success
  simp only [hConsume, Option.map] at hConservative
  rw [← hConservative]
  simp

/-- When the trace has no channel types, EdgeCoherent implies EdgeCoherentHO.
    This is the "lift" direction of the conservative extension. -/
theorem EdgeCoherent_implies_EdgeCoherentHO_no_channels
    (G : GEnv) (D : DEnv) (env : SessionEnv) (e : Edge)
    (hNoChans : hasNoChannels (lookupD D e) = true)
    (hFO : EdgeCoherent G D e) :
    EdgeCoherentHO G D env e := by
  intro Lrecv hGrecv
  -- Apply FO coherence to get the sender and consumption result
  obtain ⟨Lsender, hGsender, hConsume⟩ := hFO Lrecv hGrecv
  -- ConsumeHO agrees with Consume when no channels
  have hConservative := ConsumeHO_conservative e.sender e.receiver Lrecv (lookupD D e) hNoChans
  -- Extract L' from the successful Consume
  obtain ⟨L', hConsumeEq⟩ := Option.isSome_iff_exists.mp hConsume
  -- ConsumeHO must also succeed with the same L'
  have hHOSuccess : ∃ delta, ConsumeHO e.sender e.receiver Lrecv (lookupD D e) = some (L', delta) := by
    simp only [hConsumeEq, Option.map] at hConservative
    cases hHO : ConsumeHO e.sender e.receiver Lrecv (lookupD D e) with
    | none => simp [hHO] at hConservative
    | some p =>
      use p.2
      simp only [hHO] at hConservative
      simp only [Option.some.injEq] at hConservative
      -- Goal: some p = some (L', p.2)
      -- We have: hConservative : p.1 = L'
      have hPEq : p = (L', p.2) := Prod.ext hConservative rfl
      rw [hPEq]
  obtain ⟨delta, hConsumeHO⟩ := hHOSuccess
  -- The delta is empty (no channels), hence trivially realizable
  have hEmpty := ConsumeHO_no_channels_empty_delta e.sender e.receiver Lrecv
      (lookupD D e) hNoChans L' delta hConsumeHO
  refine ⟨Lsender, L', delta, hGsender, hConsumeHO, ?_⟩
  -- Empty delta is realizable
  simp [GraphDelta.isEmpty] at hEmpty
  obtain ⟨hAddedEmpty, hRemovedEmpty⟩ := hEmpty
  simp [GraphDelta.realizable] at hAddedEmpty hRemovedEmpty ⊢
  constructor
  · intro e' he'; rw [hAddedEmpty] at he'; cases he'
  · intro e' he'; rw [hRemovedEmpty] at he'; cases he'

/-- When no channels in trace, EdgeCoherentHO is equivalent to EdgeCoherent.
    This is the full conservative extension theorem for edge coherence. -/
theorem EdgeCoherentHO_iff_EdgeCoherent_no_channels
    (G : GEnv) (D : DEnv) (env : SessionEnv) (e : Edge)
    (hNoChans : hasNoChannels (lookupD D e) = true) :
    EdgeCoherentHO G D env e ↔ EdgeCoherent G D e :=
  ⟨EdgeCoherentHO_implies_EdgeCoherent_no_channels G D env e hNoChans,
   EdgeCoherent_implies_EdgeCoherentHO_no_channels G D env e hNoChans⟩

end
