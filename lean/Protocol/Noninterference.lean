import Protocol.Semantics
import Protocol.Coherence

/-
The Problem. Prove that non-participants in a communication cannot observe
internal choices. If role r is blind to a step (neither sender nor receiver),
then r's observable state is unchanged.

The difficulty is formalizing "observable state" in a way that:
1. Is precise enough to state the theorem
2. Is general enough to cover all step types
3. Connects to Coherence (the main invariant)

Solution Structure.
1. Define CEquiv: configuration equivalence from a role's perspective
2. Define BlindTo: when a role doesn't participate in a communication
3. Prove step locality: steps only modify participant state
4. Prove blind_step_preserves_CEquiv: the main noninterference theorem
5. Lift to traces: blind roles see deterministic traces
-/

/-!
# Noninterference for MPST

Proves that non-participants in a communication cannot observe which branch
was selected. Ported from Aristotle file 01 (185 lines, 0 sorry).

## Expose

- `CEquiv` : configuration equivalence for a role
- `BlindTo` : role is neither sender nor receiver
- `blind_step_preserves_CEquiv` : the main noninterference theorem
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Configuration Equivalence -/

/-- Two configurations are equivalent with respect to role r in session s
    if they have the same observable state for r. Observable state includes:
    - Local type at r's endpoint
    - Incoming buffers (messages sent to r)
    - Incoming traces (types of messages sent to r) -/
def CEquiv (C₁ C₂ : Config) (s : SessionId) (r : Role) : Prop :=
  let e : Endpoint := ⟨s, r⟩
  -- Same local type at r's endpoint
  lookupG C₁.G e = lookupG C₂.G e ∧
  -- Same incoming buffers (from any sender to r)
  (∀ sender, lookupBuf C₁.bufs ⟨s, sender, r⟩ = lookupBuf C₂.bufs ⟨s, sender, r⟩) ∧
  -- Same incoming traces (from any sender to r)
  (∀ sender, lookupD C₁.D ⟨s, sender, r⟩ = lookupD C₂.D ⟨s, sender, r⟩)

notation:50 C₁ " ≈[" s ", " r "] " C₂ => CEquiv C₁ C₂ s r

/-! ## CEquiv Properties -/

/-- CEquiv is reflexive: every config is equivalent to itself. -/
theorem CEquiv.refl (C : Config) (s : SessionId) (r : Role) : C ≈[s, r] C := by
  -- All three components are trivially equal.
  exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- CEquiv is symmetric: equivalence is bidirectional. -/
theorem CEquiv.symm {C₁ C₂ : Config} {s : SessionId} {r : Role}
    (h : C₁ ≈[s, r] C₂) : C₂ ≈[s, r] C₁ := by
  -- Flip each equality.
  obtain ⟨hG, hBufs, hD⟩ := h
  exact ⟨hG.symm, fun p => (hBufs p).symm, fun p => (hD p).symm⟩

/-- CEquiv is transitive: chain through intermediate config. -/
theorem CEquiv.trans {C₁ C₂ C₃ : Config} {s : SessionId} {r : Role}
    (h₁₂ : C₁ ≈[s, r] C₂) (h₂₃ : C₂ ≈[s, r] C₃) : C₁ ≈[s, r] C₃ := by
  -- Compose equalities component-wise.
  obtain ⟨hG₁₂, hBufs₁₂, hD₁₂⟩ := h₁₂
  obtain ⟨hG₂₃, hBufs₂₃, hD₂₃⟩ := h₂₃
  exact ⟨hG₁₂.trans hG₂₃,
         fun p => (hBufs₁₂ p).trans (hBufs₂₃ p),
         fun p => (hD₁₂ p).trans (hD₂₃ p)⟩

/-! ## Blindness -/

/-- A role is blind to a communication if it is neither sender nor receiver. -/
def BlindTo (r : Role) (sender receiver : Role) : Prop :=
  r ≠ sender ∧ r ≠ receiver

/-- BlindTo is symmetric in sender/receiver for our purposes. -/
theorem BlindTo.comm {r sender receiver : Role}
    (h : BlindTo r sender receiver) : BlindTo r receiver sender := by
  exact ⟨h.2, h.1⟩

/-! ## Step Locality: G Environment -/

/-- Send step only changes G at the sender's endpoint.
    Other endpoints are unaffected. -/
theorem send_G_locality {C : Config} {ep : Endpoint} {target : Role}
    {v : Value} {T : ValType} {L : LocalType}
    (ep' : Endpoint) (hne : ep' ≠ ep) :
    lookupG (sendStep C ep ⟨ep.sid, ep.role, target⟩ v T L).G ep' = lookupG C.G ep' := by
  simp only [sendStep]
  exact lookupG_updateG_ne hne

/-- Recv step only changes G at the receiver's endpoint. -/
theorem recv_G_locality {C : Config} {ep : Endpoint} {edge : Edge}
    {x : Var} {v : Value} {L : LocalType}
    (ep' : Endpoint) (hne : ep' ≠ ep) :
    lookupG (recvStep C ep edge x v L).G ep' = lookupG C.G ep' := by
  simp only [recvStep]
  cases hdq : dequeueBuf C.bufs edge with
  | none => rfl
  | some p => simp only [hdq]; exact lookupG_updateG_ne hne

/-! ## Step Locality: Buffers -/

/-- Send step only adds to the sender→receiver buffer.
    Other buffers are unaffected. -/
theorem send_buf_locality {C : Config} {ep : Endpoint} {target : Role}
    {v : Value} {T : ValType} {L : LocalType}
    (edge : Edge) (hne : edge ≠ ⟨ep.sid, ep.role, target⟩) :
    lookupBuf (sendStep C ep ⟨ep.sid, ep.role, target⟩ v T L).bufs edge =
    lookupBuf C.bufs edge := by
  simp only [sendStep]
  exact lookupBuf_enqueueBuf_ne hne

/-- Recv step only dequeues from the source→receiver buffer. -/
theorem recv_buf_locality {C : Config} {ep : Endpoint} {edge edge' : Edge}
    {x : Var} {v : Value} {L : LocalType}
    (hne : edge' ≠ edge) :
    lookupBuf (recvStep C ep edge x v L).bufs edge' = lookupBuf C.bufs edge' := by
  simp only [recvStep]
  cases hdq : dequeueBuf C.bufs edge with
  | none => rfl
  | some p => simp only [hdq]; exact lookupBuf_dequeueBuf_ne hdq hne

/-! ## Step Locality: Traces -/

/-- Send step only extends the sender→receiver trace.
    Other traces are unaffected. -/
theorem send_D_locality {C : Config} {ep : Endpoint} {target : Role}
    {v : Value} {T : ValType} {L : LocalType}
    (edge : Edge) (hne : edge ≠ ⟨ep.sid, ep.role, target⟩) :
    lookupD (sendStep C ep ⟨ep.sid, ep.role, target⟩ v T L).D edge =
    lookupD C.D edge := by
  simp only [sendStep]
  exact lookupD_update_neq C.D ⟨ep.sid, ep.role, target⟩ edge (lookupD C.D _ ++ [T]) hne.symm

/-- Recv step only shortens the source→receiver trace. -/
theorem recv_D_locality {C : Config} {ep : Endpoint} {edge edge' : Edge}
    {x : Var} {v : Value} {L : LocalType}
    (hne : edge' ≠ edge) :
    lookupD (recvStep C ep edge x v L).D edge' = lookupD C.D edge' := by
  simp only [recvStep]
  cases hdq : dequeueBuf C.bufs edge with
  | none => rfl
  | some p =>
    simp only [hdq]
    exact lookupD_update_neq C.D edge edge' (lookupD C.D edge).tail hne.symm

/-! ## Noninterference Theorem -/

/-- Helper: blind role's G is unchanged by send step. -/
private theorem send_blind_G_unchanged {C : Config} {ep : Endpoint} {target : Role}
    {v : Value} {T : ValType} {L : LocalType}
    {s : SessionId} {r : Role} (hBlind : BlindTo r ep.role target)
    (_hSid : ep.sid = s) :
    lookupG (sendStep C ep ⟨ep.sid, ep.role, target⟩ v T L).G ⟨s, r⟩ =
    lookupG C.G ⟨s, r⟩ := by
  -- r ≠ sender, so r's endpoint is different from ep.
  apply send_G_locality
  -- Show ⟨s, r⟩ ≠ ep.
  intro heq
  -- heq : ⟨s, r⟩ = ep, extract that r = ep.role.
  have hr : r = ep.role := congrArg Endpoint.role heq
  exact hBlind.1 hr

/-- Helper: blind role's incoming buffers unchanged by send step. -/
private theorem send_blind_bufs_unchanged {C : Config} {ep : Endpoint} {target : Role}
    {v : Value} {T : ValType} {L : LocalType}
    {s : SessionId} {r : Role} (hBlind : BlindTo r ep.role target)
    (hSid : ep.sid = s) (sender : Role) :
    lookupBuf (sendStep C ep ⟨ep.sid, ep.role, target⟩ v T L).bufs ⟨s, sender, r⟩ =
    lookupBuf C.bufs ⟨s, sender, r⟩ := by
  -- Send enqueues at (ep.sid, ep.role, target).
  -- r ≠ target, so (s, sender, r) ≠ (ep.sid, ep.role, target).
  apply send_buf_locality
  intro heq
  subst hSid
  simp only [Edge.mk.injEq] at heq
  exact hBlind.2 heq.2.2

/-- Helper: blind role's incoming traces unchanged by send step. -/
private theorem send_blind_D_unchanged {C : Config} {ep : Endpoint} {target : Role}
    {v : Value} {T : ValType} {L : LocalType}
    {s : SessionId} {r : Role} (hBlind : BlindTo r ep.role target)
    (hSid : ep.sid = s) (sender : Role) :
    lookupD (sendStep C ep ⟨ep.sid, ep.role, target⟩ v T L).D ⟨s, sender, r⟩ =
    lookupD C.D ⟨s, sender, r⟩ := by
  apply send_D_locality
  intro heq
  subst hSid
  simp only [Edge.mk.injEq] at heq
  exact hBlind.2 heq.2.2

/-- A role is blind to a send step if it's neither the sender nor the target. -/
def BlindToSend (r : Role) (sender target : Role) : Prop :=
  r ≠ sender ∧ r ≠ target

/-- A role is blind to a recv step if it's neither the source nor the receiver. -/
def BlindToRecv (r : Role) (source receiver : Role) : Prop :=
  r ≠ source ∧ r ≠ receiver

/-- Send step preserves CEquiv for blind roles.
    The observable state of a role r is unchanged if r is neither sender nor target. -/
theorem send_preserves_CEquiv {C : Config} {ep : Endpoint} {target : Role}
    {v : Value} {T : ValType} {L : LocalType}
    {s : SessionId} {r : Role}
    (hSid : ep.sid = s)
    (hBlind : BlindToSend r ep.role target) :
    C ≈[s, r] (sendStep C ep ⟨ep.sid, ep.role, target⟩ v T L) := by
  unfold CEquiv
  constructor
  · -- G at r's endpoint unchanged
    apply Eq.symm
    apply send_G_locality
    intro heq
    have hr : r = ep.role := congrArg Endpoint.role heq
    exact hBlind.1 hr
  constructor
  · -- Buffers to r unchanged
    intro sender'
    apply Eq.symm
    apply send_buf_locality
    intro heq
    simp only [Edge.mk.injEq] at heq
    subst hSid
    exact hBlind.2 heq.2.2
  · -- Traces to r unchanged
    intro sender'
    apply Eq.symm
    apply send_D_locality
    intro heq
    simp only [Edge.mk.injEq] at heq
    subst hSid
    exact hBlind.2 heq.2.2

/-- Recv step preserves CEquiv for blind roles. -/
theorem recv_preserves_CEquiv {C : Config} {ep : Endpoint} {source : Role}
    {x : Var} {v : Value} {L : LocalType}
    {s : SessionId} {r : Role}
    (hSid : ep.sid = s)
    (hBlind : BlindToRecv r source ep.role) :
    C ≈[s, r] (recvStep C ep ⟨ep.sid, source, ep.role⟩ x v L) := by
  unfold CEquiv
  constructor
  · -- G unchanged
    apply Eq.symm
    apply recv_G_locality
    intro heq
    have hr : r = ep.role := congrArg Endpoint.role heq
    exact hBlind.2 hr
  constructor
  · -- Buffers unchanged
    intro sender'
    apply Eq.symm
    apply recv_buf_locality
    intro heq
    simp only [Edge.mk.injEq] at heq
    exact hBlind.2 heq.2.2
  · -- Traces unchanged
    intro sender'
    apply Eq.symm
    apply recv_D_locality
    intro heq
    simp only [Edge.mk.injEq] at heq
    exact hBlind.2 heq.2.2

/-- Main noninterference theorem: blind steps preserve observable equivalence.

    If role r is blind to a step (not sender/source or receiver/target),
    then r's observable state is unchanged.

    **Proof strategy**: Case analysis on StepBase. For each communication step,
    use the corresponding locality lemmas. Control-flow steps (seq, par, assign)
    don't affect G, bufs, or D. -/
theorem blind_step_preserves_CEquiv_single {C C' : Config}
    {s : SessionId} {r : Role}
    (hStep : StepBase C C')
    (hBlindSend : ∀ ep target T L, lookupG C.G ep = some (.send target T L) →
                  ep.sid = s → BlindToSend r ep.role target)
    (hBlindSelect : ∀ ep target branches, lookupG C.G ep = some (.select target branches) →
                    ep.sid = s → BlindToSend r ep.role target)
    (hBlindRecv : ∀ ep source T L, lookupG C.G ep = some (.recv source T L) →
                  ep.sid = s → BlindToRecv r source ep.role)
    (hBlindBranch : ∀ ep source branches, lookupG C.G ep = some (.branch source branches) →
                    ep.sid = s → BlindToRecv r source ep.role) :
    C ≈[s, r] C' := by
  cases hStep with
  | @send _ k x e v target T L hProc hk hx hG =>
    -- Send step: blind if r ≠ sender and r ≠ target
    by_cases hsid : e.sid = s
    · exact send_preserves_CEquiv hsid (hBlindSend e target T L hG hsid)
    · -- Different session, trivially unchanged
      unfold CEquiv
      constructor
      · apply Eq.symm; apply send_G_locality; intro heq
        have : e.sid = s := congrArg Endpoint.sid heq.symm
        exact hsid this
      constructor <;> intro sender'
      · apply Eq.symm; apply send_buf_locality; intro heq
        simp only [Edge.mk.injEq] at heq; exact hsid heq.1.symm
      · apply Eq.symm; apply send_D_locality; intro heq
        simp only [Edge.mk.injEq] at heq; exact hsid heq.1.symm
  | @recv _ k x e v source T L hProc hk hG hBuf =>
    -- Recv step: blind if r ≠ source and r ≠ receiver
    by_cases hsid : e.sid = s
    · exact recv_preserves_CEquiv hsid (hBlindRecv e source T L hG hsid)
    · unfold CEquiv
      constructor
      · apply Eq.symm; apply recv_G_locality; intro heq
        have : e.sid = s := congrArg Endpoint.sid heq.symm
        exact hsid this
      constructor <;> intro sender'
      · apply Eq.symm; apply recv_buf_locality; intro heq
        simp only [Edge.mk.injEq] at heq; exact hsid heq.1.symm
      · apply Eq.symm; apply recv_D_locality; intro heq
        simp only [Edge.mk.injEq] at heq; exact hsid heq.1.symm
  | @select _ k e ℓ target branches L hProc hk hG hFind =>
    -- Select uses sendStep, so same as send
    by_cases hsid : e.sid = s
    · exact send_preserves_CEquiv hsid (hBlindSelect e target branches hG hsid)
    · unfold CEquiv
      constructor
      · apply Eq.symm; apply send_G_locality; intro heq
        have : e.sid = s := congrArg Endpoint.sid heq.symm
        exact hsid this
      constructor <;> intro sender'
      · apply Eq.symm; apply send_buf_locality; intro heq
        simp only [Edge.mk.injEq] at heq; exact hsid heq.1.symm
      · apply Eq.symm; apply send_D_locality; intro heq
        simp only [Edge.mk.injEq] at heq; exact hsid heq.1.symm
  | @branch _ k e ℓ source procBranches typeBranches P L bufs' hProc hk hG hBuf hPFind hTFind hDq =>
    -- Branch modifies G, bufs, D directly
    by_cases hsid : e.sid = s
    · have hb := hBlindBranch e source typeBranches hG hsid
      unfold CEquiv
      constructor
      · -- G at r unchanged (r ≠ receiver)
        apply lookupG_updateG_ne
        intro heq
        have hr : r = e.role := congrArg Endpoint.role heq
        exact hb.2 hr
      constructor
      · -- Buffers to r unchanged (dequeueBuf only affects specific edge)
        intro sender'
        simp only [hDq]
        apply lookupBuf_dequeueBuf_ne hDq
        intro heq
        simp only [Edge.mk.injEq] at heq
        exact hb.2 heq.2.2
      · -- Traces to r unchanged
        intro sender'
        apply lookupD_update_neq
        intro heq
        simp only [Edge.mk.injEq] at heq
        exact hb.2 heq.2.2
    · -- Different session
      unfold CEquiv
      constructor
      · apply lookupG_updateG_ne; intro heq
        have : e.sid = s := congrArg Endpoint.sid heq.symm
        exact hsid this
      constructor
      · intro sender'; simp only [hDq]
        apply lookupBuf_dequeueBuf_ne hDq; intro heq
        simp only [Edge.mk.injEq] at heq; exact hsid heq.1.symm
      · intro sender'; apply lookupD_update_neq; intro heq
        simp only [Edge.mk.injEq] at heq; exact hsid heq.1.symm
  | newSession hProc =>
    -- newSession adds new session with fresh ID, doesn't affect session s
    exact CEquiv.refl _ s r
  | assign hProc =>
    -- assign only modifies store, not G/bufs/D
    exact CEquiv.refl _ s r
  | seq2 hProc =>
    -- seq2 only modifies proc
    exact CEquiv.refl _ s r
  | par_skip_left hProc =>
    -- par_skip_left only modifies proc
    exact CEquiv.refl _ s r
  | par_skip_right hProc =>
    -- par_skip_right only modifies proc
    exact CEquiv.refl _ s r

/-! ## Coherence Connection -/

/-- CEquiv for all roles implies equal lookups.
    This connects noninterference to the Coherence invariant.

    Note: For list-backed GEnv/DEnv, equal lookups don't imply list equality,
    but they do imply observational equivalence which suffices for Coherence. -/
theorem CEquiv_all_implies_lookup_eq {C₁ C₂ : Config}
    (hEquiv : ∀ s r, C₁ ≈[s, r] C₂) :
    (∀ ep, lookupG C₁.G ep = lookupG C₂.G ep) ∧
    (∀ e, lookupD C₁.D e = lookupD C₂.D e) := by
  constructor
  · -- G lookup equality: for any endpoint ep.
    intro ep
    have h := hEquiv ep.sid ep.role
    exact h.1
  · -- D lookup equality: for any edge e.
    intro e
    have h := hEquiv e.sid e.receiver
    exact h.2.2 e.sender

end

/-!
## Summary

This module establishes noninterference for MPST:

1. **CEquiv**: Configuration equivalence for a role (same local type,
   incoming buffers, incoming traces)
2. **BlindTo**: When a role is neither sender nor receiver
3. **Step locality**: Steps only affect participant state
4. **blind_step_preserves_CEquiv**: The core noninterference theorem

The proofs rely on the per-edge structure of MPST: since each edge is
independent, steps on one edge cannot affect observations on unrelated edges.

**Status**: Theorem statements complete. Locality lemma proofs require
`updateG_ne`, `enqueueBuf_ne`, `updateD_ne` helper lemmas.
-/
