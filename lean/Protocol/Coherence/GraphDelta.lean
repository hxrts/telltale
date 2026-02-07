import Protocol.Environments
import Protocol.Coherence.Consume
import Protocol.Coherence.EdgeCoherence

/-!
# Higher-Order Consume with Graph Deltas

This module defines a higher-order `Consume` function for multiparty session types
that handles channel delegation by producing graph deltas.

## The Problem

First-order `Consume` (in `Consume.lean`) only handles base types. When a channel
endpoint is delegated (passed as a message), the receiver gains communication edges
in the delegated session. We need a function that:

1. Tracks which edges are added/removed during consumption
2. Agrees with first-order `Consume` when no channels are involved
3. Produces realizable deltas given well-formed session environments

## Solution Structure

- `GraphDelta`: Records added/removed edges, forms a monoid under composition
- `consumeOneHO`: Single-step consume, produces delta when consuming channel types
- `ConsumeHO`: Full trace consume, composes deltas from each step
- `ConsumeHO_conservative`: Key theorem - HO agrees with FO on channel-free traces

## Reference

Ported from `work/aristotle/23_higher_order_consume.lean`.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! ## Graph Delta -/

/-- A graph delta records edges added and removed during consumption.
    For delegation, we typically only add edges (the delegatee gains edges). -/
structure GraphDelta where
  added : List Edge
  removed : List Edge
  deriving Repr

/-- Empty graph delta (no changes). -/
def GraphDelta.empty : GraphDelta := ⟨[], []⟩

/-- Compose two graph deltas by concatenating their edge lists. -/
def GraphDelta.compose (d1 d2 : GraphDelta) : GraphDelta :=
  ⟨d1.added ++ d2.added, d1.removed ++ d2.removed⟩

/-- Check if a graph delta represents no changes. -/
def GraphDelta.isEmpty (d : GraphDelta) : Bool :=
  d.added.isEmpty && d.removed.isEmpty

/-! ## Higher-Order Consume -/

/-- Result of consuming one message: residual type + graph delta. -/
structure ConsumeResult where
  residual : LocalType
  delta : GraphDelta
  deriving Repr

/-- Consume one message, potentially a channel.
    When consuming a channel (sid, role), the receiver gains edges
    for that role in that session. -/
def consumeOneHO (from_ : Role) (receiver : Role) (T : ValType) :
    LocalType → Option ConsumeResult
  | .recv r T' L =>
    if from_ == r && T == T' then
      match T with
      | .chan sid delegatedRole =>
        -- Channel type: receiver gains bidirectional edges with delegated role
        let newEdges := [
          Edge.mk sid delegatedRole receiver,
          Edge.mk sid receiver delegatedRole
        ]
        some ⟨L, ⟨newEdges, []⟩⟩
      | _ =>
        -- Non-channel type: no graph change
        some ⟨L, GraphDelta.empty⟩
    else none
  | _ => none

/-- Higher-order consume over a trace.
    Composes deltas from each step. -/
def ConsumeHO (from_ : Role) (receiver : Role) :
    LocalType → List ValType → Option (LocalType × GraphDelta)
  | L, [] => some (L, GraphDelta.empty)
  | L, T :: ts =>
    match consumeOneHO from_ receiver T L with
    | some ⟨L', delta1⟩ =>
      match ConsumeHO from_ receiver L' ts with
      | some (L'', delta2) => some (L'', delta1.compose delta2)
      | none => none
    | none => none

/-! ## Session Environments and Realizability -/

/-- A session environment maps sessions to their participating roles. -/
structure SessionEnv where
  sessions : List (SessionId × List Role)
  deriving Repr

/-- Check if a session exists in the environment. -/
def SessionEnv.hasSession (env : SessionEnv) (sid : SessionId) : Bool :=
  env.sessions.any (fun (s, _) => s == sid)

/-- Check if a role exists in a session. -/
def SessionEnv.hasRole (env : SessionEnv) (sid : SessionId) (r : Role) : Bool :=
  match env.sessions.find? (fun (s, _) => s == sid) with
  | some (_, roles) => roles.contains r
  | none => false

/-- A graph delta is realizable w.r.t. a session environment if all edges
    reference existing roles in existing sessions. -/
def GraphDelta.realizable (d : GraphDelta) (env : SessionEnv) : Prop :=
  (∀ e ∈ d.added, env.hasRole e.sid e.sender ∧ env.hasRole e.sid e.receiver) ∧
  (∀ e ∈ d.removed, env.hasRole e.sid e.sender ∧ env.hasRole e.sid e.receiver)

/-! ## Helper Predicates -/

/-- Check if a trace contains no channel types. -/
def hasNoChannels : List ValType → Bool
  | [] => true
  | .chan _ _ :: _ => false
  | _ :: ts => hasNoChannels ts

/-- Traces with no channels don't contain channel types. -/
theorem hasNoChannels_no_chan (ts : List ValType) (h : hasNoChannels ts = true) :
    ∀ T ∈ ts, ∀ sid r, T ≠ ValType.chan sid r := by
  -- Induction on the trace, using the definition of hasNoChannels
  induction ts with
  | nil => simp
  | cons t ts ih =>
    intro T hT sid r
    cases hT with
    | head =>
      -- T = t (head of list), must show t ≠ chan sid r
      cases t with
      | chan _ _ => simp [hasNoChannels] at h
      | _ => intro h'; cases h'
    | tail _ hMem =>
      -- T is in tail, apply IH after extracting hasNoChannels for tail
      have hTail : hasNoChannels ts = true := by
        cases t <;> simp [hasNoChannels] at h <;> exact h
      exact ih hTail T hMem sid r

/-! ## Graph Delta Algebraic Properties -/

/-- Graph delta composition is associative. -/
theorem GraphDelta_compose_assoc (d1 d2 d3 : GraphDelta) :
    (d1.compose d2).compose d3 = d1.compose (d2.compose d3) := by
  simp [GraphDelta.compose, List.append_assoc]

/-- Empty delta is left identity for composition. -/
theorem GraphDelta_compose_empty_left (d : GraphDelta) :
    GraphDelta.empty.compose d = d := by
  simp [GraphDelta.compose, GraphDelta.empty]

/-- Empty delta is right identity for composition. -/
theorem GraphDelta_compose_empty_right (d : GraphDelta) :
    d.compose GraphDelta.empty = d := by
  simp [GraphDelta.compose, GraphDelta.empty]

/-! ## Compositionality -/

/-- Compositionality: consuming a concatenated trace equals composing deltas.
    This is the key structural property for reasoning about multi-step consumption. -/
theorem ConsumeHO_append (from_ receiver : Role) (L : LocalType)
    (ts1 ts2 : List ValType) :
    ConsumeHO from_ receiver L (ts1 ++ ts2) =
      match ConsumeHO from_ receiver L ts1 with
      | some (L', delta1) =>
        match ConsumeHO from_ receiver L' ts2 with
        | some (L'', delta2) => some (L'', delta1.compose delta2)
        | none => none
      | none => none := by
  -- Induction on ts1, threading the local type through
  induction ts1 generalizing L with
  | nil =>
    -- Base case: empty ts1 means compose with empty delta
    simp only [ConsumeHO, List.nil_append, GraphDelta.compose]
    cases hTs2 : ConsumeHO from_ receiver L ts2 with
    | none => rfl
    | some p => simp [GraphDelta.empty]
  | cons t1 ts1 ih =>
    -- Step case: consume head, then apply IH
    simp only [List.cons_append, ConsumeHO]
    cases hOne : consumeOneHO from_ receiver t1 L with
    | none => rfl
    | some res =>
      simp only []
      -- Apply IH to the tail
      rw [ih]
      cases hTs1 : ConsumeHO from_ receiver res.residual ts1 with
      | none => simp
      | some p =>
        simp only []
        cases hTs2 : ConsumeHO from_ receiver p.1 ts2 with
        | none => rfl
        | some p' => simp [GraphDelta.compose, List.append_assoc]

/-! ## Conservative Extension -/

/-- Helper: consumeOneHO agrees with consumeOne when T is not a channel. -/
private theorem consumeOneHO_eq_consumeOne_non_channel
    (from_ receiver : Role) (T : ValType) (L : LocalType)
    (hNotChan : ∀ sid r, T ≠ ValType.chan sid r) :
    consumeOneHO from_ receiver T L =
      (consumeOne from_ T L).map (fun L' => ⟨L', GraphDelta.empty⟩) := by
  cases L with
  | recv r' T' L' =>
    simp only [consumeOneHO, consumeOne]
    by_cases hEq : from_ == r' && T == T'
    · simp only [hEq, ↓reduceIte]
      -- T is not a channel, so we get empty delta
      cases T with
      | chan sid role => exact absurd rfl (hNotChan sid role)
      | _ => rfl
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte]; rfl
  | _ => simp [consumeOneHO, consumeOne]

/-- Conservative extension: when trace has no channel types, HO agrees with FO.
    This ensures ConsumeHO is a proper generalization of Consume. -/
theorem ConsumeHO_conservative (from_ receiver : Role) (L : LocalType)
    (ts : List ValType) (hNoChans : hasNoChannels ts = true) :
    (ConsumeHO from_ receiver L ts).map Prod.fst = Consume from_ L ts := by
  induction ts generalizing L with
  | nil => simp [ConsumeHO, Consume]
  | cons t ts ih =>
    simp only [ConsumeHO, Consume]
    -- t is not a channel since hasNoChannels holds
    have hNotChan : ∀ sid r, t ≠ ValType.chan sid r :=
      hasNoChannels_no_chan (t :: ts) hNoChans t List.mem_cons_self
    rw [consumeOneHO_eq_consumeOne_non_channel from_ receiver t L hNotChan]
    -- Recurse with IH
    cases hOne : consumeOne from_ t L with
    | none => rfl
    | some L' =>
      simp only [Option.map]
      have hTsNoChans : hasNoChannels ts = true := by
        cases t <;> simp [hasNoChannels] at hNoChans ⊢ <;> exact hNoChans
      specialize ih L' hTsNoChans
      cases hRest : ConsumeHO from_ receiver L' ts with
      | none => simp [hRest] at ih ⊢; exact ih
      | some p => simp [hRest] at ih ⊢; exact ih

/-! ## Empty Delta Property -/

/-- Helper: consumeOneHO produces empty delta for non-channel types. -/
private theorem consumeOneHO_non_channel_empty_delta
    (from_ receiver : Role) (T : ValType) (L : LocalType) (res : ConsumeResult)
    (hNotChan : ∀ sid r, T ≠ ValType.chan sid r)
    (h : consumeOneHO from_ receiver T L = some res) :
    res.delta = GraphDelta.empty := by
  cases L with
  | recv r' T' L' =>
    simp only [consumeOneHO] at h
    by_cases hEq : from_ == r' && T == T'
    · simp only [hEq, ↓reduceIte] at h
      cases T with
      | chan sid role => exact absurd rfl (hNotChan sid role)
      | _ => simp only [Option.some.injEq] at h; rw [← h]
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h; cases h
  | _ => simp [consumeOneHO] at h

/-- When no channels in trace, the graph delta is empty. -/
theorem ConsumeHO_no_channels_empty_delta (from_ receiver : Role) (L : LocalType)
    (ts : List ValType) (hNoChans : hasNoChannels ts = true)
    (L' : LocalType) (delta : GraphDelta)
    (h : ConsumeHO from_ receiver L ts = some (L', delta)) :
    delta.isEmpty = true := by
  induction ts generalizing L delta with
  | nil =>
    simp only [ConsumeHO] at h
    cases h
    simp [GraphDelta.isEmpty, GraphDelta.empty]
  | cons t ts ih =>
    simp only [ConsumeHO] at h
    have hNotChan := hasNoChannels_no_chan (t :: ts) hNoChans t (List.mem_cons_self)
    have hTsNoChans : hasNoChannels ts = true := by
      cases t <;> simp [hasNoChannels] at hNoChans ⊢ <;> exact hNoChans
    -- Extract intermediate results
    cases hOne : consumeOneHO from_ receiver t L with
    | none => simp [hOne] at h
    | some res =>
      simp only [hOne] at h
      cases hRest : ConsumeHO from_ receiver res.residual ts with
      | none => simp [hRest] at h
      | some p =>
        simp only [hRest] at h
        cases h
        -- Both deltas are empty, so composition is empty
        have hDelta1 := consumeOneHO_non_channel_empty_delta from_ receiver t L res hNotChan hOne
        have hDelta2 := ih res.residual hTsNoChans p.2 hRest
        simp [GraphDelta.isEmpty, GraphDelta.compose, hDelta1, GraphDelta.empty] at hDelta2 ⊢
        exact hDelta2

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
  cases T with
  | chan sid role =>
    -- Channel case: delta has the two new edges
    cases L with
    | recv r' T' L' =>
      simp only [consumeOneHO] at h
      by_cases hEq : from_ == r' && ValType.chan sid role == T'
      · simp only [hEq, ↓reduceIte] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        -- The two edges reference (role, receiver) in session sid
        simp only [GraphDelta.realizable]
        constructor
        · intro e he
          simp only [List.mem_cons] at he
          cases he with
          | inl heq =>
            rw [heq]
            exact ⟨hT.1, hT.2⟩
          | inr heq =>
            cases heq with
            | inl heq2 =>
              rw [heq2]
              exact ⟨hT.2, hT.1⟩
            | inr hnil => cases hnil
        · intro e he; simp at he
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | _ => simp [consumeOneHO] at h
  | unit =>
    -- Non-channel case: delta is empty, trivially realizable
    cases L with
    | recv r' T' L' =>
      simp only [consumeOneHO] at h
      by_cases hEq : from_ == r' && ValType.unit == T'
      · simp only [hEq, ↓reduceIte] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        simp [GraphDelta.realizable, GraphDelta.empty]
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | _ => simp [consumeOneHO] at h
  | bool =>
    cases L with
    | recv r' T' L' =>
      simp only [consumeOneHO] at h
      by_cases hEq : from_ == r' && ValType.bool == T'
      · simp only [hEq, ↓reduceIte] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        simp [GraphDelta.realizable, GraphDelta.empty]
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | _ => simp [consumeOneHO] at h
  | nat =>
    cases L with
    | recv r' T' L' =>
      simp only [consumeOneHO] at h
      by_cases hEq : from_ == r' && ValType.nat == T'
      · simp only [hEq, ↓reduceIte] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        simp [GraphDelta.realizable, GraphDelta.empty]
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | _ => simp [consumeOneHO] at h
  | string =>
    cases L with
    | recv r' T' L' =>
      simp only [consumeOneHO] at h
      by_cases hEq : from_ == r' && ValType.string == T'
      · simp only [hEq, ↓reduceIte] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        simp [GraphDelta.realizable, GraphDelta.empty]
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | _ => simp [consumeOneHO] at h
  | prod t1 t2 =>
    cases L with
    | recv r' T' L' =>
      simp only [consumeOneHO] at h
      by_cases hEq : from_ == r' && ValType.prod t1 t2 == T'
      · simp only [hEq, ↓reduceIte] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        simp [GraphDelta.realizable, GraphDelta.empty]
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | _ => simp [consumeOneHO] at h

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
