import Protocol.Environments
import Protocol.Coherence.Consume
import Protocol.Coherence.EdgeCoherence

/-! # Protocol.Coherence.GraphDeltaCore

Core higher-order consume and graph-delta definitions used by coherence layers.
-/


/-! # Higher-Order Consume with Graph Deltas

This module defines a higher-order `Consume` function for multiparty session types
that handles channel delegation by producing graph deltas.

The Problem. First-order `Consume` (in `Consume.lean`) only handles base types.
When a channel endpoint is delegated (passed as a message), the receiver gains
communication edges in the delegated session. We need a function that:
1. Tracks which edges are added/removed during consumption
2. Agrees with first-order `Consume` when no channels are involved
3. Produces realizable deltas given well-formed session environments

Solution Structure. We define:
- `GraphDelta`: Records added/removed edges, forms a monoid under composition
- `consumeOneHO`: Single-step consume, produces delta when consuming channel types
- `ConsumeHO`: Full trace consume, composes deltas from each step
- conservative core lemmas (`ConsumeHO_conservative`, empty-delta/converse forms)

## Reference

Ported from `work/aristotle/23_higher_order_consume.lean`.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

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

/-- Converse (existence form): for channel-free traces, any successful FO consume
    lifts to an HO consume run with the same residual local type. -/
theorem ConsumeHO_conservative_converse_exists
    (from_ receiver : Role) (L : LocalType) (ts : List ValType)
    (hNoChans : hasNoChannels ts = true) {L' : LocalType}
    (hConsume : Consume from_ L ts = some L') :
    ∃ delta, ConsumeHO from_ receiver L ts = some (L', delta) := by
  induction ts generalizing L L' with
  | nil =>
    simp [Consume] at hConsume
    cases hConsume
    refine ⟨GraphDelta.empty, ?_⟩
    simp [ConsumeHO]
  | cons t ts ih =>
    simp [Consume] at hConsume
    cases hOne : consumeOne from_ t L with
    | none =>
      simp [hOne] at hConsume
    | some L1 =>
      simp [hOne] at hConsume
      have hNotChan : ∀ sid r, t ≠ ValType.chan sid r :=
        hasNoChannels_no_chan (t :: ts) hNoChans t List.mem_cons_self
      have hTsNoChans : hasNoChannels ts = true := by
        cases t <;> simp [hasNoChannels] at hNoChans ⊢ <;> exact hNoChans
      have hOneHO : consumeOneHO from_ receiver t L = some ⟨L1, GraphDelta.empty⟩ := by
        rw [consumeOneHO_eq_consumeOne_non_channel from_ receiver t L hNotChan, hOne]
        rfl
      rcases ih L1 hTsNoChans hConsume with ⟨deltaTail, hTail⟩
      refine ⟨GraphDelta.empty.compose deltaTail, ?_⟩
      simp [ConsumeHO, hOneHO, hTail, GraphDelta.compose]

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

/-- Converse (exactness form): for channel-free traces, FO success implies an HO run
    with identical residual local type and an empty graph delta. -/
theorem ConsumeHO_conservative_converse
    (from_ receiver : Role) (L : LocalType) (ts : List ValType)
    (hNoChans : hasNoChannels ts = true) {L' : LocalType}
    (hConsume : Consume from_ L ts = some L') :
    ∃ delta,
      ConsumeHO from_ receiver L ts = some (L', delta) ∧
      delta.isEmpty = true := by
  rcases ConsumeHO_conservative_converse_exists from_ receiver L ts hNoChans hConsume with
    ⟨delta, hHO⟩
  refine ⟨delta, hHO, ?_⟩
  exact ConsumeHO_no_channels_empty_delta from_ receiver L ts hNoChans L' delta hHO


end
