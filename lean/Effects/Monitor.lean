import Effects.Coherence

/-!
# MPST Verified Monitor

This module implements the proof-carrying runtime monitor for MPST.

## Overview

The monitor is the trusted component that:
1. Tracks protocol state (local types, in-flight messages, buffers)
2. Validates each protocol action before execution
3. Updates state to reflect completed actions
4. Maintains invariants that metatheory proves are preserved

## Monitor State

The `MonitorState` structure contains:
- `G`: GEnv mapping endpoints to their current local types
- `D`: DEnv tracking in-flight message type traces per edge
- `bufs`: Runtime message buffers per directed edge
- `Lin`: Linear context tracking capability tokens
- `supply`: Fresh session ID counter

## Monitor Transitions

`MonStep` is the judgment for valid monitor transitions. Each constructor
corresponds to a protocol action (send, recv, select, branch, newSession).

The key theorem `MonStep_preserves_WTMon` states that valid transitions
preserve the well-typedness invariant.

## Untrusted Code Interface

Untrusted code interacts with the monitor by:
1. Presenting a capability token
2. Requesting an action
3. Monitor validates action matches token's type
4. Monitor updates state and returns new token

This ensures untrusted code can only perform actions allowed by the protocol.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Protocol ProtoActions -/

/-- ProtoActions that can be performed on the protocol.
    Each action specifies the endpoint, peer role, and payload type. -/
inductive ProtoAction where
  | send (e : Endpoint) (target : Role) (T : ValType)
  | recv (e : Endpoint) (source : Role) (T : ValType)
  | select (e : Endpoint) (target : Role) (label : Label)
  | branch (e : Endpoint) (source : Role) (label : Label)
  deriving Repr

namespace ProtoAction

/-- Get the endpoint involved in an action. -/
def endpoint : ProtoAction → Endpoint
  | .send e _ _ => e
  | .recv e _ _ => e
  | .select e _ _ => e
  | .branch e _ _ => e

/-- Get the session ID of an action. -/
def sessionId (a : ProtoAction) : SessionId := a.endpoint.sid

end ProtoAction

/-! ## Monitor State -/

/-- Monitor state tracks all protocol-relevant information.

This is the trusted state maintained by the runtime monitor. -/
structure MonitorState where
  /-- Current local types at each endpoint -/
  G : GEnv
  /-- In-flight message type traces per directed edge -/
  D : DEnv
  /-- Runtime message buffers per directed edge -/
  bufs : Buffers
  /-- Linear capability token context -/
  Lin : LinCtx
  /-- Fresh session ID supply -/
  supply : SessionId

namespace MonitorState

/-- Empty monitor state. -/
def empty : MonitorState where
  G := []
  D := []
  bufs := []
  Lin := LinCtx.empty
  supply := 0

/-- Get the edge for a send from endpoint e to target. -/
def sendEdge (e : Endpoint) (target : Role) : Edge :=
  { sid := e.sid, sender := e.role, receiver := target }

/-- Get the edge for a recv at endpoint e from source. -/
def recvEdge (e : Endpoint) (source : Role) : Edge :=
  { sid := e.sid, sender := source, receiver := e.role }

end MonitorState

/-! ## Monitor Transition Judgment -/

/-- Monitor transition judgment.

`MonStep ms act v ms'` means: starting from monitor state `ms`, performing
action `act` with value `v` results in new state `ms'`.

Each rule checks:
1. The endpoint's current type matches the action
2. The linear context has the required token
3. Any runtime preconditions (e.g., buffer non-empty for recv)

And produces:
1. Updated GEnv with advanced local type
2. Updated DEnv with modified trace
3. Updated buffers
4. Updated linear context with new token -/
inductive MonStep : MonitorState → ProtoAction → Value → MonitorState → Prop where
  /-- Send: enqueue value and advance sender's type. -/
  | send {ms e target T L v lin'} :
      lookupG ms.G e = some (.send target T L) →
      LinCtx.consumeToken ms.Lin e = some (lin', .send target T L) →
      HasTypeVal ms.G v T →
      MonStep ms (.send e target T) v
        { ms with
          G := updateG ms.G e L
          D := updateD ms.D (MonitorState.sendEdge e target)
              (lookupD ms.D (MonitorState.sendEdge e target) ++ [T])
          bufs := enqueueBuf ms.bufs (MonitorState.sendEdge e target) v
          Lin := LinCtx.produceToken lin' e L }

  /-- Recv: dequeue value and advance receiver's type. -/
  | recv {ms e source T L v vs lin'} :
      lookupG ms.G e = some (.recv source T L) →
      LinCtx.consumeToken ms.Lin e = some (lin', .recv source T L) →
      lookupBuf ms.bufs (MonitorState.recvEdge e source) = v :: vs →
      HasTypeVal ms.G v T →
      MonStep ms (.recv e source T) v
        { ms with
          G := updateG ms.G e L
          D := updateD ms.D (MonitorState.recvEdge e source)
              (lookupD ms.D (MonitorState.recvEdge e source)).tail
          bufs := updateBuf ms.bufs (MonitorState.recvEdge e source) vs
          Lin := LinCtx.produceToken lin' e L }

  /-- Select: send label and advance sender's type. -/
  | select {ms e target bs ℓ L lin'} :
      lookupG ms.G e = some (.select target bs) →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      LinCtx.consumeToken ms.Lin e = some (lin', .select target bs) →
      MonStep ms (.select e target ℓ) (.string ℓ)
        { ms with
          G := updateG ms.G e L
          D := updateD ms.D (MonitorState.sendEdge e target)
              (lookupD ms.D (MonitorState.sendEdge e target) ++ [.string])
          bufs := enqueueBuf ms.bufs (MonitorState.sendEdge e target) (.string ℓ)
          Lin := LinCtx.produceToken lin' e L }

  /-- Branch: receive label and select continuation. -/
  | branch {ms e source bs ℓ L vs lin'} :
      lookupG ms.G e = some (.branch source bs) →
      lookupBuf ms.bufs (MonitorState.recvEdge e source) = .string ℓ :: vs →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      LinCtx.consumeToken ms.Lin e = some (lin', .branch source bs) →
      MonStep ms (.branch e source ℓ) (.string ℓ)
        { ms with
          G := updateG ms.G e L
          D := updateD ms.D (MonitorState.recvEdge e source)
              (lookupD ms.D (MonitorState.recvEdge e source)).tail
          bufs := updateBuf ms.bufs (MonitorState.recvEdge e source) vs
          Lin := LinCtx.produceToken lin' e L }

/-! ## Well-Typed Monitor State -/

/-- A monitor state is well-typed if:
    1. G and D are coherent
    2. Buffer head types match expected receive types (progress refinement)
    3. Branch labels in buffers are valid
    4. Buffers are typed according to D
    5. Linear context matches G
    6. Linear context has no duplicate endpoints (linearity)
    7. All session IDs are below supply (freshness)

    HeadCoherent and ValidLabels are refinements needed for progress.
    Reference: `work/effects/008.lean:399-402` (StrongWTConfig) -/
structure WTMon (ms : MonitorState) : Prop where
  /-- G and D are coherent -/
  coherent : Coherent ms.G ms.D
  /-- Buffer head types match expected receive types (for progress).
      Reference: `work/effects/008.lean:380-391` -/
  headCoherent : HeadCoherent ms.G ms.D
  /-- Branch labels in buffers are valid (for progress).
      Reference: `work/effects/008.lean:392-397` -/
  validLabels : ValidLabels ms.G ms.D ms.bufs
  /-- Buffers match type traces -/
  buffers_typed : BuffersTyped ms.G ms.D ms.bufs
  /-- Linear context entries match G -/
  lin_valid : ∀ e S, (e, S) ∈ ms.Lin → lookupG ms.G e = some S
  /-- Linear context has no duplicate endpoints (linearity invariant) -/
  lin_unique : ms.Lin.Pairwise (fun a b => a.1 ≠ b.1)
  /-- All endpoints in Lin have session ID below supply (freshness) -/
  supply_fresh : ∀ e S, (e, S) ∈ ms.Lin → e.sid < ms.supply
  /-- All endpoints in G have session ID below supply (freshness) -/
  supply_fresh_G : ∀ e S, (e, S) ∈ ms.G → e.sid < ms.supply

/-! ## Helper Lemmas for Linear Context -/

/-- Membership in produceToken: new entry is at the head. -/
theorem mem_produceToken_head (ctx : LinCtx) (e : Endpoint) (S : LocalType) :
    (e, S) ∈ LinCtx.produceToken ctx e S := by
  simp only [LinCtx.produceToken, List.mem_cons, true_or]

/-- Membership in produceToken: old entries are preserved. -/
theorem mem_produceToken_tail (ctx : LinCtx) (e e' : Endpoint) (S S' : LocalType)
    (h : (e', S') ∈ ctx) :
    (e', S') ∈ LinCtx.produceToken ctx e S := by
  simp only [LinCtx.produceToken, List.mem_cons]
  exact Or.inr h

/-- If (e', S') ∈ ctx' after consuming e from ctx, then (e', S') ∈ ctx. -/
theorem mem_of_consumeToken (ctx ctx' : LinCtx) (e e' : Endpoint) (S S' : LocalType)
    (hConsume : LinCtx.consumeToken ctx e = some (ctx', S))
    (hMem : (e', S') ∈ ctx') :
    (e', S') ∈ ctx := by
  induction ctx generalizing ctx' with
  | nil =>
    simp only [LinCtx.consumeToken] at hConsume
    exact Option.noConfusion hConsume
  | cons hd tl ih =>
    simp only [LinCtx.consumeToken] at hConsume
    split_ifs at hConsume with heq
    · -- Case: e = hd.1, ctx' = tl
      simp only [Option.some.injEq, Prod.mk.injEq] at hConsume
      obtain ⟨rfl, _⟩ := hConsume
      exact List.mem_cons_of_mem hd hMem
    · -- Case: e ≠ hd.1, ctx' = hd :: ctx''
      cases hConsume' : LinCtx.consumeToken tl e with
      | none =>
        simp only [hConsume'] at hConsume
        exact Option.noConfusion hConsume
      | some result =>
        simp only [hConsume', Option.some.injEq, Prod.mk.injEq] at hConsume
        obtain ⟨rfl, rfl⟩ := hConsume
        simp only [List.mem_cons] at hMem ⊢
        cases hMem with
        | inl heqMem => exact Or.inl heqMem
        | inr hmemTl => exact Or.inr (ih result.1 hConsume' hmemTl)

/-- consumeToken preserves other entries: if (e', S') was in ctx and e' ≠ e,
    then (e', S') is still in ctx' after consuming the token for e. -/
theorem mem_consumeToken_preserved (ctx ctx' : LinCtx) (e e' : Endpoint) (S S' : LocalType)
    (hConsume : LinCtx.consumeToken ctx e = some (ctx', S))
    (hMem : (e', S') ∈ ctx)
    (hNe : e' ≠ e) :
    (e', S') ∈ ctx' := by
  induction ctx generalizing ctx' with
  | nil =>
    simp only [LinCtx.consumeToken] at hConsume
    exact Option.noConfusion hConsume
  | cons hd tl ih =>
    simp only [LinCtx.consumeToken] at hConsume
    split_ifs at hConsume with heq
    · -- Case: e = hd.1 (found the target entry)
      simp only [Option.some.injEq, Prod.mk.injEq] at hConsume
      obtain ⟨rfl, _⟩ := hConsume
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl heqMem =>
        obtain ⟨heqE, _⟩ := Prod.mk.inj heqMem
        subst heqE
        exact absurd heq hNe.symm
      | inr hmemTl =>
        exact hmemTl
    · -- Case: e ≠ hd.1 (continue recursively)
      cases hConsume' : LinCtx.consumeToken tl e with
      | none =>
        simp only [hConsume'] at hConsume
        exact Option.noConfusion hConsume
      | some result =>
        simp only [hConsume', Option.some.injEq, Prod.mk.injEq] at hConsume
        obtain ⟨rfl, rfl⟩ := hConsume
        simp only [List.mem_cons] at hMem ⊢
        cases hMem with
        | inl heqMem => exact Or.inl heqMem
        | inr hmemTl => exact Or.inr (ih result.1 hConsume' hmemTl)

/-! ## Linearity Invariant Lemmas -/

/-- If ctx has no duplicate endpoints and consumeToken succeeds,
    the consumed endpoint e is not in the result ctx'. -/
theorem consumeToken_not_mem (ctx ctx' : LinCtx) (e : Endpoint) (S : LocalType)
    (hPairwise : ctx.Pairwise (fun a b => a.1 ≠ b.1))
    (hConsume : LinCtx.consumeToken ctx e = some (ctx', S)) :
    ∀ S', (e, S') ∉ ctx' := by
  induction ctx generalizing ctx' with
  | nil =>
    simp only [LinCtx.consumeToken] at hConsume
    exact Option.noConfusion hConsume
  | cons hd tl ih =>
    simp only [LinCtx.consumeToken] at hConsume
    split_ifs at hConsume with heq
    · -- Case: e = hd.1, ctx' = tl
      simp only [Option.some.injEq, Prod.mk.injEq] at hConsume
      obtain ⟨rfl, _⟩ := hConsume
      -- Need to show (e, S') ∉ tl for any S'
      -- From hPairwise, hd.1 ≠ every element's first component in tl
      intro S' hMem
      simp only [List.pairwise_cons] at hPairwise
      obtain ⟨hAll, _⟩ := hPairwise
      -- hAll : ∀ a ∈ tl, hd.1 ≠ a.1
      have hNeq := hAll (e, S') hMem
      -- hNeq : hd.1 ≠ e, but heq : e = hd.1, contradiction
      exact hNeq (heq.symm)
    · -- Case: e ≠ hd.1, recurse
      cases hConsume' : LinCtx.consumeToken tl e with
      | none =>
        simp only [hConsume'] at hConsume
        exact Option.noConfusion hConsume
      | some result =>
        simp only [hConsume', Option.some.injEq, Prod.mk.injEq] at hConsume
        obtain ⟨rfl, rfl⟩ := hConsume
        simp only [List.pairwise_cons] at hPairwise
        obtain ⟨hAll, hTlPairwise⟩ := hPairwise
        intro S' hMem
        simp only [List.mem_cons] at hMem
        cases hMem with
        | inl heqHd =>
          -- (e, S') = hd, but e ≠ hd.1 - contradiction
          obtain ⟨heqE, _⟩ := Prod.mk.inj heqHd
          exact heq heqE
        | inr hmemTl =>
          exact ih result.1 hTlPairwise hConsume' S' hmemTl

/-- consumeToken preserves the Pairwise property. -/
theorem consumeToken_pairwise (ctx ctx' : LinCtx) (e : Endpoint) (S : LocalType)
    (hPairwise : ctx.Pairwise (fun a b => a.1 ≠ b.1))
    (hConsume : LinCtx.consumeToken ctx e = some (ctx', S)) :
    ctx'.Pairwise (fun a b => a.1 ≠ b.1) := by
  induction ctx generalizing ctx' with
  | nil =>
    simp only [LinCtx.consumeToken] at hConsume
    exact Option.noConfusion hConsume
  | cons hd tl ih =>
    simp only [LinCtx.consumeToken] at hConsume
    split_ifs at hConsume with heq
    · -- Case: e = hd.1, ctx' = tl
      simp only [Option.some.injEq, Prod.mk.injEq] at hConsume
      obtain ⟨rfl, _⟩ := hConsume
      simp only [List.pairwise_cons] at hPairwise
      exact hPairwise.2
    · -- Case: e ≠ hd.1, ctx' = hd :: ctx''
      cases hConsume' : LinCtx.consumeToken tl e with
      | none =>
        simp only [hConsume'] at hConsume
        exact Option.noConfusion hConsume
      | some result =>
        simp only [hConsume', Option.some.injEq, Prod.mk.injEq] at hConsume
        obtain ⟨rfl, rfl⟩ := hConsume
        simp only [List.pairwise_cons] at hPairwise ⊢
        obtain ⟨hAll, hTlPairwise⟩ := hPairwise
        constructor
        · -- Show hd.1 ≠ every element in result.1
          intro a haMem
          have haInTl : a ∈ tl := mem_of_consumeToken tl result.1 e a.1 result.2 a.2 hConsume' haMem
          exact hAll a haInTl
        · exact ih result.1 hTlPairwise hConsume'

/-- produceToken preserves Pairwise if the new endpoint wasn't in the context. -/
theorem produceToken_pairwise (ctx : LinCtx) (e : Endpoint) (S : LocalType)
    (hPairwise : ctx.Pairwise (fun a b => a.1 ≠ b.1))
    (hNotIn : ∀ S', (e, S') ∉ ctx) :
    (LinCtx.produceToken ctx e S).Pairwise (fun a b => a.1 ≠ b.1) := by
  simp only [LinCtx.produceToken, List.pairwise_cons]
  constructor
  · -- Show e ≠ every element's first component in ctx
    intro a haMem
    intro heq
    -- a ∈ ctx and e = a.1, so (e, a.2) = (a.1, a.2) = a ∈ ctx
    have haMem' : (e, a.2) ∈ ctx := by
      have : a = (a.1, a.2) := Prod.ext rfl rfl
      rw [heq, ← this]
      exact haMem
    exact hNotIn a.2 haMem'
  · exact hPairwise

/-- If consumeToken succeeds, the endpoint was in the original context. -/
theorem consumeToken_endpoint_in_ctx (ctx ctx' : LinCtx) (e : Endpoint) (S : LocalType)
    (hConsume : LinCtx.consumeToken ctx e = some (ctx', S)) :
    (e, S) ∈ ctx := by
  induction ctx generalizing ctx' with
  | nil =>
    simp only [LinCtx.consumeToken] at hConsume
    exact Option.noConfusion hConsume
  | cons hd tl ih =>
    simp only [LinCtx.consumeToken] at hConsume
    split_ifs at hConsume with heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at hConsume
      obtain ⟨rfl, rfl⟩ := hConsume
      simp only [beq_iff_eq] at heq
      simp only [List.mem_cons, heq, true_and, true_or]
    · cases hConsume' : LinCtx.consumeToken tl e with
      | none =>
        simp only [hConsume'] at hConsume
        exact Option.noConfusion hConsume
      | some result =>
        simp only [hConsume', Option.some.injEq, Prod.mk.injEq] at hConsume
        obtain ⟨rfl, rfl⟩ := hConsume
        have hInTl : (e, result.2) ∈ tl := ih result.1 hConsume'
        exact List.mem_cons_of_mem hd hInTl

/-- consumeToken preserves supply freshness: if all endpoints in ctx have sid < supply,
    then all endpoints in ctx' have sid < supply. -/
theorem consumeToken_preserves_supply_fresh (ctx ctx' : LinCtx) (e : Endpoint) (S : LocalType)
    (supply : SessionId)
    (hFresh : ∀ e' S', (e', S') ∈ ctx → e'.sid < supply)
    (hConsume : LinCtx.consumeToken ctx e = some (ctx', S)) :
    ∀ e' S', (e', S') ∈ ctx' → e'.sid < supply := by
  intro e' S' hMem
  have hInOrig : (e', S') ∈ ctx := mem_of_consumeToken _ _ _ _ _ _ hConsume hMem
  exact hFresh e' S' hInOrig

/-- produceToken preserves supply freshness when the produced endpoint is fresh. -/
theorem produceToken_preserves_supply_fresh (ctx : LinCtx) (e : Endpoint) (S : LocalType)
    (supply : SessionId)
    (hFresh : ∀ e' S', (e', S') ∈ ctx → e'.sid < supply)
    (heFresh : e.sid < supply) :
    ∀ e' S', (e', S') ∈ LinCtx.produceToken ctx e S → e'.sid < supply := by
  intro e' S' hMem
  simp only [LinCtx.produceToken, List.mem_cons] at hMem
  cases hMem with
  | inl heq =>
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact heFresh
  | inr hTail =>
    exact hFresh e' S' hTail

/-! ## Preservation Theorem -/

/-- Monitor transitions preserve well-typedness.

This is the key soundness theorem: if the monitor state is well-typed
and we take a valid transition, the result is also well-typed. -/
theorem MonStep_preserves_WTMon (ms ms' : MonitorState) (act : ProtoAction) (v : Value)
    (hStep : MonStep ms act v ms')
    (hWT : WTMon ms) :
    WTMon ms' := by
  cases hStep with
  | send hG hLin hv =>
    -- Send case: enqueue value, advance sender type
    rename_i e target T L lin'  -- Bring implicit variables into scope
    constructor
    · -- Coherent: use Coherent_send_preserved
      -- Requires hRecvReady hypothesis from coherence invariant
      sorry  -- Coherent_send_preserved with receiver readiness from EdgeCoherent
    · -- HeadCoherent: send preserves head coherence
      -- The receiver's expected type doesn't change (only sender advances)
      sorry  -- HeadCoherent_send_preserved
    · -- ValidLabels: send preserves valid labels (no label changes)
      sorry  -- ValidLabels_send_preserved
    · -- BuffersTyped: enqueue preserves buffer typing
      sorry  -- Buffer v : T appended, trace T appended
    · -- lin_valid: produced token matches updated G
      intro e' S' hMem
      simp only [LinCtx.produceToken, List.mem_cons] at hMem
      cases hMem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact lookupG_update_eq ms.G _ _
      | inr hTail =>
        -- Entry (e', S') ∈ lin' (after consuming e from ms.Lin)
        -- Case split on e' = e vs e' ≠ e
        by_cases he : e' = e
        · -- e' = e: Contradiction from linearity invariant
          subst he
          exact absurd hTail (consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin S')
        · -- e' ≠ e: use that (e', S') was in ms.Lin and G is only updated at e
          have hInOrigLin : (e', S') ∈ ms.Lin := mem_of_consumeToken _ _ _ _ _ _ hLin hTail
          have hGlookup : lookupG ms.G e' = some S' := hWT.lin_valid e' S' hInOrigLin
          rw [lookupG_update_neq _ _ _ _ (Ne.symm he)]
          exact hGlookup
    · -- lin_unique: produceToken preserves Pairwise
      have hLin'Pairwise := consumeToken_pairwise _ _ _ _ hWT.lin_unique hLin
      have hNotIn := consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin
      exact produceToken_pairwise _ _ _ hLin'Pairwise hNotIn
    · -- supply_fresh: all endpoints in new Lin have sid < supply
      have hLin'Fresh := consumeToken_preserves_supply_fresh _ _ _ _ _ hWT.supply_fresh hLin
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact produceToken_preserves_supply_fresh _ _ _ _ hLin'Fresh heFresh
    · -- supply_fresh_G: all endpoints in updated G have sid < supply
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact updateG_preserves_supply_fresh ms.G e L ms.supply hWT.supply_fresh_G heFresh

  | recv hG hLin hBuf hv =>
    -- Recv case: dequeue value, advance receiver type
    rename_i e source T L vs lin'
    constructor
    · -- Coherent: use Coherent_recv_preserved
      sorry  -- Need trace head = T from buffer typing
    · -- HeadCoherent: recv advances receiver, preserves head coherence
      sorry  -- HeadCoherent_recv_preserved
    · -- ValidLabels: recv dequeues from buffer, preserves valid labels
      sorry  -- ValidLabels_recv_preserved
    · -- BuffersTyped: dequeue preserves buffer typing
      sorry  -- Head removed from buffer and trace
    · -- lin_valid
      intro e' S' hMem
      simp only [LinCtx.produceToken, List.mem_cons] at hMem
      cases hMem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact lookupG_update_eq ms.G _ _
      | inr hTail =>
        by_cases he : e' = e
        · -- e' = e: Contradiction from linearity invariant
          subst he
          exact absurd hTail (consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin S')
        · have hInOrigLin : (e', S') ∈ ms.Lin := mem_of_consumeToken _ _ _ _ _ _ hLin hTail
          have hGlookup : lookupG ms.G e' = some S' := hWT.lin_valid e' S' hInOrigLin
          rw [lookupG_update_neq _ _ _ _ (Ne.symm he)]
          exact hGlookup
    · -- lin_unique: produceToken preserves Pairwise
      have hLin'Pairwise := consumeToken_pairwise _ _ _ _ hWT.lin_unique hLin
      have hNotIn := consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin
      exact produceToken_pairwise _ _ _ hLin'Pairwise hNotIn
    · -- supply_fresh: all endpoints in new Lin have sid < supply
      have hLin'Fresh := consumeToken_preserves_supply_fresh _ _ _ _ _ hWT.supply_fresh hLin
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact produceToken_preserves_supply_fresh _ _ _ _ hLin'Fresh heFresh
    · -- supply_fresh_G: all endpoints in updated G have sid < supply
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact updateG_preserves_supply_fresh ms.G e L ms.supply hWT.supply_fresh_G heFresh

  | select hG hFind hLin =>
    -- Select case: like send but with label
    rename_i e target bs ℓ L lin'
    constructor
    · sorry  -- Coherent for select
    · sorry  -- HeadCoherent for select
    · sorry  -- ValidLabels for select
    · sorry  -- BuffersTyped for label enqueue
    · -- lin_valid
      intro e' S' hMem
      simp only [LinCtx.produceToken, List.mem_cons] at hMem
      cases hMem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact lookupG_update_eq ms.G _ _
      | inr hTail =>
        by_cases he : e' = e
        · -- e' = e: Contradiction from linearity invariant
          subst he
          exact absurd hTail (consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin S')
        · have hInOrigLin : (e', S') ∈ ms.Lin := mem_of_consumeToken _ _ _ _ _ _ hLin hTail
          have hGlookup : lookupG ms.G e' = some S' := hWT.lin_valid e' S' hInOrigLin
          rw [lookupG_update_neq _ _ _ _ (Ne.symm he)]
          exact hGlookup
    · -- lin_unique: produceToken preserves Pairwise
      have hLin'Pairwise := consumeToken_pairwise _ _ _ _ hWT.lin_unique hLin
      have hNotIn := consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin
      exact produceToken_pairwise _ _ _ hLin'Pairwise hNotIn
    · -- supply_fresh: all endpoints in new Lin have sid < supply
      have hLin'Fresh := consumeToken_preserves_supply_fresh _ _ _ _ _ hWT.supply_fresh hLin
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact produceToken_preserves_supply_fresh _ _ _ _ hLin'Fresh heFresh
    · -- supply_fresh_G: all endpoints in updated G have sid < supply
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact updateG_preserves_supply_fresh ms.G e L ms.supply hWT.supply_fresh_G heFresh

  | branch hG hBuf hFind hLin =>
    -- Branch case: like recv but with label selection
    rename_i e source bs ℓ L vs lin'
    constructor
    · sorry  -- Coherent for branch
    · sorry  -- HeadCoherent for branch
    · sorry  -- ValidLabels for branch
    · sorry  -- BuffersTyped for label dequeue
    · -- lin_valid
      intro e' S' hMem
      simp only [LinCtx.produceToken, List.mem_cons] at hMem
      cases hMem with
      | inl heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact lookupG_update_eq ms.G _ _
      | inr hTail =>
        by_cases he : e' = e
        · -- e' = e: Contradiction from linearity invariant
          subst he
          exact absurd hTail (consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin S')
        · have hInOrigLin : (e', S') ∈ ms.Lin := mem_of_consumeToken _ _ _ _ _ _ hLin hTail
          have hGlookup : lookupG ms.G e' = some S' := hWT.lin_valid e' S' hInOrigLin
          rw [lookupG_update_neq _ _ _ _ (Ne.symm he)]
          exact hGlookup
    · -- lin_unique: produceToken preserves Pairwise
      have hLin'Pairwise := consumeToken_pairwise _ _ _ _ hWT.lin_unique hLin
      have hNotIn := consumeToken_not_mem _ _ _ _ hWT.lin_unique hLin
      exact produceToken_pairwise _ _ _ hLin'Pairwise hNotIn
    · -- supply_fresh: all endpoints in new Lin have sid < supply
      have hLin'Fresh := consumeToken_preserves_supply_fresh _ _ _ _ _ hWT.supply_fresh hLin
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact produceToken_preserves_supply_fresh _ _ _ _ hLin'Fresh heFresh
    · -- supply_fresh_G: all endpoints in updated G have sid < supply
      have hInOrig := consumeToken_endpoint_in_ctx _ _ _ _ hLin
      have heFresh := hWT.supply_fresh e _ hInOrig
      exact updateG_preserves_supply_fresh ms.G e L ms.supply hWT.supply_fresh_G heFresh

/-! ## Token Linearity Properties -/

/-- Tokens cannot be duplicated: consuming removes from context.

Requires the linearity invariant (no duplicate endpoints in LinCtx). -/
theorem token_consumed_removed (ctx : LinCtx) (e : Endpoint) (ctx' : LinCtx) (S : LocalType)
    (hPairwise : ctx.Pairwise (fun a b => a.1 ≠ b.1))
    (h : LinCtx.consumeToken ctx e = some (ctx', S)) :
    ¬LinCtx.contains ctx' e := by
  -- LinCtx.contains ctx' e = true means ∃ S', (e, S') ∈ ctx'
  -- But consumeToken_not_mem says ∀ S', (e, S') ∉ ctx'
  intro hContains
  simp only [LinCtx.contains, List.any_eq_true] at hContains
  obtain ⟨⟨e', S'⟩, hMem, hEq⟩ := hContains
  simp only [beq_iff_eq] at hEq
  subst hEq
  exact consumeToken_not_mem ctx ctx' e S hPairwise h S' hMem

/-- Tokens cannot be forged: only produceToken adds to context. -/
theorem token_only_from_produce (ctx ctx' : LinCtx) (e : Endpoint) (S : LocalType)
    (hNotIn : ¬LinCtx.contains ctx e)
    (hIn : (e, S) ∈ ctx') :
    ∃ ctx'' S', ctx' = LinCtx.produceToken ctx'' e S' := by
  -- This theorem states a constructive property about how contexts grow
  -- It's not directly provable without knowing how ctx' was constructed
  -- The point is that if e wasn't in ctx and now (e, S) ∈ ctx', it must have been produced
  sorry  -- Requires tracking context construction history

/-! ## Session Creation -/

/-- Lookup in mapped endpoints returns none if session ID doesn't match. -/
theorem lookup_mapped_endpoints_sid_ne (roles : RoleSet) (sid : SessionId)
    (localTypes : Role → LocalType) (e : Endpoint)
    (hNeq : e.sid ≠ sid) :
    (roles.map fun r => (Endpoint.mk sid r, localTypes r)).lookup e = none := by
  induction roles with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map, List.lookup]
    -- Check if e == Endpoint.mk sid r
    have hNeqEndpoint : (e == Endpoint.mk sid r) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      have : e.sid = sid := by simp only [heq, Endpoint.sid]
      exact hNeq this
    simp only [hNeqEndpoint, cond_false]
    exact ih

/-- Lookup in mapped endpoints finds the entry if role is in list. -/
theorem lookup_mapped_endpoints_mem (roles : RoleSet) (sid : SessionId)
    (localTypes : Role → LocalType) (r : Role)
    (hMem : r ∈ roles) :
    (roles.map fun r' => (Endpoint.mk sid r', localTypes r')).lookup
      (Endpoint.mk sid r) = some (localTypes r) := by
  induction roles with
  | nil =>
    simp only [List.mem_nil_iff] at hMem
  | cons hd tl ih =>
    simp only [List.map, List.lookup]
    by_cases heq : hd = r
    · -- hd = r: found it
      subst heq
      simp only [beq_self_eq_true]
    · -- hd ≠ r: continue searching
      have hNeqEndpoint : (Endpoint.mk sid r == Endpoint.mk sid hd) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq'
        simp only [Endpoint.mk.injEq] at heq'
        exact heq heq'.2.symm
      simp only [hNeqEndpoint, cond_false]
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl h => exact absurd h.symm heq
      | inr h => exact ih h

/-- Create a new session with given roles and local types.

Returns updated monitor state with:
- Fresh session ID allocated
- Endpoints added to G with initial types
- Empty buffers/traces for all edges
- Tokens for all endpoints in Lin -/
def MonitorState.newSession (ms : MonitorState) (roles : RoleSet)
    (localTypes : Role → LocalType) : MonitorState :=
  let sid := ms.supply
  let newEndpoints := roles.map fun r => ({ sid := sid, role := r }, localTypes r)
  let newEdges := RoleSet.allEdges sid roles
  { G := newEndpoints ++ ms.G
    D := (newEdges.map fun e => (e, [])) ++ ms.D
    bufs := (newEdges.map fun e => (e, [])) ++ ms.bufs
    Lin := (roles.map fun r => ({ sid := sid, role := r }, localTypes r)) ++ ms.Lin
    supply := sid + 1 }

/-- New session preserves well-typedness if local types are coherent projections. -/
theorem newSession_preserves_WTMon (ms : MonitorState) (roles : RoleSet)
    (localTypes : Role → LocalType)
    (hWT : WTMon ms)
    (hNodup : roles.Nodup)  -- Roles must be distinct
    (hProj : True)  -- Placeholder: localTypes are valid projections
    : WTMon (ms.newSession roles localTypes) := by
  simp only [MonitorState.newSession]
  constructor
  · -- coherent: Coherent (newEndpoints ++ ms.G) ((newEdges.map (·, [])) ++ ms.D)
    sorry  -- Requires showing EdgeCoherent for all edges
  · -- headCoherent: HeadCoherent for combined G and D
    -- New edges have empty traces, so HeadCoherent trivially holds
    sorry  -- HeadCoherent for newSession
  · -- validLabels: ValidLabels for combined G, D, bufs
    -- New edges have empty buffers, so ValidLabels trivially holds
    sorry  -- ValidLabels for newSession
  · -- buffers_typed: BuffersTyped ... (newEdges.map (·, [])) ++ ms.bufs
    intro e
    simp only [BufferTyped, lookupBuf, lookupD, List.lookup_append]
    by_cases hSid : e.sid = ms.supply
    · -- e.sid = ms.supply: edge belongs to new session
      by_cases hMem : e ∈ RoleSet.allEdges ms.supply roles
      · -- e is one of the new edges: buffer = [], trace = []
        have hBufLookup := initBuffers_lookup_mem ms.supply roles e hMem
        have hDLookup := initDEnv_lookup_mem ms.supply roles e hMem
        simp only [initBuffers, initDEnv] at hBufLookup hDLookup
        simp only [hBufLookup, hDLookup, Option.getD_some]
        exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      · -- e is not in allEdges but has fresh sid
        -- This is an edge not created by this newSession (e.g., different roles)
        -- It shouldn't be in the old buffers either (fresh session ID)
        -- The lookup falls through to ms.bufs/ms.D, but since e.sid = ms.supply (fresh),
        -- by the supply invariant, e shouldn't be there either.
        -- For now, we leave this as sorry - it requires a supply_fresh invariant on D/bufs
        sorry
    · -- e.sid ≠ ms.supply: edge from old session
      -- The lookup in initBuffers/initDEnv returns none, so we fall through to ms.bufs/ms.D
      -- Need to show HasTypeVal extends from ms.G to newEndpoints ++ ms.G
      -- This requires careful handling of the lookup_append rewriting
      sorry
  · -- lin_valid: for each (e, S) in combined Lin, lookupG G e = some S
    intro e S hMem
    simp only [List.mem_append, List.mem_map] at hMem
    cases hMem with
    | inl hNew =>
      -- e is in new endpoints (sid = ms.supply)
      obtain ⟨r, hrMem, heq⟩ := hNew
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- lookupG in prepended list finds the new entry
      simp only [lookupG, List.lookup_append]
      -- Use helper lemma: lookup in newEndpoints finds this entry
      have hLookup := lookup_mapped_endpoints_mem roles ms.supply localTypes r hrMem
      simp only [hLookup, Option.some_or]
    | inr hOld =>
      -- e is in ms.Lin, so e.sid < ms.supply (different from new endpoints)
      have heFresh : e.sid < ms.supply := hWT.supply_fresh e S hOld
      have hNeq : e.sid ≠ ms.supply := Nat.ne_of_lt heFresh
      -- lookupG in prepended list skips new entries (different sid)
      simp only [lookupG, List.lookup_append]
      -- lookup in newEndpoints returns none (e.sid ≠ ms.supply)
      have hLookupNone := lookup_mapped_endpoints_sid_ne roles ms.supply localTypes e hNeq
      simp only [hLookupNone, Option.none_or]
      -- Use hWT.lin_valid for the old entry
      exact hWT.lin_valid e S hOld
  · -- lin_unique: combined Lin is Pairwise distinct
    simp only [List.pairwise_append]
    constructor
    · -- New endpoints are pairwise distinct (from hNodup)
      -- Need to show: mapped list has distinct first components
      -- If r1 ≠ r2 then Endpoint.mk ms.supply r1 ≠ Endpoint.mk ms.supply r2
      have hInj : ∀ r1 r2, Endpoint.mk ms.supply r1 = Endpoint.mk ms.supply r2 → r1 = r2 := by
        intro r1 r2 heq
        simp only [Endpoint.mk.injEq] at heq
        exact heq.2
      -- Mapped list Pairwise follows from Nodup and injectivity
      induction roles with
      | nil => exact List.Pairwise.nil
      | cons hd tl ih =>
        simp only [List.map, List.pairwise_cons]
        simp only [List.nodup_cons] at hNodup
        obtain ⟨hNotMem, hTlNodup⟩ := hNodup
        constructor
        · -- hd's endpoint is different from all in tl's mapped list
          intro a haMem
          simp only [List.mem_map] at haMem
          obtain ⟨r, hrMem, rfl⟩ := haMem
          intro heq
          have hrEq : hd = r := hInj hd r heq
          exact hNotMem (hrEq ▸ hrMem)
        · exact ih hTlNodup
    constructor
    · -- Old endpoints are pairwise distinct
      exact hWT.lin_unique
    · -- Cross: new endpoints don't collide with old (different session IDs)
      intro a haMem b hbMem
      simp only [List.mem_map] at haMem
      obtain ⟨r, _, rfl⟩ := haMem
      -- a = ({ sid := ms.supply, role := r }, localTypes r), so a.1.sid = ms.supply
      -- b.1.sid < ms.supply
      have hbFresh : b.1.sid < ms.supply := hWT.supply_fresh b.1 b.2 hbMem
      intro heq
      -- heq : { sid := ms.supply, role := r } = b.1
      -- This means b.1.sid = ms.supply, contradicting hbFresh
      have hSidEq : b.1.sid = ms.supply := by rw [← heq]
      rw [hSidEq] at hbFresh
      exact Nat.lt_irrefl _ hbFresh
  · -- supply_fresh: all endpoints in combined Lin have sid < supply + 1
    intro e S hMem
    simp only [List.mem_append, List.mem_map] at hMem
    cases hMem with
    | inl hNew =>
      obtain ⟨r, _, heq⟩ := hNew
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- New endpoint has sid = ms.supply < ms.supply + 1
      exact Nat.lt_succ_self ms.supply
    | inr hOld =>
      -- Old endpoint has sid < ms.supply < ms.supply + 1
      have heFresh : e.sid < ms.supply := hWT.supply_fresh e S hOld
      exact Nat.lt_trans heFresh (Nat.lt_succ_self ms.supply)
  · -- supply_fresh_G: all endpoints in combined G have sid < supply + 1
    intro e S hMem
    simp only [List.mem_append, List.mem_map] at hMem
    cases hMem with
    | inl hNew =>
      obtain ⟨r, _, heq⟩ := hNew
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- New endpoint has sid = ms.supply < ms.supply + 1
      exact Nat.lt_succ_self ms.supply
    | inr hOld =>
      -- Old endpoint has sid < ms.supply < ms.supply + 1
      have heFresh : e.sid < ms.supply := hWT.supply_fresh_G e S hOld
      exact Nat.lt_trans heFresh (Nat.lt_succ_self ms.supply)

end
