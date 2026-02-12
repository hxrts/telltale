import Protocol.Coherence

/-! # MPST Verified Monitor

This module implements the proof-carrying runtime monitor for MPST. -/

/-
The Problem. Untrusted code must interact with the session type system safely.
We need a runtime monitor that validates actions, maintains invariants, and
provides a safe interface for protocol execution.

Solution Structure. We define:
1. `MonitorState`: runtime state (GEnv, DEnv, buffers, linear context, supply)
2. `MonStep`: judgment for valid monitor transitions
3. `MonStep_preserves_WTMon`: preservation theorem
4. Capability token interface for untrusted code interaction
-/


/-! ## Overview

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

section

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
  D := (∅ : DEnv)
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
      (∀ Lrecv, lookupG ms.G { sid := e.sid, role := target } = some Lrecv →
        ∃ L', Consume e.role Lrecv (lookupD ms.D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
              (Consume e.role L' [T]).isSome) →
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
      (∀ Lrecv, lookupG ms.G { sid := e.sid, role := target } = some Lrecv →
        ∃ L', Consume e.role Lrecv (lookupD ms.D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
              (Consume e.role L' [.string]).isSome) →
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

/-! ## Complete Monitor Invariant -/

/-- Complete monitor invariant: well-typedness plus role completeness. -/
def WTMonComplete (ms : MonitorState) : Prop :=
  -- Combine typing invariants with endpoint coverage.
  WTMon ms ∧ RoleComplete ms.G

/-- Extract the WTMon component. -/
theorem WTMonComplete.toWTMon (ms : MonitorState) (h : WTMonComplete ms) : WTMon ms := by
  -- Project the well-typedness half.
  exact h.1

/-- Extract the RoleComplete component. -/
theorem WTMonComplete.toRoleComplete (ms : MonitorState) (h : WTMonComplete ms) :
    RoleComplete ms.G := by
  -- Project the role-completeness half.
  exact h.2

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
    intro a haMem heq
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
      have heq' : e = hd.1 := by
        simpa [beq_iff_eq] using heq
      subst heq'
      simp [List.mem_cons]
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


end
