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
    2. Buffers are typed according to D
    3. Linear context matches G -/
structure WTMon (ms : MonitorState) : Prop where
  /-- G and D are coherent -/
  coherent : Coherent ms.G ms.D
  /-- Buffers match type traces -/
  buffers_typed : BuffersTyped ms.G ms.D ms.bufs
  /-- Linear context entries match G -/
  lin_valid : ∀ e S, (e, S) ∈ ms.Lin → lookupG ms.G e = some S

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
    constructor
    · -- Coherent: use Coherent_send_preserved
      sorry
    · -- BuffersTyped: use BuffersTyped_enqueue
      sorry
    · -- lin_valid
      sorry
  | recv hG hLin hBuf hv =>
    constructor
    · -- Coherent: use Coherent_recv_preserved
      sorry
    · -- BuffersTyped: buffer dequeued
      sorry
    · -- lin_valid
      sorry
  | select hG hFind hLin =>
    constructor
    · sorry
    · sorry
    · sorry
  | branch hG hBuf hFind hLin =>
    constructor
    · sorry
    · sorry
    · sorry

/-! ## Token Linearity Properties -/

/-- Tokens cannot be duplicated: consuming removes from context. -/
theorem token_consumed_removed (ctx : LinCtx) (e : Endpoint) (ctx' : LinCtx) (S : LocalType)
    (h : LinCtx.consumeToken ctx e = some (ctx', S)) :
    ¬LinCtx.contains ctx' e := by
  sorry  -- Proof by induction on ctx

/-- Tokens cannot be forged: only produceToken adds to context. -/
theorem token_only_from_produce (ctx ctx' : LinCtx) (e : Endpoint) (S : LocalType)
    (hNotIn : ¬LinCtx.contains ctx e)
    (hIn : (e, S) ∈ ctx') :
    ∃ ctx'' S', ctx' = LinCtx.produceToken ctx'' e S' := by
  sorry  -- Structural property of LinCtx operations

/-! ## Session Creation -/

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
    (hProj : True)  -- Placeholder: localTypes are valid projections
    : WTMon (ms.newSession roles localTypes) := by
  sorry  -- Proof requires showing new endpoints + edges maintain coherence

end
