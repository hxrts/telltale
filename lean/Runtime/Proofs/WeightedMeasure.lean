import Protocol.LocalType
import Protocol.Semantics

/-!
# Weighted Liveness Measure for Session Types

Defines the weighted progress measure for async multiparty session types:

  W = 2 * Σ depth(L) + Σ buffer_size(e)

This measure strictly decreases under every productive step:
- Send:   depth -2, buffer +1 → net -1
- Recv:   depth -2, buffer -1 → net -3
- Select: depth -2, buffer +1 → net -1
- Branch: depth -2, buffer -1 → net -3

## Main Definitions

- `SessionState`: Abstract per-session state (roles, types, buffers)
- `weightedMeasure`: The Lyapunov function W
- `SessionSemantics`: Typeclass for step semantics

## Main Results

- `send_step_decreases`: Send decreases W by at least 1
- `recv_step_decreases`: Recv decreases W by at least 3
- `select_step_decreases`: Select decreases W by at least 1
- `branch_step_decreases`: Branch decreases W by at least 3
- `total_measure_decreasing`: Any productive step decreases total W
- `total_productive_steps_bounded`: At most W₀ productive steps

## References

Ported from Aristotle files 09 and 09b.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Session State Abstraction -/

/-- Per-session state: roles, local types, and buffer sizes.
    This abstracts over the concrete representation in Protocol. -/
structure SessionState where
  /-- Session identifier. -/
  sid : SessionId
  /-- Roles participating in this session. -/
  roles : List Role
  /-- Local type for each role. List of (role, type) pairs. -/
  localTypes : List (Role × LocalType)
  /-- Buffer sizes for each directed edge. List of (sender, receiver, size). -/
  bufferSizes : List (Role × Role × Nat)

namespace SessionState

/-- Lookup the local type for a role. -/
def lookupType (s : SessionState) (r : Role) : Option LocalType :=
  match s.localTypes.find? (fun p => p.1 == r) with
  | some (_, L) => some L
  | none => none

/-- Get buffer size for a directed edge. -/
def getBuffer (s : SessionState) (sender receiver : Role) : Nat :=
  match s.bufferSizes.find? (fun (s', r', _) => s' == sender && r' == receiver) with
  | some (_, _, n) => n
  | none => 0

/-- Uniqueness: each role appears at most once in localTypes. -/
def uniqueRoles (s : SessionState) : Prop :=
  (s.localTypes.map Prod.fst).Nodup

/-- Uniqueness: each directed edge appears at most once in bufferSizes. -/
def uniqueBuffers (s : SessionState) : Prop :=
  (s.bufferSizes.map fun (s', r', _) => (s', r')).Nodup

end SessionState

/-! ## Weighted Measure -/

/-- Sum of depths across all local types in a session. -/
def sumDepths (s : SessionState) : Nat :=
  (s.localTypes.map (fun (_, L) => L.depth)).foldl (· + ·) 0

/-- Sum of buffer sizes across all edges in a session. -/
def sumBuffers (s : SessionState) : Nat :=
  (s.bufferSizes.map (fun (_, _, n) => n)).foldl (· + ·) 0

/-- Weighted progress measure for a single session:
    W(s) = 2 * Σ depth(L) + Σ buffer_size(e)

    The factor of 2 on depth ensures:
    - Send: depth -1 contributes -2, buffer +1, net = -1
    - Recv: depth -1 contributes -2, buffer -1, net = -3
    - Select: depth -1 contributes -2, buffer +1, net = -1
    - Branch: depth -1 contributes -2, buffer -1, net = -3 -/
def weightedMeasure (s : SessionState) : Nat :=
  2 * sumDepths s + sumBuffers s

/-! ## Multi-Session Configuration -/

/-- Configuration with multiple sessions. -/
structure MultiConfig where
  sessions : List SessionState

/-- Total weighted measure across all sessions. -/
def totalWeightedMeasure (cfg : MultiConfig) : Nat :=
  (cfg.sessions.map weightedMeasure).foldl (· + ·) 0

/-- Uniqueness: each session ID appears at most once. -/
def MultiConfig.uniqueSids (cfg : MultiConfig) : Prop :=
  (cfg.sessions.map (·.sid)).Nodup

/-! ## Step Representation -/

/-- A session step: identifies the session, actor, partner, and type. -/
structure SessionStep where
  sid : SessionId
  actor : Role
  partner : Role
  isSend : Bool  -- true for send/select, false for recv/branch

/-! ## Session Semantics Typeclass -/

/-- Abstract semantics for session steps.

    This typeclass captures the key properties needed for the liveness proof:
    1. Steps on one session don't affect other sessions (isolation)
    2. Steps on unrelated sessions preserve their measure
    3. Productive steps on the target session decrease its measure -/
class SessionSemantics where
  /-- Apply a step to a configuration, producing a new local type. -/
  applyStep : MultiConfig → SessionStep → LocalType → MultiConfig

  /-- Steps don't affect sessions with different SIDs. -/
  step_isolation (cfg : MultiConfig) (step : SessionStep) (newType : LocalType)
      (s : SessionState) :
      s ∈ cfg.sessions → s.sid ≠ step.sid →
      s ∈ (applyStep cfg step newType).sessions

  /-- Steps preserve measure of unrelated sessions. -/
  step_nonincreasing_other (cfg : MultiConfig) (step : SessionStep) (newType : LocalType)
      (s : SessionState) (hs : s ∈ cfg.sessions) (hne : s.sid ≠ step.sid) :
      ∃ s' ∈ (applyStep cfg step newType).sessions,
        s'.sid = s.sid ∧ weightedMeasure s' ≤ weightedMeasure s

/-! ## Helper Lemmas for Sum Updates -/

/-- foldl (+) 0 computes the sum of a list. -/
theorem foldl_add_eq_sum (l : List Nat) : l.foldl (· + ·) 0 = l.sum := by
  rw [List.sum_eq_foldl]

/-- foldl (+) n = n + foldl (+) 0. -/
theorem foldl_add_shift (l : List Nat) (n : Nat) :
    l.foldl (· + ·) n = n + l.foldl (· + ·) 0 := by
  induction l generalizing n with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl, Nat.zero_add]
    -- Goal: t.foldl (n + h) = n + t.foldl h
    have ih1 := ih (n + h)
    have ih2 := ih h
    calc t.foldl (· + ·) (n + h) = (n + h) + t.foldl (· + ·) 0 := ih1
      _ = n + (h + t.foldl (· + ·) 0) := by ring
      _ = n + t.foldl (· + ·) h := by rw [← ih2]

/-! ## Step Decrease Theorems

These theorems show that each type of communication step strictly
decreases the weighted measure. -/

/-- Update a session's local type for a given role. -/
def SessionState.updateType (s : SessionState) (actor : Role) (newType : LocalType) :
    SessionState :=
  { s with localTypes := s.localTypes.map fun (r, L) =>
      if r == actor then (r, newType) else (r, L) }

/-- Increment buffer from actor to partner. -/
def SessionState.incrBuffer (s : SessionState) (actor partner : Role) : SessionState :=
  { s with bufferSizes := s.bufferSizes.map fun (s', r', n) =>
      if s' == actor && r' == partner then (s', r', n + 1) else (s', r', n) }

/-- Decrement buffer from partner to actor. -/
def SessionState.decrBuffer (s : SessionState) (actor partner : Role) : SessionState :=
  { s with bufferSizes := s.bufferSizes.map fun (s', r', n) =>
      if s' == partner && r' == actor then (s', r', n - 1) else (s', r', n) }

/-- Sum update lemma: updating one unique key changes sum by the difference. -/
theorem sum_update_unique {α : Type} [DecidableEq α]
    (l : List (α × Nat)) (key : α) (oldVal newVal : Nat)
    (hunique : (l.map Prod.fst).Nodup)
    (hmem : (key, oldVal) ∈ l) :
    (l.map (fun (k, v) => if k == key then newVal else v)).foldl (· + ·) 0 + oldVal =
    (l.map Prod.snd).foldl (· + ·) 0 + newVal := by
  -- This requires careful induction with uniqueness tracking
  sorry

/-- Send step decreases the weighted measure.

    When actor sends to partner with type `send partner T L`:
    - Actor's depth decreases from (1 + L.depth) to L.depth (delta = -1)
    - Buffer (actor, partner) increases by 1
    - Net change to W = 2*(-1) + 1 = -1 -/
theorem send_step_decreases
    (s : SessionState) (actor partner : Role) (T : ValType) (L : LocalType)
    (hlookup : s.lookupType actor = some (.send partner T L))
    (hunique_roles : s.uniqueRoles)
    (hunique_buffers : s.uniqueBuffers)
    (s' : SessionState)
    (hs' : s' = (s.updateType actor L).incrBuffer actor partner) :
    weightedMeasure s' < weightedMeasure s := by
  -- The depth sum decreases by at least 1 (actor's type: send partner T L → L)
  -- The buffer sum increases by at most 1
  -- Net: 2*(-1) + 1 = -1, so W decreases by at least 1
  sorry

/-- Recv step decreases the weighted measure.

    When actor receives from partner with type `recv partner T L`:
    - Actor's depth decreases from (1 + L.depth) to L.depth (delta = -1)
    - Buffer (partner, actor) decreases by 1
    - Net change to W = 2*(-1) + (-1) = -3 -/
theorem recv_step_decreases
    (s : SessionState) (actor partner : Role) (T : ValType) (L : LocalType)
    (hlookup : s.lookupType actor = some (.recv partner T L))
    (hbuf : s.getBuffer partner actor > 0)
    (hunique_roles : s.uniqueRoles)
    (hunique_buffers : s.uniqueBuffers)
    (s' : SessionState)
    (hs' : s' = (s.updateType actor L).decrBuffer actor partner) :
    weightedMeasure s' < weightedMeasure s := by
  sorry

/-- Select step decreases the weighted measure.

    When actor selects label ℓ to partner with type `select partner branches`:
    - Actor's depth decreases from (1 + depthList branches) to L.depth where (ℓ, L) ∈ branches
    - Buffer (actor, partner) increases by 1
    - Net change: depth decreases by at least 1, buffer increases by 1
    - W change = 2*(-1) + 1 = -1 -/
theorem select_step_decreases
    (s : SessionState) (actor partner : Role) (branches : List (Label × LocalType))
    (ℓ : Label) (L : LocalType)
    (hlookup : s.lookupType actor = some (.select partner branches))
    (hmem : (ℓ, L) ∈ branches)
    (hunique_roles : s.uniqueRoles)
    (hunique_buffers : s.uniqueBuffers)
    (s' : SessionState)
    (hs' : s' = (s.updateType actor L).incrBuffer actor partner) :
    weightedMeasure s' < weightedMeasure s := by
  sorry

/-- Branch step decreases the weighted measure.

    When actor branches on label ℓ from partner with type `branch partner branches`:
    - Actor's depth decreases from (1 + depthList branches) to L.depth where (ℓ, L) ∈ branches
    - Buffer (partner, actor) decreases by 1
    - Net change: depth decreases by at least 1, buffer decreases by 1
    - W change = 2*(-1) + (-1) = -3 -/
theorem branch_step_decreases
    (s : SessionState) (actor partner : Role) (branches : List (Label × LocalType))
    (ℓ : Label) (L : LocalType)
    (hlookup : s.lookupType actor = some (.branch partner branches))
    (hmem : (ℓ, L) ∈ branches)
    (hbuf : s.getBuffer partner actor > 0)
    (hunique_roles : s.uniqueRoles)
    (hunique_buffers : s.uniqueBuffers)
    (s' : SessionState)
    (hs' : s' = (s.updateType actor L).decrBuffer actor partner) :
    weightedMeasure s' < weightedMeasure s := by
  sorry

/-! ## Total Measure Decrease -/

/-- Any productive step decreases the total weighted measure. -/
theorem total_measure_decreasing [sem : SessionSemantics]
    (cfg : MultiConfig) (step : SessionStep) (newType : LocalType)
    (s_stepped : SessionState)
    (hs : s_stepped ∈ cfg.sessions)
    (hsid : s_stepped.sid = step.sid)
    (hunique_roles : s_stepped.uniqueRoles)
    (hunique_buffers : s_stepped.uniqueBuffers)
    (hunique_sids : cfg.uniqueSids)
    (hdecrease : weightedMeasure s_stepped > weightedMeasure (s_stepped.updateType step.actor newType)) :
    totalWeightedMeasure (sem.applyStep cfg step newType) < totalWeightedMeasure cfg := by
  sorry

/-! ## Productive Trace Bound -/

/-- A trace is productive if every step decreases the total measure. -/
def ProductiveTrace [SessionSemantics] (cfg : MultiConfig) :
    List (SessionStep × LocalType) → Prop
  | [] => True
  | (step, newType) :: rest =>
    totalWeightedMeasure (SessionSemantics.applyStep cfg step newType) < totalWeightedMeasure cfg ∧
    ProductiveTrace (SessionSemantics.applyStep cfg step newType) rest

/-- The number of productive steps is bounded by the initial weighted measure. -/
theorem total_productive_steps_bounded [SessionSemantics]
    (cfg₀ : MultiConfig) (steps : List (SessionStep × LocalType))
    (hprod : ProductiveTrace cfg₀ steps) :
    steps.length ≤ totalWeightedMeasure cfg₀ := by
  induction steps generalizing cfg₀ with
  | nil => exact Nat.zero_le _
  | cons hd tl ih =>
    have hdec := hprod.1
    have htl := ih _ hprod.2
    simp only [List.length_cons]
    omega

/-! ## Shared Participant Decomposition -/

/-- Sessions a role participates in. -/
def roleSessions (cfg : MultiConfig) (r : Role) : List SessionId :=
  cfg.sessions.filterMap fun s => if r ∈ s.roles then some s.sid else none

/-- A shared participant is a role in multiple sessions. -/
def SharedParticipant (cfg : MultiConfig) (s1 s2 : SessionId) (r : Role) : Prop :=
  s1 ∈ roleSessions cfg r ∧ s2 ∈ roleSessions cfg r ∧ s1 ≠ s2

/-- Measure additivity: the total measure is the sum of session measures.
    Shared participants do not introduce multiplicative overhead. -/
theorem shared_participant_no_overhead_unique
    (cfg : MultiConfig) (s1 s2 : SessionState) (r : Role)
    (hs1 : s1 ∈ cfg.sessions) (hs2 : s2 ∈ cfg.sessions)
    (hshared : SharedParticipant cfg s1.sid s2.sid r)
    (hunique : cfg.uniqueSids) :
    totalWeightedMeasure cfg ≤ weightedMeasure s1 + weightedMeasure s2 +
      ((cfg.sessions.filter (fun s => s.sid ≠ s1.sid ∧ s.sid ≠ s2.sid)).map weightedMeasure).foldl (· + ·) 0 := by
  sorry

end
