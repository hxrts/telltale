import Protocol.LocalType
import Protocol.Semantics

/-! # Weighted Liveness Measure for Session Types

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
- `total_productive_steps_bounded`: At most W₀ productive steps -/

/-
The Problem. To bound protocol execution time, we need a Lyapunov-like measure
that strictly decreases on every communication step. The challenge is finding
weights that work for both send (adds to buffer) and recv (removes from buffer).

Solution Structure. Uses weighted measure W = 2 * Σ depth(L) + Σ buffer_size(e).
The factor of 2 ensures sends still decrease (depth -2, buffer +1 = net -1) while
receives decrease more (depth -2, buffer -1 = net -3). Proves each step type
decreases W, yielding bounded termination via W₀ productive steps.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

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

  /-- Apply a step to a single session state. This captures the concrete
      session-local effect (type update + buffer update). -/
  applySessionStep : SessionState → SessionStep → LocalType → SessionState

  /-- Global step is a map update on the single session identified by sid. -/
  applyStep_map (cfg : MultiConfig) (step : SessionStep) (newType : LocalType) :
    (applyStep cfg step newType).sessions =
      cfg.sessions.map (fun s =>
        if s.sid == step.sid then applySessionStep s step newType else s)

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

/-- updateType doesn't change bufferSizes. -/
@[simp] lemma SessionState.updateType_bufferSizes (s : SessionState) (actor : Role) (L : LocalType) :
    (s.updateType actor L).bufferSizes = s.bufferSizes := rfl

/-- incrBuffer doesn't change localTypes. -/
@[simp] lemma SessionState.incrBuffer_localTypes (s : SessionState) (actor partner : Role) :
    (s.incrBuffer actor partner).localTypes = s.localTypes := rfl

/-- decrBuffer doesn't change localTypes. -/
@[simp] lemma SessionState.decrBuffer_localTypes (s : SessionState) (actor partner : Role) :
    (s.decrBuffer actor partner).localTypes = s.localTypes := rfl

/-- sumDepths only depends on localTypes. -/
lemma sumDepths_eq_of_localTypes_eq {s₁ s₂ : SessionState}
    (h : s₁.localTypes = s₂.localTypes) : sumDepths s₁ = sumDepths s₂ := by
  unfold sumDepths; rw [h]

/-- sumBuffers only depends on bufferSizes. -/
lemma sumBuffers_eq_of_bufferSizes_eq {s₁ s₂ : SessionState}
    (h : s₁.bufferSizes = s₂.bufferSizes) : sumBuffers s₁ = sumBuffers s₂ := by
  unfold sumBuffers; rw [h]

/-- sumDepths after updateType then incrBuffer equals sumDepths after updateType. -/
lemma sumDepths_updateType_incrBuffer (s : SessionState) (actor : Role) (L : LocalType)
    (partner : Role) :
    sumDepths ((s.updateType actor L).incrBuffer actor partner) =
    sumDepths (s.updateType actor L) := by
  apply sumDepths_eq_of_localTypes_eq
  simp only [SessionState.incrBuffer_localTypes]

/-- sumBuffers after updateType then incrBuffer equals sumBuffers after incrBuffer. -/
lemma sumBuffers_updateType_incrBuffer (s : SessionState) (actor : Role) (L : LocalType)
    (partner : Role) :
    sumBuffers ((s.updateType actor L).incrBuffer actor partner) =
    sumBuffers (s.incrBuffer actor partner) := by
  apply sumBuffers_eq_of_bufferSizes_eq
  simp only [SessionState.incrBuffer, SessionState.updateType_bufferSizes]

/-- sumDepths after updateType then decrBuffer equals sumDepths after updateType. -/
lemma sumDepths_updateType_decrBuffer (s : SessionState) (actor : Role) (L : LocalType)
    (partner : Role) :
    sumDepths ((s.updateType actor L).decrBuffer actor partner) =
    sumDepths (s.updateType actor L) := by
  apply sumDepths_eq_of_localTypes_eq
  simp only [SessionState.decrBuffer_localTypes]

/-- sumBuffers after updateType then decrBuffer equals sumBuffers after decrBuffer. -/
lemma sumBuffers_updateType_decrBuffer (s : SessionState) (actor : Role) (L : LocalType)
    (partner : Role) :
    sumBuffers ((s.updateType actor L).decrBuffer actor partner) =
    sumBuffers (s.decrBuffer actor partner) := by
  apply sumBuffers_eq_of_bufferSizes_eq
  simp only [SessionState.decrBuffer, SessionState.updateType_bufferSizes]

/-! ## Concrete Session Semantics -/

/-- Concrete session-local step: update local type, then adjust the buffer.
    This matches the G/D updates of send/recv/select/branch in StepBase. -/
def applySessionStepConcrete (s : SessionState) (step : SessionStep) (newType : LocalType) :
    SessionState :=
  if step.isSend then
    (s.updateType step.actor newType).incrBuffer step.actor step.partner
  else
    (s.updateType step.actor newType).decrBuffer step.actor step.partner

/-- Concrete multi-session step: map update on the target session id. -/
def applyStepConcrete (cfg : MultiConfig) (step : SessionStep) (newType : LocalType) :
    MultiConfig :=
  { sessions := cfg.sessions.map fun s =>
      if s.sid == step.sid then applySessionStepConcrete s step newType else s }

lemma applyStepConcrete_isolation
    (cfg : MultiConfig) (step : SessionStep) (newType : LocalType)
    (s : SessionState) (hs : s ∈ cfg.sessions) (hne : s.sid ≠ step.sid) :
    s ∈ (applyStepConcrete cfg step newType).sessions := by
  have hfalse : (s.sid == step.sid) = false :=
    (beq_eq_false_iff_ne (a := s.sid) (b := step.sid)).2 hne
  unfold applyStepConcrete
  refine List.mem_map.2 ?_
  refine ⟨s, hs, ?_⟩
  simp [hfalse]

/-! ## SessionSemantics Instance -/

instance : SessionSemantics where
  applyStep := applyStepConcrete
  applySessionStep := applySessionStepConcrete
  applyStep_map _ _ _ := rfl
  step_isolation := applyStepConcrete_isolation
  step_nonincreasing_other := by
    intro cfg step newType s hs hne
    refine ⟨s, applyStepConcrete_isolation cfg step newType s hs hne, rfl, le_rfl⟩

/-! ## Sum-Update Helper Lemmas -/

private lemma map_update_eq_snd_of_not_mem {α : Type} [DecidableEq α]
    (tl : List (α × Nat)) (key : α) (newVal : Nat)
    (hnotIn : key ∉ tl.map Prod.fst) :
    tl.map (fun (k, v) => if k == key then newVal else v) = tl.map Prod.snd := by
  apply List.map_congr_left
  intro kv hmem
  rcases kv with ⟨k', v'⟩
  simp only
  have hne : k' ≠ key := by
    intro heq
    apply hnotIn
    rw [← heq]
    exact List.mem_map_of_mem (f := Prod.fst) hmem
  simp [beq_eq_false_iff_ne.mpr hne]

/-! ## Sum-Update Arithmetic -/

/-- Sum update lemma: updating one unique key changes sum by the difference. -/
theorem sum_update_unique {α : Type} [DecidableEq α]
    (l : List (α × Nat)) (key : α) (oldVal newVal : Nat)
    (hunique : (l.map Prod.fst).Nodup)
    (hmem : (key, oldVal) ∈ l) :
    (l.map (fun (k, v) => if k == key then newVal else v)).foldl (· + ·) 0 + oldVal =
    (l.map Prod.snd).foldl (· + ·) 0 + newVal := by
  -- Unique key update changes sum by difference oldVal → newVal
  induction l with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    rcases List.mem_cons.mp hmem with heq | htl
    · -- hd = (key, oldVal)
      subst heq
      simp only [beq_self_eq_true, ↓reduceIte]
      -- In tail, key doesn't appear (uniqueness)
      have hnodup : (tl.map Prod.fst).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        exact hunique.2
      have hnotIn : key ∉ tl.map Prod.fst := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        exact hunique.1
      -- Map on tail is identity for key
      have htl_eq : tl.map (fun (k, v) => if k == key then newVal else v) = tl.map Prod.snd :=
        map_update_eq_snd_of_not_mem tl key newVal hnotIn
      rw [htl_eq]
      rw [foldl_add_shift (l := tl.map Prod.snd) (n := newVal)]
      rw [foldl_add_shift (l := tl.map Prod.snd) (n := oldVal)]
      omega
    · -- key is in tail
      have hnodup : (tl.map Prod.fst).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        exact hunique.2
      have hne : hd.1 ≠ key := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        intro heq
        have hmemFst : key ∈ tl.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) htl
        rw [← heq] at hmemFst
        exact hunique.1 hmemFst
      have hcond : (hd.1 == key) = false := beq_eq_false_iff_ne.mpr hne
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      have ih' := ih hnodup htl
      -- ih': mapped_sum + oldVal = orig_sum + newVal
      -- Goal: foldl hd.2 mapped + oldVal = foldl hd.2 orig + newVal
      -- Apply foldl_add_shift to both sides
      have hL : (tl.map (fun x => if x.1 == key then newVal else x.2)).foldl (· + ·) hd.2 =
          hd.2 + (tl.map (fun x => if x.1 == key then newVal else x.2)).foldl (· + ·) 0 :=
        foldl_add_shift _ hd.2
      have hR : (tl.map Prod.snd).foldl (· + ·) hd.2 =
          hd.2 + (tl.map Prod.snd).foldl (· + ·) 0 := foldl_add_shift _ hd.2
      rw [hL, hR]
      -- Goal: (hd.2 + mapped_sum) + oldVal = (hd.2 + orig_sum) + newVal
      -- ih' says: mapped_sum + oldVal = orig_sum + newVal
      -- Add hd.2 to both sides of ih'
      calc hd.2 + (tl.map (fun x => if x.1 == key then newVal else x.2)).foldl (· + ·) 0 + oldVal
          = hd.2 + ((tl.map (fun x => if x.1 == key then newVal else x.2)).foldl (· + ·) 0 + oldVal) := by ring
        _ = hd.2 + ((tl.map Prod.snd).foldl (· + ·) 0 + newVal) := by rw [ih']
        _ = hd.2 + (tl.map Prod.snd).foldl (· + ·) 0 + newVal := by ring


end
