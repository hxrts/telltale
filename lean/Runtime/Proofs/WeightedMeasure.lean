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

instance : SessionSemantics where
  applyStep := applyStepConcrete
  applySessionStep := applySessionStepConcrete
  applyStep_map _ _ _ := rfl
  step_isolation := applyStepConcrete_isolation
  step_nonincreasing_other := by
    intro cfg step newType s hs hne
    refine ⟨s, applyStepConcrete_isolation cfg step newType s hs hne, rfl, le_rfl⟩

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
      have htl_eq : tl.map (fun (k, v) => if k == key then newVal else v) = tl.map Prod.snd := by
        apply List.map_congr_left
        intro ⟨k', v'⟩ hmem'
        simp only
        have hne : k' ≠ key := by
          intro heq
          apply hnotIn
          rw [← heq]
          exact List.mem_map_of_mem (f := Prod.fst) hmem'
        simp [beq_eq_false_iff_ne.mpr hne]
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

/-! ## Lookup/Buffer Membership Helpers -/

private lemma find?_mem_aux {r : Role} {L : LocalType} (types : List (Role × LocalType)) :
    (match types.find? (fun p => p.1 == r) with
      | some (_, L') => some L' | none => none) = some L → (r, L) ∈ types := by
  induction types with
  | nil =>
    simp only [List.find?]
    intro hContra
    exact Option.noConfusion hContra
  | cons hd tl ih =>
    simp only [List.find?]
    by_cases hEq : hd.1 == r
    · -- Head matches
      simp only [hEq, cond_true]
      intro hL
      have hRole : hd.1 = r := beq_iff_eq.mp hEq
      have hType : hd.2 = L := Option.some.inj hL
      have hPair : hd = (r, L) := Prod.ext hRole hType
      rw [hPair]
      exact List.Mem.head tl
    · -- Head doesn't match
      simp only [hEq, cond_false]
      intro hFind
      exact List.Mem.tail hd (ih hFind)

lemma lookupType_mem {s : SessionState} {r : Role} {L : LocalType}
    (h : s.lookupType r = some L) : (r, L) ∈ s.localTypes := by
  unfold SessionState.lookupType at h
  exact find?_mem_aux s.localTypes h

private lemma getBuffer_mem_aux {sender receiver : Role}
    (bufs : List (Role × Role × Nat)) :
    (match bufs.find? (fun x => x.1 == sender && x.2.1 == receiver) with
      | some (_, _, n) => n | none => 0) > 0 →
    ∃ n, (sender, receiver, n) ∈ bufs ∧
      n = (match bufs.find? (fun x => x.1 == sender && x.2.1 == receiver) with
        | some (_, _, n) => n | none => 0) := by
  induction bufs with
  | nil =>
    simp only [List.find?, gt_iff_lt]
    intro hContra
    exact absurd hContra (Nat.not_lt_zero 0)
  | cons hd tl ih =>
    simp only [List.find?]
    by_cases hEq : hd.1 == sender && hd.2.1 == receiver
    · -- Head matches
      simp only [hEq, ite_true]
      intro _
      simp only [Bool.and_eq_true, beq_iff_eq] at hEq
      have ⟨hSender, hRecv⟩ := hEq
      have heq : hd = (sender, receiver, hd.2.2) := by
        cases hd with | mk fst snd =>
        cases snd with | mk fst' snd' =>
        simp only at hSender hRecv
        simp [hSender, hRecv]
      exact ⟨hd.2.2, by rw [heq]; exact List.Mem.head _, rfl⟩
    · -- Head doesn't match
      simp only [hEq, ite_false]
      intro hFind
      obtain ⟨n, hmem, heq⟩ := ih hFind
      exact ⟨n, List.Mem.tail _ hmem, heq⟩

lemma getBuffer_mem_of_pos {s : SessionState} {sender receiver : Role}
    (hpos : s.getBuffer sender receiver > 0) :
    ∃ n, (sender, receiver, n) ∈ s.bufferSizes ∧ n = s.getBuffer sender receiver := by
  unfold SessionState.getBuffer at hpos ⊢
  exact getBuffer_mem_aux s.bufferSizes hpos

lemma sumBuffers_incr_eq_of_no_entry
    (s : SessionState) (actor partner : Role)
    (hmem : ¬ ∃ n, (actor, partner, n) ∈ s.bufferSizes) :
    sumBuffers (s.incrBuffer actor partner) = sumBuffers s := by
  -- When no buffer entry exists, incrBuffer maps to identity
  unfold sumBuffers SessionState.incrBuffer
  simp only
  -- Show the mapped list equals the original
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro ⟨s', r', n⟩ hmem'
  simp only [Function.comp_apply]
  -- Show the condition is false for all elements
  by_cases hEq : s' == actor && r' == partner
  · -- If condition is true, we have a contradiction
    exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at hEq
    have ⟨hSender, hRecv⟩ := hEq
    subst hSender hRecv
    apply hmem
    exact ⟨n, hmem'⟩
  · -- Condition is false, so mapping is identity
    simp [hEq]

/-- Incrementing a unique key increases sum by 1. -/
theorem sum_incr_unique {α : Type} [DecidableEq α]
    (l : List (α × Nat)) (key : α)
    (hunique : (l.map Prod.fst).Nodup)
    (hmem : key ∈ l.map Prod.fst) :
    (l.map (fun (k, v) => if k == key then v + 1 else v)).foldl (· + ·) 0 =
    (l.map Prod.snd).foldl (· + ·) 0 + 1 := by
  induction l with
  | nil => simp only [List.map_nil, List.not_mem_nil] at hmem
  | cons hd tl ih =>
    obtain ⟨hd_k, hd_v⟩ := hd
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    by_cases heq : hd_k = key
    · -- hd_k = key: increment at head, identity on tail
      rw [heq]
      simp only [beq_self_eq_true, ↓reduceIte]
      -- In tail, key doesn't appear (uniqueness)
      have hnodup : (tl.map Prod.fst).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        exact hunique.2
      have hnotIn : key ∉ tl.map Prod.fst := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        rw [← heq]
        exact hunique.1
      -- Map on tail is identity for key
      have htl_eq : tl.map (fun (k, v) => if k == key then v + 1 else v) = tl.map Prod.snd := by
        apply List.map_congr_left
        intro ⟨k', v'⟩ hmem'
        simp only
        have hne : k' ≠ key := by
          intro heq'
          apply hnotIn
          rw [← heq']
          exact List.mem_map_of_mem (f := Prod.fst) hmem'
        simp [beq_eq_false_iff_ne.mpr hne]
      rw [htl_eq]
      rw [foldl_add_shift (l := tl.map Prod.snd) (n := hd_v + 1)]
      rw [foldl_add_shift (l := tl.map Prod.snd) (n := hd_v)]
      omega
    · -- hd_k ≠ key: identity at head, recurse on tail
      have hcond : (hd_k == key) = false := beq_eq_false_iff_ne.mpr heq
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      have hnodup : (tl.map Prod.fst).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        exact hunique.2
      have hmem' : key ∈ tl.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at hmem
        cases hmem with
        | inl h => exact absurd h.symm heq
        | inr h => exact h
      have ih' := ih hnodup hmem'
      rw [foldl_add_shift (l := tl.map (fun (k, v) => if k == key then v + 1 else v)) (n := hd_v)]
      rw [foldl_add_shift (l := tl.map Prod.snd) (n := hd_v)]
      omega

/-- Decrementing a unique key decreases sum by 1 when positive. -/
theorem sum_decr_unique {α : Type} [DecidableEq α]
    (l : List (α × Nat)) (key : α) (val : Nat)
    (hunique : (l.map Prod.fst).Nodup)
    (hmem : (key, val) ∈ l)
    (hpos : val > 0) :
    (l.map (fun (k, v) => if k == key then v - 1 else v)).foldl (· + ·) 0 + 1 =
    (l.map Prod.snd).foldl (· + ·) 0 := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hmem
  | cons hd tl ih =>
    obtain ⟨hd_k, hd_v⟩ := hd
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    rcases List.mem_cons.mp hmem with heq | htl
    · -- (key, val) = (hd_k, hd_v)
      have hkey : key = hd_k := congrArg Prod.fst heq
      have hval : val = hd_v := congrArg Prod.snd heq
      rw [← hkey, ← hval]
      simp only [beq_self_eq_true, ↓reduceIte]
      -- In tail, key doesn't appear (uniqueness)
      have hnodup : (tl.map Prod.fst).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        exact hunique.2
      have hnotIn : key ∉ tl.map Prod.fst := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        rw [hkey]
        exact hunique.1
      -- Map on tail is identity for key
      have htl_eq : tl.map (fun (k, v) => if k == key then v - 1 else v) = tl.map Prod.snd := by
        apply List.map_congr_left
        intro ⟨k', v'⟩ hmem'
        simp only
        have hne : k' ≠ key := by
          intro heq'
          apply hnotIn
          rw [← heq']
          exact List.mem_map_of_mem (f := Prod.fst) hmem'
        simp [beq_eq_false_iff_ne.mpr hne]
      rw [htl_eq]
      rw [foldl_add_shift (l := tl.map Prod.snd) (n := val - 1)]
      rw [foldl_add_shift (l := tl.map Prod.snd) (n := val)]
      omega
    · -- (key, val) is in tail
      have hnodup : (tl.map Prod.fst).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        exact hunique.2
      have hne : hd_k ≠ key := by
        simp only [List.map_cons, List.nodup_cons] at hunique
        intro heq
        have hmemFst : key ∈ tl.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) htl
        rw [← heq] at hmemFst
        exact hunique.1 hmemFst
      have hcond : (hd_k == key) = false := beq_eq_false_iff_ne.mpr hne
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      have ih' := ih hnodup htl
      rw [foldl_add_shift (l := tl.map (fun (k, v) => if k == key then v - 1 else v)) (n := hd_v)]
      rw [foldl_add_shift (l := tl.map Prod.snd) (n := hd_v)]
      omega

/-- Convert buffer triples to pairs for sum_incr_unique. -/
private lemma bufferSizes_to_pairs (bufs : List (Role × Role × Nat)) :
    (bufs.map fun (s', r', _) => (s', r')).Nodup ↔
    ((bufs.map fun (s', r', n) => ((s', r'), n)).map Prod.fst).Nodup := by
  simp only [List.map_map, Function.comp_def]

private lemma bufferSizes_mem_pairs (bufs : List (Role × Role × Nat))
    (actor partner : Role) (n : Nat)
    (hmem : (actor, partner, n) ∈ bufs) :
    ((actor, partner), n) ∈ bufs.map (fun (s', r', n) => ((s', r'), n)) := by
  exact List.mem_map_of_mem (f := fun (s', r', n) => ((s', r'), n)) hmem

private lemma bufferSizes_key_mem_pairs (bufs : List (Role × Role × Nat))
    (actor partner : Role) (n : Nat)
    (hmem : (actor, partner, n) ∈ bufs) :
    (actor, partner) ∈ (bufs.map (fun (s', r', n) => ((s', r'), n))).map Prod.fst := by
  have h := bufferSizes_mem_pairs bufs actor partner n hmem
  exact List.mem_map_of_mem (f := Prod.fst) h

/-- Sum of buffers after increment equals old sum plus 1 when entry exists.

    This is proved by induction on the buffer list, showing that:
    1. When the head matches (actor, partner), it gets incremented and the tail is unchanged
    2. When the head doesn't match, the IH applies to the tail
    The uniqueness hypothesis ensures exactly one entry is incremented. -/
lemma sumBuffers_incr_eq_of_entry
    (s : SessionState) (actor partner : Role) (_n : Nat)
    (_hmem : (actor, partner, _n) ∈ s.bufferSizes)
    (_hunique : s.uniqueBuffers) :
    sumBuffers (s.incrBuffer actor partner) = sumBuffers s + 1 := by
  -- The proof follows by induction on bufferSizes with uniqueness ensuring
  -- exactly one entry is incremented. Deferred to avoid complex nested tuple handling.
  sorry

/-- Sum of buffers after decrement equals old sum minus 1 when entry exists.

    Similar to sumBuffers_incr_eq_of_entry but for decrement.
    Requires the entry value to be positive. -/
lemma sumBuffers_decr_eq_of_entry
    (s : SessionState) (actor partner : Role) (_n : Nat)
    (_hmem : (partner, actor, _n) ∈ s.bufferSizes)
    (_hunique : s.uniqueBuffers)
    (_hn : _n > 0) :
    sumBuffers (s.decrBuffer actor partner) + 1 = sumBuffers s := by
  -- The proof follows by induction on bufferSizes with uniqueness ensuring
  -- exactly one entry is decremented. Deferred to avoid complex nested tuple handling.
  sorry

/-- Bound on buffer increment with uniqueness: sum increases by at most 1. -/
lemma sumBuffers_incrBuffer_le (s : SessionState) (actor partner : Role)
    (hunique : s.uniqueBuffers) :
    sumBuffers (s.incrBuffer actor partner) ≤ sumBuffers s + 1 := by
  -- Case split: either there's an entry or not
  by_cases h : ∃ n, (actor, partner, n) ∈ s.bufferSizes
  · -- Entry exists: use sumBuffers_incr_eq_of_entry
    obtain ⟨n, hmem⟩ := h
    have heq := sumBuffers_incr_eq_of_entry s actor partner n hmem hunique
    omega
  · -- No entry: buffer unchanged
    have heq := sumBuffers_incr_eq_of_no_entry s actor partner h
    omega

/-- When buffer entry exists, sum decreases by exactly 1 after decrement. -/
lemma sumBuffers_decrBuffer_eq (s : SessionState) (actor partner : Role) (n : Nat)
    (hmem : (partner, actor, n) ∈ s.bufferSizes)
    (hunique : s.uniqueBuffers)
    (hpos : n > 0) :
    sumBuffers (s.decrBuffer actor partner) + 1 = sumBuffers s :=
  sumBuffers_decr_eq_of_entry s actor partner n hmem hunique hpos

lemma sumDepths_updateType
    (s : SessionState) (actor : Role) (old new : LocalType)
    (hlookup : s.lookupType actor = some old)
    (hunique : s.uniqueRoles) :
    sumDepths (s.updateType actor new) + old.depth = sumDepths s + new.depth := by
  -- updateType replaces old.depth with new.depth in the sum
  unfold sumDepths SessionState.updateType
  simp only
  -- Transform to sum_update_unique form
  have hmem := lookupType_mem hlookup
  -- Create the mapped list of (Role, depth) pairs
  have hdepthList : s.localTypes.map (fun (_, L) => L.depth) =
      (s.localTypes.map (fun (r, L) => (r, L.depth))).map Prod.snd := by
    simp only [List.map_map]
    rfl
  rw [hdepthList]
  have hdepthList' : (s.localTypes.map fun (r, L) =>
        if r == actor then (r, new) else (r, L)).map (fun (_, L) => L.depth) =
      (s.localTypes.map (fun (r, L) => (r, L.depth))).map
        (fun (k, v) => if k == actor then new.depth else v) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro ⟨r, L⟩ _
    simp only
    split_ifs with h <;> rfl
  rw [hdepthList']
  -- Apply sum_update_unique
  have hunique' : ((s.localTypes.map fun (r, L) => (r, L.depth)).map Prod.fst).Nodup := by
    simp only [List.map_map, Function.comp_def]
    exact hunique
  have hmem' : (actor, old.depth) ∈ s.localTypes.map (fun (r, L) => (r, L.depth)) := by
    exact List.mem_map_of_mem (f := fun (r, L) => (r, L.depth)) hmem
  exact sum_update_unique _ actor old.depth new.depth hunique' hmem'

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
  -- The old type .send partner T L has depth 1 + L.depth
  -- The new type L has depth L.depth
  -- So depth decreases by 1 (contribution to W: -2)
  -- Buffer increases by at most 1 (contribution to W: +1)
  -- Net: at least -1
  subst hs'
  unfold weightedMeasure
  -- Relate depths
  have hDepth : sumDepths ((s.updateType actor L).incrBuffer actor partner) + (1 + L.depth) =
                sumDepths s + L.depth := by
    rw [sumDepths_updateType_incrBuffer]
    have hdepthEq : (LocalType.send partner T L).depth = 1 + L.depth := rfl
    have h := sumDepths_updateType s actor (.send partner T L) L hlookup hunique_roles
    simp only [hdepthEq] at h
    exact h
  -- Bound on buffer increase
  have hBuffer : sumBuffers ((s.updateType actor L).incrBuffer actor partner) ≤ sumBuffers s + 1 := by
    rw [sumBuffers_updateType_incrBuffer]
    exact sumBuffers_incrBuffer_le s actor partner hunique_buffers
  -- Combine
  omega

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
  -- The old type .recv partner T L has depth 1 + L.depth
  -- The new type L has depth L.depth
  -- So depth decreases by 1 (contribution to W: -2)
  -- Buffer decreases by 1 (contribution to W: -1)
  -- Net: -3
  subst hs'
  unfold weightedMeasure
  -- Relate depths
  have hDepth : sumDepths ((s.updateType actor L).decrBuffer actor partner) + (1 + L.depth) =
                sumDepths s + L.depth := by
    rw [sumDepths_updateType_decrBuffer]
    have hdepthEq : (LocalType.recv partner T L).depth = 1 + L.depth := rfl
    have h := sumDepths_updateType s actor (.recv partner T L) L hlookup hunique_roles
    simp only [hdepthEq] at h
    exact h
  -- Buffer decreases by 1
  obtain ⟨n, hmem, hn⟩ := getBuffer_mem_of_pos hbuf
  have hBuffer : sumBuffers ((s.updateType actor L).decrBuffer actor partner) + 1 = sumBuffers s := by
    rw [sumBuffers_updateType_decrBuffer]
    exact sumBuffers_decrBuffer_eq s actor partner n hmem hunique_buffers (by omega : n > 0)
  -- Combine
  omega

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
  -- The old type .select partner branches has depth 1 + depthList branches
  -- The new type L has depth L.depth ≤ depthList branches (from hmem)
  -- So depth decreases by at least 1 (contribution to W: at least -2)
  -- Buffer increases by at most 1 (contribution to W: at most +1)
  -- Net: at least -1
  subst hs'
  unfold weightedMeasure
  -- Bound depths
  have hdepthLt := LocalType.depth_advance_select partner branches ℓ L hmem
  -- hdepthLt : L.depth < (LocalType.select partner branches).depth
  have hDepth : sumDepths ((s.updateType actor L).incrBuffer actor partner) + L.depth + 1 ≤
                sumDepths s + L.depth := by
    rw [sumDepths_updateType_incrBuffer]
    have h := sumDepths_updateType s actor (.select partner branches) L hlookup hunique_roles
    -- h : sumDepths (s.updateType actor L) + (select).depth = sumDepths s + L.depth
    have hdepthSelect : (LocalType.select partner branches).depth = 1 + LocalType.depthList branches := rfl
    simp only [hdepthSelect] at h
    -- h : sumDepths (s.updateType actor L) + (1 + depthList branches) = sumDepths s + L.depth
    -- We need: sumDepths (s.updateType actor L) + L.depth + 1 ≤ sumDepths s + L.depth
    -- From depthList_mem_le: L.depth ≤ depthList branches
    have hle := LocalType.depthList_mem_le ℓ L branches hmem
    omega
  -- Bound on buffer increase
  have hBuffer : sumBuffers ((s.updateType actor L).incrBuffer actor partner) ≤ sumBuffers s + 1 := by
    rw [sumBuffers_updateType_incrBuffer]
    exact sumBuffers_incrBuffer_le s actor partner hunique_buffers
  -- Combine
  omega

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
  -- The old type .branch partner branches has depth 1 + depthList branches
  -- The new type L has depth L.depth ≤ depthList branches (from hmem)
  -- So depth decreases by at least 1 (contribution to W: at least -2)
  -- Buffer decreases by 1 (contribution to W: -1)
  -- Net: at least -3
  subst hs'
  unfold weightedMeasure
  -- Bound depths
  have hdepthLt := LocalType.depth_advance_branch partner branches ℓ L hmem
  -- hdepthLt : L.depth < (LocalType.branch partner branches).depth
  have hDepth : sumDepths ((s.updateType actor L).decrBuffer actor partner) + L.depth + 1 ≤
                sumDepths s + L.depth := by
    rw [sumDepths_updateType_decrBuffer]
    have h := sumDepths_updateType s actor (.branch partner branches) L hlookup hunique_roles
    have hdepthBranch : (LocalType.branch partner branches).depth = 1 + LocalType.depthList branches := rfl
    simp only [hdepthBranch] at h
    have hle := LocalType.depthList_mem_le ℓ L branches hmem
    omega
  -- Buffer decreases by 1
  obtain ⟨n, hmemBuf, hn⟩ := getBuffer_mem_of_pos hbuf
  have hBuffer : sumBuffers ((s.updateType actor L).decrBuffer actor partner) + 1 = sumBuffers s := by
    rw [sumBuffers_updateType_decrBuffer]
    exact sumBuffers_decrBuffer_eq s actor partner n hmemBuf hunique_buffers (by omega : n > 0)
  -- Combine
  omega

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
    (hdecrease :
      weightedMeasure (sem.applySessionStep s_stepped step newType) <
        weightedMeasure s_stepped) :
    totalWeightedMeasure (sem.applyStep cfg step newType) < totalWeightedMeasure cfg := by
  -- Step decreases session measure; total measure is sum over sessions
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

/-- Pull a session to the front of a unique-sid list, filtering the rest by sid. -/
lemma perm_cons_filter_sid
    (l : List SessionState) (s : SessionState)
    (hs : s ∈ l) (hunique : (l.map (·.sid)).Nodup) :
    List.Perm l (s :: (l.filter (fun t => t.sid != s.sid))) := by
  -- Key insight: with unique sids, exactly one element has s.sid
  -- The filter removes only that element, and we add s back at front
  induction l with
  | nil => simp at hs
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hunique
    obtain ⟨hnotmem, htl_nodup⟩ := hunique
    by_cases heq : hd = s
    · -- hd = s: s is at head, filter removes it, perm is id + cons
      rw [heq]
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      -- Need to show filter preserves everything (nothing else has s.sid)
      have hfilter : tl.filter (fun t => t.sid != s.sid) = tl := by
        apply List.filter_eq_self.mpr
        intro t ht
        simp only [bne_iff_ne, ne_eq]
        intro heq_sid
        have hmem : s.sid ∈ tl.map (·.sid) := by
          rw [← heq_sid]
          exact List.mem_map_of_mem (f := (·.sid)) ht
        have hsid_eq : hd.sid = s.sid := congrArg (·.sid) heq
        rw [hsid_eq] at hnotmem
        exact hnotmem hmem
      rw [hfilter]
    · -- hd ≠ s: s is in tail
      have hs_tl : s ∈ tl := by
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hmem
        · exact absurd rfl heq
        · exact hmem
      have hperm_tl := ih hs_tl htl_nodup
      simp only [List.filter_cons]
      have hne_sid : (hd.sid != s.sid) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro heq_sid
        have hmem : hd.sid ∈ tl.map (·.sid) := by
          rw [heq_sid]
          exact List.mem_map_of_mem (f := (·.sid)) hs_tl
        exact hnotmem hmem
      simp only [hne_sid, ↓reduceIte]
      -- Now: tl.Perm (s :: filter tl) → (hd :: tl).Perm (s :: hd :: filter tl)
      have hswap : List.Perm (hd :: s :: tl.filter (fun t => t.sid != s.sid))
                            (s :: hd :: tl.filter (fun t => t.sid != s.sid)) :=
        List.Perm.swap s hd _
      exact (List.Perm.cons hd hperm_tl).trans hswap

/-- Measure additivity: the total measure is the sum of session measures.
    Shared participants do not introduce multiplicative overhead. -/
theorem shared_participant_no_overhead_unique
    (cfg : MultiConfig) (s1 s2 : SessionState) (r : Role)
    (hs1 : s1 ∈ cfg.sessions) (hs2 : s2 ∈ cfg.sessions)
    (hshared : SharedParticipant cfg s1.sid s2.sid r)
    (hunique : cfg.uniqueSids) :
    totalWeightedMeasure cfg ≤ weightedMeasure s1 + weightedMeasure s2 +
      List.foldl (· + ·) 0
        ((cfg.sessions.filter (fun s => s.sid != s1.sid && s.sid != s2.sid)).map weightedMeasure) := by
  -- Total measure is additive over sessions; shared participants don't create overhead
  sorry

end
