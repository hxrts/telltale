
import Runtime.Proofs.WeightedMeasure.Core

/-! # Runtime.Proofs.WeightedMeasure.StepDecrease

Per-step weighted-measure decrease lemmas.
-/

/-
The Problem. To derive a global bound we first need step-local decrease lemmas
for all communication forms.

Solution Structure. Proves send/recv/select/branch decrease lemmas.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

-- Lookup/Buffer Membership Helpers

-- # Type Lookup Membership

lemma find?_mem_aux {r : Role} {L : LocalType} (types : List (Role × LocalType)) :
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
      simp only [hEq]
      intro hL
      have hRole : hd.1 = r := beq_iff_eq.mp hEq
      have hType : hd.2 = L := Option.some.inj hL
      have hPair : hd = (r, L) := Prod.ext hRole hType
      rw [hPair]
      exact List.Mem.head tl
    · -- Head doesn't match
      simp only [hEq]
      intro hFind
      exact List.Mem.tail hd (ih hFind)

lemma lookupType_mem {s : SessionState} {r : Role} {L : LocalType}
    (h : s.lookupType r = some L) : (r, L) ∈ s.localTypes := by
  unfold SessionState.lookupType at h
  exact find?_mem_aux s.localTypes h

-- # Buffer Lookup Membership

lemma getBuffer_mem_aux {sender receiver : Role}
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
      simp only [hEq]
      intro _
/- ## Structured Block 2 -/
      simp only [Bool.and_eq_true, beq_iff_eq] at hEq
      have ⟨hSender, hRecv⟩ := hEq
      have heq : hd = (sender, receiver, hd.2.2) := by
        cases hd with | mk fst snd =>
        cases snd with | mk fst' snd' =>
        simp only at hSender hRecv
        simp [hSender, hRecv]
      exact ⟨hd.2.2, by rw [heq]; exact List.Mem.head _, rfl⟩
    · -- Head doesn't match
      simp only [hEq]
      intro hFind
      obtain ⟨n, hmem, heq⟩ := ih hFind
      exact ⟨n, List.Mem.tail _ hmem, heq⟩

lemma getBuffer_mem_of_pos {s : SessionState} {sender receiver : Role}
    (hpos : s.getBuffer sender receiver > 0) :
    ∃ n, (sender, receiver, n) ∈ s.bufferSizes ∧ n = s.getBuffer sender receiver := by
  unfold SessionState.getBuffer at hpos ⊢
  exact getBuffer_mem_aux s.bufferSizes hpos

-- # Buffer Sum Stability Without Matching Entry

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

-- Unique-Key Sum Update Lemmas

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

    -- # `sum_incr_unique`: head-key case split

/- ## Structured Block 3 -/
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

    -- # `sum_incr_unique`: tail recursion case

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

-- Unique-Key Decrement Lemmas

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
/- ## Structured Block 4 -/
    obtain ⟨hd_k, hd_v⟩ := hd
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    rcases List.mem_cons.mp hmem with heq | htl

    -- # `sum_decr_unique`: matching head case

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

    -- # `sum_decr_unique`: tail membership case

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

-- Buffer-Pair Translation Helpers

/-- Convert buffer triples to pairs for sum_incr_unique. -/
lemma bufferSizes_to_pairs (bufs : List (Role × Role × Nat)) :
    (bufs.map fun (s', r', _) => (s', r')).Nodup ↔
    ((bufs.map fun (s', r', n) => ((s', r'), n)).map Prod.fst).Nodup := by
  simp only [List.map_map, Function.comp_def]

lemma bufferSizes_mem_pairs (bufs : List (Role × Role × Nat))
/- ## Structured Block 5 -/
    (actor partner : Role) (n : Nat)
    (hmem : (actor, partner, n) ∈ bufs) :
    ((actor, partner), n) ∈ bufs.map (fun (s', r', n) => ((s', r'), n)) := by
  exact List.mem_map_of_mem (f := fun (s', r', n) => ((s', r'), n)) hmem

lemma bufferSizes_key_mem_pairs (bufs : List (Role × Role × Nat))
    (actor partner : Role) (n : Nat)
    (hmem : (actor, partner, n) ∈ bufs) :
    (actor, partner) ∈ (bufs.map (fun (s', r', n) => ((s', r'), n))).map Prod.fst := by
  have h := bufferSizes_mem_pairs bufs actor partner n hmem
  exact List.mem_map_of_mem (f := Prod.fst) h

-- Session Buffer Increment/Decrement Equalities

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
  -- Re-express buffer triples as key/value pairs keyed by (sender, receiver).
  let pairs : List ((Role × Role) × Nat) :=
    s.bufferSizes.map (fun (s', r', n) => ((s', r'), n))
  have hunique_pairs : (pairs.map Prod.fst).Nodup := by
    dsimp [pairs]
    exact (bufferSizes_to_pairs s.bufferSizes).1 _hunique
  have hkey_mem : (actor, partner) ∈ pairs.map Prod.fst := by
    dsimp [pairs]
    exact bufferSizes_key_mem_pairs s.bufferSizes actor partner _n _hmem
  have hsum_pairs :
      (pairs.map (fun (k, v) => if k == (actor, partner) then v + 1 else v)).foldl (· + ·) 0 =
      (pairs.map Prod.snd).foldl (· + ·) 0 + 1 := by
    simpa using (sum_incr_unique pairs (actor, partner) hunique_pairs hkey_mem)
  -- Translate back to the triple-based buffer representation.
  have hleft :
      sumBuffers (s.incrBuffer actor partner) =
        (pairs.map (fun (k, v) => if k == (actor, partner) then v + 1 else v)).foldl (· + ·) 0 := by
    unfold sumBuffers SessionState.incrBuffer
    simp only [pairs, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro x hx
    rcases x with ⟨s', r', n⟩
    by_cases hsr : s' = actor ∧ r' = partner
    · simp [hsr]
    · simp [hsr]
  have hright : sumBuffers s = (pairs.map Prod.snd).foldl (· + ·) 0 := by
    unfold sumBuffers
    simp [pairs, List.map_map, Function.comp_def]
  rw [hleft, hright]
  exact hsum_pairs

-- Derived Buffer/Depth Bounds

/-- Sum of buffers after decrement equals old sum minus 1 when entry exists.

    Similar to sumBuffers_incr_eq_of_entry but for decrement.
    Requires the entry value to be positive. -/
lemma sumBuffers_decr_eq_of_entry
    (s : SessionState) (actor partner : Role) (_n : Nat)
    (_hmem : (partner, actor, _n) ∈ s.bufferSizes)
    (_hunique : s.uniqueBuffers)
    (_hn : _n > 0) :
    sumBuffers (s.decrBuffer actor partner) + 1 = sumBuffers s := by
  -- Re-express buffer triples as key/value pairs keyed by (sender, receiver).
/- ## Structured Block 6 -/
  let pairs : List ((Role × Role) × Nat) :=
    s.bufferSizes.map (fun (s', r', n) => ((s', r'), n))
  have hunique_pairs : (pairs.map Prod.fst).Nodup := by
    dsimp [pairs]
    exact (bufferSizes_to_pairs s.bufferSizes).1 _hunique
  have hmem_pairs : ((partner, actor), _n) ∈ pairs := by
    dsimp [pairs]
    exact bufferSizes_mem_pairs s.bufferSizes partner actor _n _hmem
  have hsum_pairs :
      (pairs.map (fun (k, v) => if k == (partner, actor) then v - 1 else v)).foldl (· + ·) 0 + 1 =
      (pairs.map Prod.snd).foldl (· + ·) 0 := by
    simpa using (sum_decr_unique pairs (partner, actor) _n hunique_pairs hmem_pairs _hn)
  -- Translate back to the triple-based buffer representation.
  have hleft :
      sumBuffers (s.decrBuffer actor partner) + 1 =
        (pairs.map (fun (k, v) => if k == (partner, actor) then v - 1 else v)).foldl (· + ·) 0 + 1 := by
    unfold sumBuffers SessionState.decrBuffer
    simp only [pairs, List.map_map, Function.comp_def]
    congr 1
    congr 1
    apply List.map_congr_left
    intro x hx
    rcases x with ⟨s', r', n⟩
    by_cases hsr : s' = partner ∧ r' = actor
    · simp [hsr]
    · simp [hsr]
  have hright : sumBuffers s = (pairs.map Prod.snd).foldl (· + ·) 0 := by
    unfold sumBuffers
    simp [pairs, List.map_map, Function.comp_def]
  rw [hleft, hright]
  exact hsum_pairs

-- # Buffer Delta Bounds

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

-- # Type-Depth Rewrite Under Update

lemma sumDepths_updateType
    (s : SessionState) (actor : Role) (old new : LocalType)
    (hlookup : s.lookupType actor = some old)
/- ## Structured Block 7 -/
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

end
