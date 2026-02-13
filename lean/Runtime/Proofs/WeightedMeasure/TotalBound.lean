import Runtime.Proofs.WeightedMeasure.StepDecrease

/-! # Runtime.Proofs.WeightedMeasure.TotalBound

Total-measure decrease and productive-step bound.
-/

/-
The Problem. Local decrease lemmas must lift to whole-configuration bounds.

Solution Structure. Lifts per-step decreases to total measure and bounded trace
length statements.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Local Session Step Decrease Lemmas -/

/-! ### Send -/

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

/-! ### Receive -/

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

/-! ### Select -/

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

/-! ### Branch -/

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

/-! ### Fold-Sum Comparison Helpers -/

/-- Sum is monotone: pointwise ≤ implies sum ≤. -/
lemma sum_le_of_pointwise_le {α : Type*} (l : List α) (f g : α → Nat)
    (hle : ∀ y ∈ l, f y ≤ g y) :
    (l.map f).foldl (· + ·) 0 ≤ (l.map g).foldl (· + ·) 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    rw [foldl_add_shift (l := tl.map f) (n := f hd)]
    rw [foldl_add_shift (l := tl.map g) (n := g hd)]
    have h1 : f hd ≤ g hd := hle hd (by simp)
    have h2 := ih (fun y hy => hle y (List.mem_cons.mpr (Or.inr hy)))
    omega

/-! ### Strict Fold-Sum Decrease -/

/-- Sum decreases when one element strictly decreases and others don't increase. -/
lemma sum_lt_of_one_lt {α : Type*} (l : List α) (f g : α → Nat)
    (x : α) (hx : x ∈ l)
    (hlt : f x < g x)
    (hle : ∀ y ∈ l, f y ≤ g y) :
    (l.map f).foldl (· + ·) 0 < (l.map g).foldl (· + ·) 0 := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    rw [foldl_add_shift (l := tl.map f) (n := f hd)]
    rw [foldl_add_shift (l := tl.map g) (n := g hd)]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | htl
    · -- x = hd: the strict decrease is at the head
      have h2 := sum_le_of_pointwise_le tl f g
        (fun y hy => hle y (List.mem_cons.mpr (Or.inr hy)))
      omega
    · -- x ∈ tl: use inductive hypothesis
      have h1 : f hd ≤ g hd := hle hd (by simp)
      have h2 := ih htl (fun y hy => hle y (List.mem_cons.mpr (Or.inr hy)))
      omega

/-! ### Unique-Key Equality from Nodup Map -/

/-- If a list has unique images under f and x, y are in the list with f x = f y, then x = y. -/
lemma eq_of_mem_of_eq_of_nodup_map {α β : Type*} [DecidableEq β]
    (l : List α) (f : α → β) (x y : α)
    (hx : x ∈ l) (hy : y ∈ l)
    (hnodup : (l.map f).Nodup)
    (heq : f x = f y) : x = y := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotmem, htl_nodup⟩ := hnodup
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx_tl
    · -- x = hd
      rcases hy with rfl | hy_tl
      · rfl
      · -- y ∈ tl, but f hd = f y, so f y ∈ tl.map f, contradicting hnotmem
        exfalso
        have hmem : f y ∈ tl.map f := List.mem_map_of_mem (f := f) hy_tl
        rw [← heq] at hmem
        exact hnotmem hmem
    · -- x ∈ tl
      rcases hy with rfl | hy_tl
      · -- y = hd, x ∈ tl, f x = f hd
        exfalso
        have hmem : f x ∈ tl.map f := List.mem_map_of_mem (f := f) hx_tl
        rw [heq] at hmem
        exact hnotmem hmem
      · -- Both in tail
        exact ih hx_tl hy_tl htl_nodup

/-! ### Configuration-Level Decrease Lift -/

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
  unfold totalWeightedMeasure
  rw [sem.applyStep_map]
  -- Define the stepped-session weighted measure function
  let f := fun s : SessionState =>
    weightedMeasure (if s.sid == step.sid then sem.applySessionStep s step newType else s)
  let g := weightedMeasure
  -- Rewrite the mapped sum using f
  have hmap : (cfg.sessions.map (fun s =>
      if s.sid == step.sid then sem.applySessionStep s step newType else s)).map weightedMeasure =
      cfg.sessions.map f := by simp only [List.map_map]; rfl
  rw [hmap]
  -- Apply sum_lt_of_one_lt with s_stepped
  apply sum_lt_of_one_lt cfg.sessions f g s_stepped hs
  · -- f s_stepped < g s_stepped
    simp only [f, g]
    have heq : (s_stepped.sid == step.sid) = true := by
      simp only [beq_iff_eq]
      exact hsid
    simp only [heq, ↓reduceIte]
    exact hdecrease
  · -- ∀ y ∈ cfg.sessions, f y ≤ g y
    intro y hy
    simp only [f, g]
    by_cases heq : y.sid == step.sid
    · -- y.sid = step.sid: y must equal s_stepped by uniqueness
      simp only [heq, ↓reduceIte]
      have hsid_eq : y.sid = step.sid := beq_iff_eq.mp heq
      have hsid_s : s_stepped.sid = step.sid := hsid
      have hsid_y : y.sid = s_stepped.sid := by simpa [hsid_s] using hsid_eq
      have hsame : y = s_stepped := eq_of_mem_of_eq_of_nodup_map
        cfg.sessions (·.sid) y s_stepped hy hs hunique_sids (by simpa using hsid_y)
      rw [hsame]
      exact Nat.le_of_lt hdecrease
    · -- y.sid ≠ step.sid: measure unchanged
      simp only [Bool.not_eq_true] at heq
      simp only [heq, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]


end
