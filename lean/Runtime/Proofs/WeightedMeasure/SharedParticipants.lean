import Runtime.Proofs.WeightedMeasure.TotalBound

/-! # Runtime.Proofs.WeightedMeasure.SharedParticipants

Shared-participant decomposition and no-overhead theorem.
-/

/-
The Problem. Multi-session overlap requires a final decomposition theorem to
bound interaction overhead.

Solution Structure. Defines shared-participant helpers and proves the final
no-overhead theorem.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

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
  -- The total measure is exactly equal to the decomposition, so ≤ holds
  -- Key insight: with unique sids, s1 and s2 are distinct elements, and the
  -- filter captures everything else. Sum is invariant under this decomposition.
  have hne : s1.sid ≠ s2.sid := hshared.2.2
  -- Pull s1 to front
  have hperm1 := perm_cons_filter_sid cfg.sessions s1 hs1 hunique
  -- The filtered list still contains s2 (since s2.sid ≠ s1.sid)
  have hs2_in_filter : s2 ∈ cfg.sessions.filter (fun t => t.sid != s1.sid) := by
    simp only [List.mem_filter, bne_iff_ne, ne_eq]
    exact ⟨hs2, hne.symm⟩
  -- Uniqueness of sids in the filtered list (sublist preserves nodup)
  have hunique_filter : (cfg.sessions.filter (fun t => t.sid != s1.sid)).map (·.sid) |>.Nodup := by
    have hsub : List.Sublist (cfg.sessions.filter (fun t => t.sid != s1.sid)) cfg.sessions :=
      List.filter_sublist
    exact List.Nodup.sublist (List.Sublist.map (·.sid) hsub) hunique
  -- Pull s2 to front of filtered list
  have hperm2 := perm_cons_filter_sid
    (cfg.sessions.filter (fun t => t.sid != s1.sid)) s2 hs2_in_filter hunique_filter
  -- The double filter is equivalent to filtering both conditions
  have hfilter_eq : (cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid) =
      cfg.sessions.filter (fun s => s.sid != s1.sid && s.sid != s2.sid) := by
    simp only [List.filter_filter, Bool.and_comm]
  -- Decompose total measure by pulling s1, then s2, to the front.
  have hsum1 :
      totalWeightedMeasure cfg =
        weightedMeasure s1 +
          List.foldl (· + ·) 0 ((cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure) := by
    unfold totalWeightedMeasure
    have hpermNat :
        List.Perm (cfg.sessions.map weightedMeasure)
          ((s1 :: cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure) := by
      exact hperm1.map weightedMeasure
    have hsumEq :
        (cfg.sessions.map weightedMeasure).foldl (· + ·) 0 =
          ((s1 :: cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure).foldl (· + ·) 0 := by
      rw [foldl_add_eq_sum, foldl_add_eq_sum]
      exact hpermNat.sum_eq
    calc
      (cfg.sessions.map weightedMeasure).foldl (· + ·) 0
          = ((s1 :: cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure).foldl (· + ·) 0 := hsumEq
      _ = weightedMeasure s1 +
            List.foldl (· + ·) 0 ((cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure) := by
            rw [List.map_cons, List.foldl_cons, Nat.zero_add]
            rw [foldl_add_shift (l := (cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure)
              (n := weightedMeasure s1)]
  have hsum2 :
      List.foldl (· + ·) 0 ((cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure) =
        weightedMeasure s2 +
          List.foldl (· + ·) 0
            ((((cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid)).map weightedMeasure)) := by
    have hpermNat :
        List.Perm
          ((cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure)
          ((s2 :: (cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid)).map weightedMeasure) := by
      exact hperm2.map weightedMeasure
    have hsumEq :
        ((cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure).foldl (· + ·) 0 =
          ((s2 :: (cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid)).map weightedMeasure).foldl (· + ·) 0 := by
      rw [foldl_add_eq_sum, foldl_add_eq_sum]
      exact hpermNat.sum_eq
    calc
      ((cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure).foldl (· + ·) 0
          = ((s2 :: (cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid)).map weightedMeasure).foldl (· + ·) 0 := hsumEq
      _ = weightedMeasure s2 +
            List.foldl (· + ·) 0
              ((((cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid)).map weightedMeasure)) := by
            rw [List.map_cons, List.foldl_cons, Nat.zero_add]
            rw [foldl_add_shift
              (l := ((cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid)).map weightedMeasure)
              (n := weightedMeasure s2)]
  have htotal_eq :
      totalWeightedMeasure cfg =
        weightedMeasure s1 + weightedMeasure s2 +
          List.foldl (· + ·) 0
            ((cfg.sessions.filter (fun s => s.sid != s1.sid && s.sid != s2.sid)).map weightedMeasure) := by
    calc
      totalWeightedMeasure cfg
          = weightedMeasure s1 +
              List.foldl (· + ·) 0 ((cfg.sessions.filter (fun t => t.sid != s1.sid)).map weightedMeasure) := hsum1
      _ = weightedMeasure s1 +
            (weightedMeasure s2 +
              List.foldl (· + ·) 0
                ((((cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid)).map weightedMeasure))) := by
              rw [hsum2]
      _ = weightedMeasure s1 + weightedMeasure s2 +
            List.foldl (· + ·) 0
              ((((cfg.sessions.filter (fun t => t.sid != s1.sid)).filter (fun t => t.sid != s2.sid)).map weightedMeasure)) := by
              omega
      _ = weightedMeasure s1 + weightedMeasure s2 +
            List.foldl (· + ·) 0
              ((cfg.sessions.filter (fun s => s.sid != s1.sid && s.sid != s2.sid)).map weightedMeasure) := by
              rw [hfilter_eq]
  exact le_of_eq htotal_eq


end
