import Telltale.Coinductive.BisimDecidable.Part2

set_option linter.dupNamespace false

/-! # BisimDecidable Part 3

Reachable pairs, termination measure, soundness, and completeness.
-/

open Classical

namespace Telltale.Coinductive
/-! ## Reachable Pairs -/

/-- Local decidable equality for visited membership. -/
noncomputable local instance : DecidableEq (LocalTypeC × LocalTypeC) := by
  -- Use classical choice to decide equality on pairs.
  classical
  infer_instance

/-- The set of pairs reachable from (a, b) via child relation. -/
def ReachablePairs (a b : LocalTypeC) : Set (LocalTypeC × LocalTypeC) :=
  { p | p.1 ∈ Reachable a ∧ p.2 ∈ Reachable b }

/-- For regular types, the reachable pairs are finite. -/
lemma reachablePairs_finite {a b : LocalTypeC} (ha : Regular a) (hb : Regular b) :
    Set.Finite (ReachablePairs a b) := by
  have hprod : Set.Finite (Reachable a ×ˢ Reachable b) := Set.Finite.prod ha hb
  exact Set.Finite.subset hprod (fun ⟨x, y⟩ ⟨hx, hy⟩ => ⟨hx, hy⟩)

/-- Convert finite reachable pairs to Finset. -/
noncomputable def reachablePairsFinset (a b : LocalTypeC) (ha : Regular a) (hb : Regular b) :
    Finset (LocalTypeC × LocalTypeC) :=
  (reachablePairs_finite ha hb).toFinset

/-! ## Measure for Termination -/

/-- The measure: size of unvisited pairs from the reachable set. -/
noncomputable def pairMeasure (all : Finset (LocalTypeC × LocalTypeC))
    (visited : Finset (LocalTypeC × LocalTypeC)) : Nat :=
  all.card - visited.card

/-- Measure decreases when we visit a new pair that's in the reachable set. -/
lemma pairMeasure_lt {all visited : Finset (LocalTypeC × LocalTypeC)}
    {p : LocalTypeC × LocalTypeC}
    (h_in_all : p ∈ all) (h_not_visited : p ∉ visited) (h_sub : visited ⊆ all) :
    pairMeasure all (insert p visited) < pairMeasure all visited := by
  unfold pairMeasure
  have h_card : (insert p visited).card = visited.card + 1 :=
    Finset.card_insert_of_notMem h_not_visited
  have h_lt : visited.card < all.card := by
    have hsub : visited ⊂ all := Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, by
      intro heq
      rw [heq] at h_not_visited
      exact h_not_visited h_in_all⟩
    exact Finset.card_lt_card hsub
  omega

/-! ## Bisimulation Functions -/

/-- Compute sufficient fuel for bisim based on reachable pairs. -/
noncomputable def bisimFuel (a b : LocalTypeC) (ha : Regular a) (hb : Regular b) : Nat :=
  (reachablePairsFinset a b ha hb).card + 1

/-- Main bisimulation check for regular types. -/
noncomputable def bisim (a b : LocalTypeC) (ha : Regular a) (hb : Regular b) (bound : Nat) : Bool :=
  bisimAux (bisimFuel a b ha hb) bound ∅ (a, b)

/-! ## Soundness via Paco Coinduction -/

/-- Helper: obsMatch true with end kind implies both unfold to end. -/
lemma obsMatch_end_implies_UnfoldsToEndC {bound : Nat} {a b : LocalTypeC}
    (hobs : obsMatch bound a b = true)
    (hk : obsKindOf (fullUnfoldN bound a) = some .obs_end) :
    UnfoldsToEndC a ∧ UnfoldsToEndC b := by
  have ⟨k, hk1, hk2⟩ := obsMatch_true_implies_same_kind hobs
  have hhead_a := obsKindOf_end_iff.mp hk
  -- k = .obs_end since hk1 and hk both give obsKindOf (fullUnfoldN bound a)
  have heq : k = .obs_end := by simp_all
  rw [heq] at hk2
  have hhead_b := obsKindOf_end_iff.mp hk2
  constructor
  · exact ⟨fullUnfoldN bound a, fullUnfoldN_UnfoldsToC bound a, hhead_a⟩
  · exact ⟨fullUnfoldN bound b, fullUnfoldN_UnfoldsToC bound b, hhead_b⟩

/-- Helper: obsKindOf send implies CanSendC -/
lemma obsKindOf_send_implies_CanSendC {t : LocalTypeC} {p : String} {labels : List Label}
    (hk : obsKindOf t = some (.obs_send p labels)) :
    CanSendC t p (branchesOf t) := by
  have hhead := obsKindOf_send_iff.mp hk
  exact ⟨t, labels, Relation.ReflTransGen.refl, hhead, rfl⟩

/-- Helper: obsKindOf recv implies CanRecvC -/
lemma obsKindOf_recv_implies_CanRecvC {t : LocalTypeC} {p : String} {labels : List Label}
    (hk : obsKindOf t = some (.obs_recv p labels)) :
    CanRecvC t p (branchesOf t) := by
  have hhead := obsKindOf_recv_iff.mp hk
  exact ⟨t, labels, Relation.ReflTransGen.refl, hhead, rfl⟩

/-- Helper: fullUnfoldN with send head gives CanSendC via unfolding -/
lemma fullUnfoldN_send_implies_CanSendC {bound : Nat} {t : LocalTypeC}
    {p : String} {labels : List Label}
    (hk : obsKindOf (fullUnfoldN bound t) = some (.obs_send p labels)) :
    CanSendC t p (branchesOf (fullUnfoldN bound t)) := by
  have hhead := obsKindOf_send_iff.mp hk
  exact ⟨fullUnfoldN bound t, labels, fullUnfoldN_UnfoldsToC bound t, hhead, rfl⟩

/-- Helper: fullUnfoldN with recv head gives CanRecvC via unfolding -/
lemma fullUnfoldN_recv_implies_CanRecvC {bound : Nat} {t : LocalTypeC}
    {p : String} {labels : List Label}
    (hk : obsKindOf (fullUnfoldN bound t) = some (.obs_recv p labels)) :
    CanRecvC t p (branchesOf (fullUnfoldN bound t)) := by
  have hhead := obsKindOf_recv_iff.mp hk
  exact ⟨fullUnfoldN bound t, labels, fullUnfoldN_UnfoldsToC bound t, hhead, rfl⟩

/-- obsMatch with send implies same participant and labels (needed for BranchesRelC).

    **Justification**: When obsMatch returns true for send types, the ObsKind equality
    implies same participant and labels. This is needed to construct CanSendC for both
    types with the same parameters.

    The proof unfolds obsMatch, obsKindOf, and uses the definitional equality of ObsKind.
    We defer this to focus on the main soundness theorem structure. -/
lemma obsMatch_send_implies_same_labels {bound : Nat} {a b : LocalTypeC}
    {p : String} {labels : List Label}
    (hobs : obsMatch bound a b = true)
    (hk : obsKindOf (fullUnfoldN bound a) = some (.obs_send p labels)) :
    obsKindOf (fullUnfoldN bound b) = some (.obs_send p labels) := by
  have ⟨k, hk1, hk2⟩ := obsMatch_true_implies_same_kind hobs
  have heq : k = .obs_send p labels := by simp_all
  rw [heq] at hk2
  exact hk2

/-- obsMatch with recv implies same participant and labels (needed for BranchesRelC). -/
lemma obsMatch_recv_implies_same_labels {bound : Nat} {a b : LocalTypeC}
    {p : String} {labels : List Label}
    (hobs : obsMatch bound a b = true)
    (hk : obsKindOf (fullUnfoldN bound a) = some (.obs_recv p labels)) :
    obsKindOf (fullUnfoldN bound b) = some (.obs_recv p labels) := by
  have ⟨k, hk1, hk2⟩ := obsMatch_true_implies_same_kind hobs
  have heq : k = .obs_recv p labels := by simp_all
  rw [heq] at hk2
  exact hk2

/-- Helper: obsMatch true with var kind implies both unfold to same var. -/
lemma obsMatch_var_implies_UnfoldsToVarC {bound : Nat} {a b : LocalTypeC} {v : String}
    (hobs : obsMatch bound a b = true)
    (hk : obsKindOf (fullUnfoldN bound a) = some (.obs_var v)) :
    UnfoldsToVarC a v ∧ UnfoldsToVarC b v := by
  have ⟨k, hk1, hk2⟩ := obsMatch_true_implies_same_kind hobs
  have hhead_a := obsKindOf_var_iff.mp hk
  -- k = .obs_var v since hk1 and hk both give obsKindOf (fullUnfoldN bound a)
  have heq : k = .obs_var v := by simp_all
  rw [heq] at hk2
  have hhead_b := obsKindOf_var_iff.mp hk2
  constructor
  · exact ⟨fullUnfoldN bound a, fullUnfoldN_UnfoldsToC bound a, hhead_a⟩
  · exact ⟨fullUnfoldN bound b, fullUnfoldN_UnfoldsToC bound b, hhead_b⟩

/-- EQ2C is a post-fixpoint of EQ2CMono.F (needed for BisimRel_postfixpoint). -/
lemma EQ2C_postfixpoint : ∀ a b, EQ2C a b → EQ2CMono.F EQ2C a b := by
  intro a b heq
  rcases heq with ⟨R, hR, hab⟩
  have hstep := hR a b hab
  rcases hstep with ⟨obs_a, obs_b, hrel⟩
  refine ⟨obs_a, obs_b, ?_⟩
  -- R ≤ EQ2C (any bisimulation is contained in the greatest)
  have hR_le : R ≤ EQ2C := fun x y hxy => ⟨R, hR, hxy⟩
  exact ObservableRelC_mono hR_le hrel

/-- BisimRel is a post-fixpoint of EQ2CMono.F (for paco coinduction).

    BisimRel = BisimRelCore ∨ EQ2C where:
    - BisimRelCore: pairs where bisimAux returns true
    - EQ2C: already known to be equivalent

    The proof handles these cases separately:
    - For EQ2C: use EQ2C_postfixpoint and monotonicity
    - For BisimRelCore: analyze bisimAux computation -/
theorem BisimRel_postfixpoint (bound : Nat) :
    ∀ a b, BisimRel bound a b → EQ2CMono.F (BisimRel bound ⊔ ⊥) a b := by
  intro a b h
  simp only [Paco.Rel.sup_bot]
  -- Case split on BisimRel disjunction
  rcases h with hcore | heq
  -- Case 1: EQ2C (including visited pairs via hvisited)
  case inr =>
    -- EQ2C is a post-fixpoint, lift to BisimRel by monotonicity
    have hstep := EQ2C_postfixpoint a b heq
    rcases hstep with ⟨obs_a, obs_b, hrel⟩
    refine ⟨obs_a, obs_b, ?_⟩
    -- EQ2C ⊆ BisimRel (right disjunct)
    have hEQ2C_le : EQ2C ≤ BisimRel bound := fun x y hxy => Or.inr hxy
    exact ObservableRelC_mono hEQ2C_le hrel
  -- Case 2: BisimRelCore (bisimAux returns true)
  case inl =>
    rcases hcore with ⟨fuel, visited, hvisited, hbisim⟩
    -- Case split on fuel
    match fuel with
    | 0 =>
        -- bisimAux 0 returns false, contradiction
        simp only [bisimAux] at hbisim
        exact absurd hbisim (by decide)
    | fuel' + 1 =>
        simp only [bisimAux] at hbisim
        by_cases hmem : (a, b) ∈ visited
        · -- Already visited: use hvisited to get EQ2C
          have heq' : EQ2C a b := hvisited (a, b) hmem
          -- Reduce to the EQ2C case
          have hstep := EQ2C_postfixpoint a b heq'
          rcases hstep with ⟨obs_a, obs_b, hrel⟩
          refine ⟨obs_a, obs_b, ?_⟩
          have hEQ2C_le : EQ2C ≤ BisimRel bound := fun x y hxy => Or.inr hxy
          exact ObservableRelC_mono hEQ2C_le hrel
        · -- Not visited: extract obsMatch and bisimAll
          simp only [hmem, ↓reduceIte] at hbisim
          have ⟨hobs, hchildren⟩ := Bool.and_eq_true_iff.mp hbisim
          have ⟨k, hk1, hk2⟩ := obsMatch_true_implies_same_kind hobs
          -- Case split on observable kind k
          match k with
          | .obs_end =>
              have ⟨ha, hb⟩ := obsMatch_end_implies_UnfoldsToEndC hobs hk1
              have obs_a := ObservableC.is_end ha
              have obs_b := ObservableC.is_end hb
              exact ⟨obs_a, obs_b, ObservableRelC.is_end ha hb⟩
          | .obs_var v =>
              have ⟨ha, hb⟩ := obsMatch_var_implies_UnfoldsToVarC hobs hk1
              have obs_a := ObservableC.is_var v ha
              have obs_b := ObservableC.is_var v hb
              exact ⟨obs_a, obs_b, ObservableRelC.is_var v ha hb⟩
          | .obs_send p labels =>
              -- For send, children come from bisimAll = true
              have hk_a := hk1
              have hk_b := obsMatch_send_implies_same_labels hobs hk1
              -- Extract CanSendC witnesses
              have ha_send := fullUnfoldN_send_implies_CanSendC hk_a
              have hb_send := fullUnfoldN_send_implies_CanSendC hk_b
              -- Get BranchesRelC from bisimAll
              have hbr := obsMatch_send_bisimAll_to_BranchesRelC hk_a hk_b hchildren hvisited
              -- Construct ObservableRelC
              have obs_a := ObservableC.is_send p (branchesOf (fullUnfoldN bound a)) ha_send
              have obs_b := ObservableC.is_send p (branchesOf (fullUnfoldN bound b)) hb_send
              exact ⟨obs_a, obs_b, ObservableRelC.is_send p _ _ ha_send hb_send hbr⟩
          | .obs_recv p labels =>
              -- Similar to send case
              have hk_a := hk1
              have hk_b := obsMatch_recv_implies_same_labels hobs hk1
              have ha_recv := fullUnfoldN_recv_implies_CanRecvC hk_a
              have hb_recv := fullUnfoldN_recv_implies_CanRecvC hk_b
              have hbr := obsMatch_recv_bisimAll_to_BranchesRelC hk_a hk_b hchildren hvisited
              have obs_a := ObservableC.is_recv p (branchesOf (fullUnfoldN bound a)) ha_recv
              have obs_b := ObservableC.is_recv p (branchesOf (fullUnfoldN bound b)) hb_recv
              exact ⟨obs_a, obs_b, ObservableRelC.is_recv p _ _ ha_recv hb_recv hbr⟩

/-- Key lemma: if bisimAux returns true, the pair is in EQ2C.

    Uses paco coinduction: BisimRel is a post-fixpoint of EQ2CMono.F,
    so by paco_coind, BisimRel ≤ EQ2C_paco = EQ2C. -/
theorem bisimAux_sound {fuel bound : Nat} {visited : Finset (LocalTypeC × LocalTypeC)}
    {p : LocalTypeC × LocalTypeC}
    (hvisited : ∀ q ∈ visited, EQ2C q.1 q.2)
    (hbisim : bisimAux fuel bound visited p = true) :
    EQ2C p.1 p.2 := by
  -- Show p is in BisimRel bound via BisimRelCore (left disjunct)
  have hCore : BisimRelCore bound p.1 p.2 := ⟨fuel, visited, hvisited, hbisim⟩
  have hBisim : BisimRel bound p.1 p.2 := Or.inl hCore
  -- Use paco coinduction: BisimRel_postfixpoint shows BisimRel is a post-fixpoint
  -- By paco_coind', BisimRel ≤ paco EQ2CMono ⊥ = EQ2C_paco
  have hle : BisimRel bound ≤ EQ2C_paco :=
    Paco.paco_coind' EQ2CMono ⊥ (BisimRel bound) (BisimRel_postfixpoint bound)
  -- Apply to get EQ2C_paco p.1 p.2
  have hPaco := hle p.1 p.2 hBisim
  -- Convert to EQ2C
  exact paco_to_EQ2C hPaco

/-- Soundness: bisim = true implies EQ2C. -/
theorem bisim_sound {a b : LocalTypeC} {ha : Regular a} {hb : Regular b} {bound : Nat}
    (hbisim : bisim a b ha hb bound = true) :
    EQ2C a b := by
  unfold bisim at hbisim
  exact bisimAux_sound (fun _ h => (Finset.notMem_empty _ h).elim) hbisim

/-! ## Maximum Unfolding Depth -/

/-- Maximum mu-nesting depth for a regular type (upper bound on unfoldings needed). -/
noncomputable def maxUnfoldDepth (t : LocalTypeC) : Nat := by
  -- Use classical choice to decide observability for the bounded unfolding depth.
  classical
  exact if hobs : ObservableC t then
    Classical.choose (hasNonMuHead_fullUnfoldN_of_observable hobs)
  else
    0

lemma hasNonMuHead_fullUnfoldN_maxUnfoldDepth {t : LocalTypeC} (hobs : ObservableC t) :
    hasNonMuHead (fullUnfoldN (maxUnfoldDepth t) t) = true := by
  unfold maxUnfoldDepth
  classical
  simp [hobs, Classical.choose_spec (hasNonMuHead_fullUnfoldN_of_observable hobs)]

lemma head_fullUnfoldN_eq_of_unfoldsToC {t u : LocalTypeC} {bound : Nat}
    (hunf : UnfoldsToC t u) (hnomu : ¬ (∃ x, head u = .mu x))
    (hobs : ObservableC t) (hbound : bound ≥ maxUnfoldDepth t) :
    head (fullUnfoldN bound t) = head u := by
  have hmax := hasNonMuHead_fullUnfoldN_maxUnfoldDepth (t := t) hobs
  have hnomu' : ¬ (∃ x, head (fullUnfoldN (maxUnfoldDepth t) t) = .mu x) := by
    intro hx
    rcases hx with ⟨x, hx⟩
    have hmax' : hasNonMuHead (fullUnfoldN (maxUnfoldDepth t) t) = true := hmax
    simp [hasNonMuHead, hx] at hmax'
  have hdet :=
    observable_head_deterministic hunf (fullUnfoldN_UnfoldsToC (maxUnfoldDepth t) t) hnomu hnomu'
  have hge : fullUnfoldN bound t = fullUnfoldN (maxUnfoldDepth t) t :=
    fullUnfoldN_eq_of_ge hbound hmax
  simpa [hge] using hdet.symm

lemma obsMatch_of_EQ2C {a b : LocalTypeC} {bound : Nat}
    (heq : EQ2C a b) (hbound : bound ≥ maxUnfoldDepth a ∧ bound ≥ maxUnfoldDepth b) :
    obsMatch bound a b = true := by
  rcases heq with ⟨R, hR, hab⟩
  obtain ⟨obs_a, obs_b, hrel⟩ := hR a b hab
  cases hrel with
  | is_end ha hb =>
      rcases ha with ⟨ua, hunf_a, hhead_a⟩
      rcases hb with ⟨ub, hunf_b, hhead_b⟩
      have hhead_a' : head (fullUnfoldN bound a) = .end := by
        have hnomu : ¬ (∃ x, head ua = .mu x) := by simp [hhead_a]
        have := head_fullUnfoldN_eq_of_unfoldsToC (bound := bound) hunf_a hnomu obs_a hbound.1
        simpa [hhead_a] using this
      have hhead_b' : head (fullUnfoldN bound b) = .end := by
        have hnomu : ¬ (∃ x, head ub = .mu x) := by simp [hhead_b]
        have := head_fullUnfoldN_eq_of_unfoldsToC (bound := bound) hunf_b hnomu obs_b hbound.2
        simpa [hhead_b] using this
      simp [obsMatch, obsKindOf, hhead_a', hhead_b']
  | is_var v ha hb =>
      rcases ha with ⟨ua, hunf_a, hhead_a⟩
      rcases hb with ⟨ub, hunf_b, hhead_b⟩
      have hhead_a' : head (fullUnfoldN bound a) = .var v := by
        have hnomu : ¬ (∃ x, head ua = .mu x) := by simp [hhead_a]
        have := head_fullUnfoldN_eq_of_unfoldsToC (bound := bound) hunf_a hnomu obs_a hbound.1
        simpa [hhead_a] using this
      have hhead_b' : head (fullUnfoldN bound b) = .var v := by
        have hnomu : ¬ (∃ x, head ub = .mu x) := by simp [hhead_b]
        have := head_fullUnfoldN_eq_of_unfoldsToC (bound := bound) hunf_b hnomu obs_b hbound.2
        simpa [hhead_b] using this
      simp [obsMatch, obsKindOf, hhead_a', hhead_b']
  | is_send p bs cs ha hb hbr =>
      rcases ha with ⟨ua, labels_a, hunf_a, hhead_a, hbs_a⟩
      rcases hb with ⟨ub, labels_b, hunf_b, hhead_b, hbs_b⟩
      have hhead_a' : head (fullUnfoldN bound a) = .send p labels_a := by
        have hnomu : ¬ (∃ x, head ua = .mu x) := by simp [hhead_a]
        have := head_fullUnfoldN_eq_of_unfoldsToC (bound := bound) hunf_a hnomu obs_a hbound.1
        simpa [hhead_a] using this
      have hhead_b' : head (fullUnfoldN bound b) = .send p labels_b := by
        have hnomu : ¬ (∃ x, head ub = .mu x) := by simp [hhead_b]
        have := head_fullUnfoldN_eq_of_unfoldsToC (bound := bound) hunf_b hnomu obs_b hbound.2
        simpa [hhead_b] using this
      have hlabels_a : labelsOfBranches bs = labels_a := by
        simpa [hbs_a] using (branchesOf_labels_eq (t := ua) (p := p) (labels := labels_a) hhead_a)
      have hlabels_b : labelsOfBranches cs = labels_b := by
        simpa [hbs_b] using (branchesOf_labels_eq (t := ub) (p := p) (labels := labels_b) hhead_b)
      have hlabels_eq : labels_a = labels_b := by
        calc
          labels_a = labelsOfBranches bs := hlabels_a.symm
          _ = labelsOfBranches cs := labelsOfBranches_eq_of_BranchesRelC hbr
          _ = labels_b := hlabels_b
      simp [obsMatch, obsKindOf, hhead_a', hhead_b', hlabels_eq]
  | is_recv p bs cs ha hb hbr =>
      rcases ha with ⟨ua, labels_a, hunf_a, hhead_a, hbs_a⟩
      rcases hb with ⟨ub, labels_b, hunf_b, hhead_b, hbs_b⟩
      have hhead_a' : head (fullUnfoldN bound a) = .recv p labels_a := by
        have hnomu : ¬ (∃ x, head ua = .mu x) := by simp [hhead_a]
        have := head_fullUnfoldN_eq_of_unfoldsToC (bound := bound) hunf_a hnomu obs_a hbound.1
        simpa [hhead_a] using this
      have hhead_b' : head (fullUnfoldN bound b) = .recv p labels_b := by
        have hnomu : ¬ (∃ x, head ub = .mu x) := by simp [hhead_b]
        have := head_fullUnfoldN_eq_of_unfoldsToC (bound := bound) hunf_b hnomu obs_b hbound.2
        simpa [hhead_b] using this
      have hlabels_a : labelsOfBranches bs = labels_a := by
        simpa [hbs_a] using (branchesOf_labels_eq_recv (t := ua) (p := p) (labels := labels_a) hhead_a)
      have hlabels_b : labelsOfBranches cs = labels_b := by
        simpa [hbs_b] using (branchesOf_labels_eq_recv (t := ub) (p := p) (labels := labels_b) hhead_b)
      have hlabels_eq : labels_a = labels_b := by
        calc
          labels_a = labelsOfBranches bs := hlabels_a.symm
          _ = labelsOfBranches cs := labelsOfBranches_eq_of_BranchesRelC hbr
          _ = labels_b := hlabels_b
      simp [obsMatch, obsKindOf, hhead_a', hhead_b', hlabels_eq]

/-! ## Completeness (Optional) -/

/-
Completeness (EQ2C ⇒ bisim = true) is intentionally omitted in the paco-first approach.
The decidable checker remains sound (bisim_sound), and coinductive proofs should use
the EQ2CE/EQ2C erasure lemmas directly (see Roundtrip.lean).
-/

/-! ## Connection to EQ2CE -/

/-- Environment-aware bisimulation with resolution (local definition for this module).
    This matches the definition in Roundtrip.lean. -/
def EQ2CE_resolved'_local (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-
The bridge from environment-aware EQ2CE to EQ2C is provided coinductively in
Roundtrip.lean (paco-style). We avoid duplicating it here to keep this file
focused on the sound decidable checker.
-/

end Telltale.Coinductive
