import Telltale.Coinductive.BisimDecidable.Part1

set_option linter.dupNamespace false

/-! # BisimDecidable Part 2

Decidable bisimulation definitions and helpers connecting `bisimAll` to `BranchesRelC`.
-/

open Classical

namespace Telltale.Coinductive
/-! ## Decidable Bisimulation Definitions -/

/-- Local decidable equality for visited membership. -/
noncomputable local instance : DecidableEq (LocalTypeC × LocalTypeC) := by
  -- Use classical choice to decide equality on pairs.
  classical
  infer_instance

/-- Helper: check if all pairs in a list satisfy bisim. -/
def bisimAll (bisimFn : LocalTypeC × LocalTypeC → Bool)
    (pairs : List (LocalTypeC × LocalTypeC)) : Bool :=
  pairs.all bisimFn

/-- The decidable bisimulation check with explicit fuel.

    For regular types a and b, this function checks if they are bisimilar.
    It uses:
    - A visited set to detect cycles
    - Fuel to ensure termination (decreases at each step)

    Parameters:
    - `fuel`: Remaining recursion depth (decreases each step)
    - `bound`: Upper bound on unfolding depth for mu
    - `visited`: Set of already-visited pairs
    - `p`: Current pair to check

    Returns `true` if the pair is bisimilar (or already visited). -/
noncomputable def bisimAux (fuel : Nat) (bound : Nat)
    (visited : Finset (LocalTypeC × LocalTypeC))
    (p : LocalTypeC × LocalTypeC) : Bool :=
  match fuel with
  | 0 => false  -- Fuel exhausted, conservatively return false
  | fuel' + 1 =>
    if p ∈ visited then
      -- Already visited: cycle detected, consider bisimilar
      true
    else
      -- Check observable match and recurse on children
      obsMatch bound p.1 p.2 &&
        bisimAll (bisimAux fuel' bound visited) (nextPairs bound p)

/-- The core relation: pairs for which bisimAux returns true (with given bound).
    Note: this is the "raw" bisim relation before combining with EQ2C. -/
def BisimRelCore (bound : Nat) : Paco.Rel LocalTypeC :=
  fun a b => ∃ fuel visited,
    (∀ q ∈ visited, EQ2C q.1 q.2) ∧ bisimAux fuel bound visited (a, b) = true

/-- The relation for paco coinduction: either bisimAux returns true, or EQ2C holds.
    Including EQ2C handles visited pairs cleanly: visited pairs satisfy EQ2C,
    and EQ2C is already a post-fixpoint of EQ2CMono. -/
def BisimRel (bound : Nat) : Paco.Rel LocalTypeC :=
  fun a b => BisimRelCore bound a b ∨ EQ2C a b

/-! ## Helper Lemmas: Connecting bisimAll to BranchesRelC -/

/-- Helper: extract labels from branchesOf. -/
def labelsOfBranches (bs : List (Label × LocalTypeC)) : List Label :=
  bs.map (·.1)

/-- BranchesRelC preserves the list of labels. -/
lemma labelsOfBranches_eq_of_BranchesRelC {R : LocalTypeC → LocalTypeC → Prop}
    {bs cs : List (Label × LocalTypeC)} (h : BranchesRelC R bs cs) :
    labelsOfBranches bs = labelsOfBranches cs := by
  induction h with
  | nil => rfl
  | cons hrel hrest ih =>
      rcases hrel with ⟨hlab, _⟩
      simpa [labelsOfBranches, hlab] using ih

/-- Helper: childrenOf for send equals the second components of branchesOf. -/
lemma childrenOf_send_eq_snd_branchesOf {t : LocalTypeC} {p : String} {labels : List Label}
    (hhead : head t = .send p labels) :
    childrenOf t = (branchesOf t).map (·.2) := by
  simp only [childrenOf, branchesOf, head] at hhead ⊢
  match hdest : PFunctor.M.dest t with
  | ⟨LocalTypeHead.send p' labels', f⟩ =>
      simp only [hdest] at hhead ⊢
      have : p = p' ∧ labels = labels' := by simp_all
      simp only [List.map_ofFn]
      rfl
  | ⟨LocalTypeHead.end, _⟩ => simp_all
  | ⟨LocalTypeHead.var _, _⟩ => simp_all
  | ⟨LocalTypeHead.recv _ _, _⟩ => simp_all
  | ⟨LocalTypeHead.mu _, _⟩ => simp_all

/-- Helper: childrenOf for recv equals the second components of branchesOf. -/
lemma childrenOf_recv_eq_snd_branchesOf {t : LocalTypeC} {p : String} {labels : List Label}
    (hhead : head t = .recv p labels) :
    childrenOf t = (branchesOf t).map (·.2) := by
  simp only [childrenOf, branchesOf, head] at hhead ⊢
  match hdest : PFunctor.M.dest t with
  | ⟨LocalTypeHead.recv p' labels', f⟩ =>
      simp only [hdest] at hhead ⊢
      have : p = p' ∧ labels = labels' := by simp_all
      simp only [List.map_ofFn]
      rfl
  | ⟨LocalTypeHead.end, _⟩ => simp_all
  | ⟨LocalTypeHead.var _, _⟩ => simp_all
  | ⟨LocalTypeHead.send _ _, _⟩ => simp_all
  | ⟨LocalTypeHead.mu _, _⟩ => simp_all

/-- Helper: if bisimAll succeeds on zipped children, construct BranchesRelC.
    This requires showing that the branches have matching labels. -/
lemma bisimAll_to_BranchesRelC {R : LocalTypeC → LocalTypeC → Prop}
    {bs cs : List (Label × LocalTypeC)}
    (hlen : bs.length = cs.length)
    (hlabels : ∀ i : Fin bs.length, (bs.get i).1 = (cs.get ⟨i.val, hlen ▸ i.isLt⟩).1)
    (hchildren : ∀ i : Fin bs.length, R (bs.get i).2 (cs.get ⟨i.val, hlen ▸ i.isLt⟩).2) :
    BranchesRelC R bs cs := by
  revert cs
  induction bs with
  | nil =>
      intro cs hlen hlabels hchildren
      simp only [List.length_nil] at hlen
      have : cs = [] := by
        cases cs with
        | nil => rfl
        | cons _ _ => simp at hlen
      rw [this]
      exact List.Forall₂.nil
  | cons b bs ih =>
      intro cs hlen hlabels hchildren
      cases cs with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen
          omega
      | cons c cs =>
          simp only [List.length_cons] at hlen
          have hlen' : bs.length = cs.length := Nat.succ.inj hlen
          refine List.Forall₂.cons ?_ (ih hlen' ?_ ?_)
          · -- First element
            have hlabel := hlabels ⟨0, by simp⟩
            have hchild := hchildren ⟨0, by simp⟩
            simp only [List.get_eq_getElem, List.getElem_cons_zero] at hlabel hchild
            exact ⟨hlabel, hchild⟩
          · -- Labels for tail
            intro i
            have hi_succ : i.val + 1 < (b :: bs).length := by
              simp only [List.length_cons]
              omega
            have hlabel := hlabels ⟨i.val + 1, hi_succ⟩
            simp only [List.get_eq_getElem, List.getElem_cons_succ] at hlabel
            exact hlabel
          · -- Children for tail
            intro i
            have hi_succ : i.val + 1 < (b :: bs).length := by
              simp only [List.length_cons]
              omega
            have hchild := hchildren ⟨i.val + 1, hi_succ⟩
            simp only [List.get_eq_getElem, List.getElem_cons_succ] at hchild
            exact hchild

/-- Helper: branchesOf preserves label structure. -/
lemma branchesOf_labels_eq {t : LocalTypeC} {p : String} {labels : List Label}
    (hhead : head t = .send p labels) :
    labelsOfBranches (branchesOf t) = labels := by
  simp only [labelsOfBranches, branchesOf, head] at hhead ⊢
  match hdest : PFunctor.M.dest t with
  | ⟨LocalTypeHead.send p' labels', f⟩ =>
      simp only [hdest] at hhead ⊢
      have : p = p' ∧ labels = labels' := by simp_all
      have ⟨_, hlabels⟩ := this
      subst hlabels
      simp only [List.map_ofFn]
      exact List.ofFn_get labels
  | ⟨LocalTypeHead.end, _⟩ => simp_all
  | ⟨LocalTypeHead.var _, _⟩ => simp_all
  | ⟨LocalTypeHead.recv _ _, _⟩ => simp_all
  | ⟨LocalTypeHead.mu _, _⟩ => simp_all

/-- Helper: branchesOf preserves label structure for recv. -/
lemma branchesOf_labels_eq_recv {t : LocalTypeC} {p : String} {labels : List Label}
    (hhead : head t = .recv p labels) :
    labelsOfBranches (branchesOf t) = labels := by
  simp only [labelsOfBranches, branchesOf, head] at hhead ⊢
  match hdest : PFunctor.M.dest t with
  | ⟨LocalTypeHead.recv p' labels', f⟩ =>
      simp only [hdest] at hhead ⊢
      have : p = p' ∧ labels = labels' := by simp_all
      have ⟨_, hlabels⟩ := this
      subst hlabels
      simp only [List.map_ofFn]
      exact List.ofFn_get labels
  | ⟨LocalTypeHead.end, _⟩ => simp_all
  | ⟨LocalTypeHead.var _, _⟩ => simp_all
  | ⟨LocalTypeHead.send _ _, _⟩ => simp_all
  | ⟨LocalTypeHead.mu _, _⟩ => simp_all

/-- Key lemma: if obsMatch succeeds with send and bisimAll succeeds on nextPairs,
    then we have BranchesRelC relating the branches. -/
lemma obsMatch_send_bisimAll_to_BranchesRelC {n : Nat} {a b : LocalTypeC}
    {fuel : Nat} {visited_any : Finset (LocalTypeC × LocalTypeC)}
    {p : String} {labels : List Label}
    (hk_a : obsKindOf (fullUnfoldN n a) = some (.obs_send p labels))
    (hk_b : obsKindOf (fullUnfoldN n b) = some (.obs_send p labels))
    (hchildren : bisimAll (bisimAux fuel n visited_any) (nextPairs n (a, b)) = true)
    (hvisited : ∀ q ∈ visited_any, EQ2C q.1 q.2) :
    BranchesRelC (BisimRel n)
      (branchesOf (fullUnfoldN n a))
      (branchesOf (fullUnfoldN n b)) := by
  have hhead_a := obsKindOf_send_iff.mp hk_a
  have hhead_b := obsKindOf_send_iff.mp hk_b
  let bs := branchesOf (fullUnfoldN n a)
  let cs := branchesOf (fullUnfoldN n b)
  have hlabels_a := branchesOf_labels_eq hhead_a
  have hlabels_b := branchesOf_labels_eq hhead_b
  have hlen : bs.length = cs.length := by
    simp only [labelsOfBranches] at hlabels_a hlabels_b
    have ha : bs.length = labels.length := by
      have := congrArg List.length hlabels_a
      simp only [List.length_map] at this
      exact this
    have hb : cs.length = labels.length := by
      have := congrArg List.length hlabels_b
      simp only [List.length_map] at this
      exact this
    omega
  apply bisimAll_to_BranchesRelC hlen
  · intro i
    have hlen_a : bs.length = labels.length := by
      have := congrArg List.length hlabels_a
      simp [labelsOfBranches] at this
      exact this
    have hlen_b : cs.length = labels.length := by
      have := congrArg List.length hlabels_b
      simp [labelsOfBranches] at this
      exact this
    let i_label : Fin labels.length := ⟨i.val, by simpa [hlen_a] using i.isLt⟩
    let i_map : Fin (bs.map (·.1)).length := ⟨i.val, by simp [List.length_map]⟩
    have hlabels_a' : bs.map (·.1) = labels := by
      simpa [labelsOfBranches] using hlabels_a
    have hmap_get_a : (bs.map (·.1)).get i_map = labels.get i_label := by
      simpa using (List.get_eq_get_of_eq hlabels_a' i_map)
    have hget_a : (bs.get i).1 = labels.get i_label := by
      have hmap' : (bs.get i).1 = (bs.map (·.1)).get i_map := by
        simp [i_map]
      exact hmap'.trans hmap_get_a
    let j : Fin cs.length := ⟨i.val, hlen ▸ i.isLt⟩
    let j_map : Fin (cs.map (·.1)).length := ⟨i.val, by
      have : i.val < cs.length := j.isLt
      simp [List.length_map]
      exact this⟩
    have hlabels_b' : cs.map (·.1) = labels := by
      simpa [labelsOfBranches] using hlabels_b
    have hmap_get_b : (cs.map (·.1)).get j_map = labels.get i_label := by
      have h := List.get_eq_get_of_eq hlabels_b' j_map
      simpa [j_map, i_label, hlen_b] using h
    have hget_b : (cs.get j).1 = labels.get i_label := by
      have hmap' : (cs.get j).1 = (cs.map (·.1)).get j_map := by
        simp [j, j_map]
      exact hmap'.trans hmap_get_b
    exact hget_a.trans hget_b.symm
  · intro i
    -- Children are in BisimRel: extract from bisimAll on nextPairs
    simp only [nextPairs, zipChildren, bisimAll, List.all_eq_true] at hchildren
    -- Get child equality lemmas
    have hchildren_eq_a := childrenOf_send_eq_snd_branchesOf hhead_a
    have hchildren_eq_b := childrenOf_send_eq_snd_branchesOf hhead_b
    -- The children are the second components
    have ha_child : (bs.get i).2 = (List.map (·.2) bs).get ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩ := by
      exact (List.get_map' (·.2) bs i).symm
    have hb_child : (cs.get ⟨i.val, hlen ▸ i.isLt⟩).2 = (List.map (·.2) cs).get ⟨i.val, by simp only [List.length_map]; omega⟩ := by
      exact (List.get_map' (·.2) cs ⟨i.val, hlen ▸ i.isLt⟩).symm
    -- The pair is in the zip
    have hmem : ((List.map (·.2) bs).get ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩,
                 (List.map (·.2) cs).get ⟨i.val, by simp only [List.length_map]; omega⟩) ∈
                List.zip (List.map (·.2) bs) (List.map (·.2) cs) := by
      apply List.get_mem_zip
      simp only [List.length_map, hlen]
    -- Convert hmem to use childrenOf
    have hmem' : ((List.map (·.2) bs).get ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩,
                  (List.map (·.2) cs).get ⟨i.val, by simp only [List.length_map]; omega⟩) ∈
                 (childrenOf (fullUnfoldN n a)).zip (childrenOf (fullUnfoldN n b)) := by
      rw [hchildren_eq_a, hchildren_eq_b]
      exact hmem
    -- bisimAll says this pair satisfies bisimAux
    have hpair := hchildren _ hmem'
    -- This means it's in BisimRelCore, hence BisimRel
    rw [ha_child, hb_child]
    exact Or.inl ⟨fuel, visited_any, hvisited, hpair⟩

/-- Key lemma: if obsMatch succeeds with recv and bisimAll succeeds on nextPairs,
    then we have BranchesRelC relating the branches. -/
lemma obsMatch_recv_bisimAll_to_BranchesRelC {n : Nat} {a b : LocalTypeC}
    {fuel : Nat} {visited_any : Finset (LocalTypeC × LocalTypeC)}
    {p : String} {labels : List Label}
    (hk_a : obsKindOf (fullUnfoldN n a) = some (.obs_recv p labels))
    (hk_b : obsKindOf (fullUnfoldN n b) = some (.obs_recv p labels))
    (hchildren : bisimAll (bisimAux fuel n visited_any) (nextPairs n (a, b)) = true)
    (hvisited : ∀ q ∈ visited_any, EQ2C q.1 q.2) :
    BranchesRelC (BisimRel n)
      (branchesOf (fullUnfoldN n a))
      (branchesOf (fullUnfoldN n b)) := by
  have hhead_a := obsKindOf_recv_iff.mp hk_a
  have hhead_b := obsKindOf_recv_iff.mp hk_b
  let bs := branchesOf (fullUnfoldN n a)
  let cs := branchesOf (fullUnfoldN n b)
  have hlabels_a := branchesOf_labels_eq_recv hhead_a
  have hlabels_b := branchesOf_labels_eq_recv hhead_b
  have hlen : bs.length = cs.length := by
    simp only [labelsOfBranches] at hlabels_a hlabels_b
    have ha : bs.length = labels.length := by
      have := congrArg List.length hlabels_a
      simp only [List.length_map] at this
      exact this
    have hb : cs.length = labels.length := by
      have := congrArg List.length hlabels_b
      simp only [List.length_map] at this
      exact this
    omega
  apply bisimAll_to_BranchesRelC hlen
  · intro i
    have hlen_a : bs.length = labels.length := by
      have := congrArg List.length hlabels_a
      simp [labelsOfBranches] at this
      exact this
    have hlen_b : cs.length = labels.length := by
      have := congrArg List.length hlabels_b
      simp [labelsOfBranches] at this
      exact this
    let i_label : Fin labels.length := ⟨i.val, by simpa [hlen_a] using i.isLt⟩
    let i_map : Fin (bs.map (·.1)).length := ⟨i.val, by simp [List.length_map]⟩
    have hlabels_a' : bs.map (·.1) = labels := by
      simpa [labelsOfBranches] using hlabels_a
    have hmap_get_a : (bs.map (·.1)).get i_map = labels.get i_label := by
      simpa using (List.get_eq_get_of_eq hlabels_a' i_map)
    have hget_a : (bs.get i).1 = labels.get i_label := by
      have hmap' : (bs.get i).1 = (bs.map (·.1)).get i_map := by
        simp [i_map]
      exact hmap'.trans hmap_get_a
    let j : Fin cs.length := ⟨i.val, hlen ▸ i.isLt⟩
    let j_map : Fin (cs.map (·.1)).length := ⟨i.val, by
      have : i.val < cs.length := j.isLt
      simp [List.length_map]
      exact this⟩
    have hlabels_b' : cs.map (·.1) = labels := by
      simpa [labelsOfBranches] using hlabels_b
    have hmap_get_b : (cs.map (·.1)).get j_map = labels.get i_label := by
      have h := List.get_eq_get_of_eq hlabels_b' j_map
      simpa [j_map, i_label, hlen_b] using h
    have hget_b : (cs.get j).1 = labels.get i_label := by
      have hmap' : (cs.get j).1 = (cs.map (·.1)).get j_map := by
        simp [j, j_map]
      exact hmap'.trans hmap_get_b
    exact hget_a.trans hget_b.symm
  · intro i
    -- Children are in BisimRel (same proof as send case)
    simp only [nextPairs, zipChildren, bisimAll, List.all_eq_true] at hchildren
    have hchildren_eq_a := childrenOf_recv_eq_snd_branchesOf hhead_a
    have hchildren_eq_b := childrenOf_recv_eq_snd_branchesOf hhead_b
    have ha_child : (bs.get i).2 = (List.map (·.2) bs).get ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩ := by
      exact (List.get_map' (·.2) bs i).symm
    have hb_child : (cs.get ⟨i.val, hlen ▸ i.isLt⟩).2 = (List.map (·.2) cs).get ⟨i.val, by simp only [List.length_map]; omega⟩ := by
      exact (List.get_map' (·.2) cs ⟨i.val, hlen ▸ i.isLt⟩).symm
    have hmem : ((List.map (·.2) bs).get ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩,
                 (List.map (·.2) cs).get ⟨i.val, by simp only [List.length_map]; omega⟩) ∈
                List.zip (List.map (·.2) bs) (List.map (·.2) cs) := by
      apply List.get_mem_zip
      simp only [List.length_map, hlen]
    -- Convert hmem to use childrenOf
    have hmem' : ((List.map (·.2) bs).get ⟨i.val, by simp only [List.length_map]; exact i.isLt⟩,
                  (List.map (·.2) cs).get ⟨i.val, by simp only [List.length_map]; omega⟩) ∈
                 (childrenOf (fullUnfoldN n a)).zip (childrenOf (fullUnfoldN n b)) := by
      rw [hchildren_eq_a, hchildren_eq_b]
      exact hmem
    have hpair := hchildren _ hmem'
    rw [ha_child, hb_child]
    exact Or.inl ⟨fuel, visited_any, hvisited, hpair⟩

end Telltale.Coinductive
