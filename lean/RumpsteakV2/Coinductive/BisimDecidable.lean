import Mathlib
import Paco
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CEnv
import RumpsteakV2.Coinductive.EQ2CPaco
import RumpsteakV2.Coinductive.EQ2CProps
import RumpsteakV2.Coinductive.BisimHelpers

set_option linter.dupNamespace false

/-!
# Decidable Bisimulation for Regular Types

This module implements a decidable bisimulation check for regular coinductive types,
following the approach in the Coq reference implementation (subject_reduction/theories/CoTypes/bisim.v).

## Two-Phase Approach

1. **Phase 1**: Define a decidable `bisim` function with explicit termination via a measure
   - Uses a visited set to detect cycles
   - Terminates because the set of unvisited pairs decreases

2. **Phase 2**: Prove `bisim_sound` - that `bisim = true` implies `EQ2C`
   - Uses the existing bisimulation infrastructure

## Key Definitions

- `fullUnfoldN`: Unfold mu up to n times (bounded unfolding)
- `fullUnfold`: Unfold all mu until non-mu head (for regular types)
- `nextChildren`: Get children of a type after unfolding
- `reachablePairs`: Cartesian product of reachable sets
- `observableMatch`: Check if observables match
- `bisim`: The decidable bisimulation check
- `bisim_sound`: Soundness theorem
-/

namespace RumpsteakV2.Coinductive

open Classical
open RumpsteakV2.Protocol.GlobalType

/-! ## Bounded Unfolding -/

/-- Unfold mu up to n times. Returns the result after unfolding or the original if stuck. -/
def fullUnfoldN : Nat → LocalTypeC → LocalTypeC
  | 0, t => t
  | n + 1, t =>
    match PFunctor.M.dest t with
    | ⟨LocalTypeHead.mu _, f⟩ => fullUnfoldN n (f ())
    | _ => t

/-- Check if a type has a non-mu head. -/
def hasNonMuHead (t : LocalTypeC) : Bool :=
  match head t with
  | .mu _ => false
  | _ => true

/-- For regular types, there's a bound on unfolding depth. -/
lemma hasNonMuHead_fullUnfoldN_of_regular {t : LocalTypeC} (hreg : Regular t) :
    ∃ n, hasNonMuHead (fullUnfoldN n t) = true := by
  -- For regular types, the reachable set is finite
  -- Each unfolding moves to a different node
  -- Eventually we must reach a non-mu node (or cycle back)
  sorry -- This requires showing regular types have bounded mu-nesting

/-! ## Connection between fullUnfoldN and UnfoldsToC -/

/-- One step unfolding: if dest gives mu, we have UnfoldsC. -/
lemma unfoldsC_of_dest_mu {t : LocalTypeC} {x : String} {f : Unit → LocalTypeC}
    (hdest : PFunctor.M.dest t = ⟨LocalTypeHead.mu x, f⟩) :
    UnfoldsC t (f ()) := ⟨x, f, hdest, rfl⟩

/-- fullUnfoldN produces a chain of UnfoldsC steps. -/
lemma fullUnfoldN_UnfoldsToC (n : Nat) (t : LocalTypeC) :
    UnfoldsToC t (fullUnfoldN n t) := by
  induction n generalizing t with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      simp only [fullUnfoldN]
      match hdest : PFunctor.M.dest t with
      | ⟨LocalTypeHead.mu x, f⟩ =>
          have hstep : UnfoldsC t (f ()) := unfoldsC_of_dest_mu hdest
          exact Relation.ReflTransGen.head hstep (ih (f ()))
      | ⟨LocalTypeHead.end, _⟩ => exact Relation.ReflTransGen.refl
      | ⟨LocalTypeHead.var _, _⟩ => exact Relation.ReflTransGen.refl
      | ⟨LocalTypeHead.send _ _, _⟩ => exact Relation.ReflTransGen.refl
      | ⟨LocalTypeHead.recv _ _, _⟩ => exact Relation.ReflTransGen.refl

/-- Observable kind for comparison. -/
inductive ObsKind
  | obs_end : ObsKind
  | obs_var (v : String) : ObsKind
  | obs_send (p : String) (labels : List Label) : ObsKind
  | obs_recv (p : String) (labels : List Label) : ObsKind
  deriving DecidableEq

/-- Extract observable kind from head (after unfolding). -/
def obsKindOf (t : LocalTypeC) : Option ObsKind :=
  match head t with
  | .end => some .obs_end
  | .var v => some (.obs_var v)
  | .send p labels => some (.obs_send p labels)
  | .recv p labels => some (.obs_recv p labels)
  | .mu _ => none

/-- If obsKindOf gives Some, the type is observable. -/
lemma obsKindOf_some_implies_observable {t : LocalTypeC} {k : ObsKind}
    (hk : obsKindOf t = some k) : ObservableC t := by
  simp only [obsKindOf] at hk
  match hhead : head t with
  | .end => exact ObservableC.is_end ⟨t, Relation.ReflTransGen.refl, hhead⟩
  | .var v => exact ObservableC.is_var v ⟨t, Relation.ReflTransGen.refl, hhead⟩
  | .send p labels =>
      -- The head being send implies we can extract branches
      have hbs : branchesOf t = branchesOf t := rfl  -- placeholder
      exact ObservableC.is_send p (branchesOf t) ⟨t, labels, Relation.ReflTransGen.refl, hhead, rfl⟩
  | .recv p labels =>
      exact ObservableC.is_recv p (branchesOf t) ⟨t, labels, Relation.ReflTransGen.refl, hhead, rfl⟩
  | .mu x => simp [hhead] at hk

/-! ## Children Extraction -/

/-- Get the children of a type (continuations after communication). -/
def childrenOf (t : LocalTypeC) : List LocalTypeC :=
  match PFunctor.M.dest t with
  | ⟨LocalTypeHead.send _ labels, f⟩ => List.ofFn fun i : Fin labels.length => f i
  | ⟨LocalTypeHead.recv _ labels, f⟩ => List.ofFn fun i : Fin labels.length => f i
  | ⟨LocalTypeHead.mu _, f⟩ => [f ()]
  | _ => []

/-- Get children after full unfolding. -/
def childrenAfterUnfold (n : Nat) (t : LocalTypeC) : List LocalTypeC :=
  childrenOf (fullUnfoldN n t)

/-! ## Pair Operations -/

/-- Zip two lists of children into pairs. -/
def zipChildren (cs ds : List LocalTypeC) : List (LocalTypeC × LocalTypeC) :=
  List.zip cs ds

/-- Get next pairs after unfolding both types. -/
def nextPairs (n : Nat) (p : LocalTypeC × LocalTypeC) : List (LocalTypeC × LocalTypeC) :=
  let t1 := fullUnfoldN n p.1
  let t2 := fullUnfoldN n p.2
  zipChildren (childrenOf t1) (childrenOf t2)

/-! ## Observable Matching -/

/-- Check if two types have matching observable kinds (after bounded unfolding). -/
def obsMatch (n : Nat) (t1 t2 : LocalTypeC) : Bool :=
  let u1 := fullUnfoldN n t1
  let u2 := fullUnfoldN n t2
  match obsKindOf u1, obsKindOf u2 with
  | some k1, some k2 => k1 == k2
  | _, _ => false

/-! ## Observable Match Lemmas -/

/-- If obsMatch returns true, both types have the same observable kind after unfolding. -/
lemma obsMatch_true_implies_same_kind {n : Nat} {t1 t2 : LocalTypeC}
    (h : obsMatch n t1 t2 = true) :
    ∃ k, obsKindOf (fullUnfoldN n t1) = some k ∧ obsKindOf (fullUnfoldN n t2) = some k := by
  -- This follows from the definition of obsMatch: it returns true only when
  -- both obsKindOf return some and the kinds are equal
  simp only [obsMatch] at h
  split at h <;> simp_all

/-! ## ObsKind Helper Lemmas -/

/-- Helper: observable kind end means head is end -/
lemma obsKindOf_end_iff {t : LocalTypeC} :
    obsKindOf t = some .obs_end ↔ head t = .end := by
  simp only [obsKindOf]
  constructor
  · intro h; match hh : head t with
    | .end => rfl
    | .var _ => simp [hh] at h
    | .send _ _ => simp [hh] at h
    | .recv _ _ => simp [hh] at h
    | .mu _ => simp [hh] at h
  · intro h; simp [h]

/-- Helper: observable kind var means head is var with same name -/
lemma obsKindOf_var_iff {t : LocalTypeC} {v : String} :
    obsKindOf t = some (.obs_var v) ↔ head t = .var v := by
  simp only [obsKindOf]
  constructor
  · intro h; match hh : head t with
    | .end => simp [hh] at h
    | .var v' => simp [hh] at h; simp [h]
    | .send _ _ => simp [hh] at h
    | .recv _ _ => simp [hh] at h
    | .mu _ => simp [hh] at h
  · intro h; simp [h]

/-- Helper: observable kind send means head is send -/
lemma obsKindOf_send_iff {t : LocalTypeC} {p : String} {labels : List Label} :
    obsKindOf t = some (.obs_send p labels) ↔ head t = .send p labels := by
  simp only [obsKindOf]
  constructor
  · intro h; match hh : head t with
    | .end => simp [hh] at h
    | .var _ => simp [hh] at h
    | .send p' labels' => simp [hh] at h; simp [h]
    | .recv _ _ => simp [hh] at h
    | .mu _ => simp [hh] at h
  · intro h; simp [h]

/-- Helper: observable kind recv means head is recv -/
lemma obsKindOf_recv_iff {t : LocalTypeC} {p : String} {labels : List Label} :
    obsKindOf t = some (.obs_recv p labels) ↔ head t = .recv p labels := by
  simp only [obsKindOf]
  constructor
  · intro h; match hh : head t with
    | .end => simp [hh] at h
    | .var _ => simp [hh] at h
    | .send _ _ => simp [hh] at h
    | .recv p' labels' => simp [hh] at h; simp [h]
    | .mu _ => simp [hh] at h
  · intro h; simp [h]

/-! ## Decidable Bisimulation Definitions -/

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
      let visited' := insert p visited
      obsMatch bound p.1 p.2 &&
        bisimAll (bisimAux fuel' bound visited') (nextPairs bound p)

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
        | cons _ _ => simp_all
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
            convert hlabel using 2 <;> simp [List.get_eq_getElem]
          · -- Children for tail
            intro i
            have hi_succ : i.val + 1 < (b :: bs).length := by
              simp only [List.length_cons]
              omega
            have hchild := hchildren ⟨i.val + 1, hi_succ⟩
            simp only [List.get_eq_getElem, List.getElem_cons_succ] at hchild
            convert hchild using 2 <;> simp [List.get_eq_getElem]

/-- Helper: branchesOf preserves label structure. -/
lemma branchesOf_labels_eq {t : LocalTypeC} {p : String} {labels : List Label}
    (hhead : head t = .send p labels) :
    labelsOfBranches (branchesOf t) = labels := by
  simp only [labelsOfBranches, branchesOf, head] at hhead ⊢
  match hdest : PFunctor.M.dest t with
  | ⟨LocalTypeHead.send p' labels', f⟩ =>
      simp only [hdest] at hhead ⊢
      have : p = p' ∧ labels = labels' := by simp_all
      simp only [List.map_ofFn]
      have ⟨_, hlabels⟩ := this
      subst hlabels
      simp
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
      simp only [List.map_ofFn]
      have ⟨_, hlabels⟩ := this
      subst hlabels
      simp
  | ⟨LocalTypeHead.end, _⟩ => simp_all
  | ⟨LocalTypeHead.var _, _⟩ => simp_all
  | ⟨LocalTypeHead.send _ _, _⟩ => simp_all
  | ⟨LocalTypeHead.mu _, _⟩ => simp_all

/-- Key lemma: if obsMatch succeeds with send and bisimAll succeeds on nextPairs,
    then we have BranchesRelC relating the branches. -/
lemma obsMatch_send_bisimAll_to_BranchesRelC {n : Nat} {a b : LocalTypeC}
    {fuel : Nat} {visited_any : Finset (LocalTypeC × LocalTypeC)}
    {p : String} {labels : List Label}
    (hvisited : ∀ q ∈ visited_any, EQ2C q.1 q.2)
    (hobs : obsMatch n a b = true)
    (hk_a : obsKindOf (fullUnfoldN n a) = some (.obs_send p labels))
    (hk_b : obsKindOf (fullUnfoldN n b) = some (.obs_send p labels))
    (hchildren : bisimAll (bisimAux fuel n visited_any) (nextPairs n (a, b)) = true) :
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
    -- Labels match pointwise: bs.map (·.1) = labels and cs.map (·.1) = labels
    simp only [labelsOfBranches] at hlabels_a hlabels_b
    have ha : (bs.get i).1 = labels.get i := by
      have := congrFun (congrArg List.get hlabels_a) i
      simp only [List.get_map] at this
      exact this
    have hb : (cs.get ⟨i.val, hlen ▸ i.isLt⟩).1 = labels.get ⟨i.val, by omega⟩ := by
      have := congrFun (congrArg List.get hlabels_b) ⟨i.val, hlen ▸ i.isLt⟩
      simp only [List.get_map] at this
      exact this
    rw [ha, hb]
  · intro i
    -- Children are in BisimRel: extract from bisimAll on nextPairs
    simp only [nextPairs, zipChildren, bisimAll, List.all_eq_true] at hchildren
    -- Get child equality lemmas
    have hchildren_eq_a := childrenOf_send_eq_snd_branchesOf hhead_a
    have hchildren_eq_b := childrenOf_send_eq_snd_branchesOf hhead_b
    -- The children are the second components
    have : (bs.get i).2 = (childrenOf (fullUnfoldN n a)).get ⟨i.val, by rw [hchildren_eq_a]; simp; exact i.isLt⟩ := by
      conv_lhs => rw [← List.get_map (·.2) bs i]
      rw [← hchildren_eq_a]; rfl
    have : (cs.get ⟨i.val, hlen ▸ i.isLt⟩).2 = (childrenOf (fullUnfoldN n b)).get ⟨i.val, by rw [hchildren_eq_b]; simp [hlen]; exact i.isLt⟩ := by
      conv_lhs => rw [← List.get_map (·.2) cs ⟨i.val, hlen ▸ i.isLt⟩]
      rw [← hchildren_eq_b]; rfl
    -- The pair is in the zip
    have hmem : ((childrenOf (fullUnfoldN n a)).get ⟨i.val, _⟩, (childrenOf (fullUnfoldN n b)).get ⟨i.val, _⟩) ∈
                List.zip (childrenOf (fullUnfoldN n a)) (childrenOf (fullUnfoldN n b)) := by
      apply List.get_mem_zip
      rw [hchildren_eq_a, hchildren_eq_b]; simp [hlen]
    -- bisimAll says this pair satisfies bisimAux
    have hpair := hchildren _ hmem
    -- This means it's in BisimRelCore, hence BisimRel
    exact Or.inl ⟨fuel, visited_any, hvisited, hpair⟩

/-- Key lemma: if obsMatch succeeds with recv and bisimAll succeeds on nextPairs,
    then we have BranchesRelC relating the branches. -/
lemma obsMatch_recv_bisimAll_to_BranchesRelC {n : Nat} {a b : LocalTypeC}
    {fuel : Nat} {visited_any : Finset (LocalTypeC × LocalTypeC)}
    {p : String} {labels : List Label}
    (hvisited : ∀ q ∈ visited_any, EQ2C q.1 q.2)
    (hobs : obsMatch n a b = true)
    (hk_a : obsKindOf (fullUnfoldN n a) = some (.obs_recv p labels))
    (hk_b : obsKindOf (fullUnfoldN n b) = some (.obs_recv p labels))
    (hchildren : bisimAll (bisimAux fuel n visited_any) (nextPairs n (a, b)) = true) :
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
    -- Labels match pointwise (same proof as send case)
    simp only [labelsOfBranches] at hlabels_a hlabels_b
    have ha : (bs.get i).1 = labels.get i := by
      have := congrFun (congrArg List.get hlabels_a) i
      simp only [List.get_map] at this
      exact this
    have hb : (cs.get ⟨i.val, hlen ▸ i.isLt⟩).1 = labels.get ⟨i.val, by omega⟩ := by
      have := congrFun (congrArg List.get hlabels_b) ⟨i.val, hlen ▸ i.isLt⟩
      simp only [List.get_map] at this
      exact this
    rw [ha, hb]
  · intro i
    -- Children are in BisimRel (same proof as send case)
    simp only [nextPairs, zipChildren, bisimAll, List.all_eq_true] at hchildren
    have hchildren_eq_a := childrenOf_recv_eq_snd_branchesOf hhead_a
    have hchildren_eq_b := childrenOf_recv_eq_snd_branchesOf hhead_b
    have : (bs.get i).2 = (childrenOf (fullUnfoldN n a)).get ⟨i.val, by rw [hchildren_eq_a]; simp; exact i.isLt⟩ := by
      conv_lhs => rw [← List.get_map (·.2) bs i]
      rw [← hchildren_eq_a]; rfl
    have : (cs.get ⟨i.val, hlen ▸ i.isLt⟩).2 = (childrenOf (fullUnfoldN n b)).get ⟨i.val, by rw [hchildren_eq_b]; simp [hlen]; exact i.isLt⟩ := by
      conv_lhs => rw [← List.get_map (·.2) cs ⟨i.val, hlen ▸ i.isLt⟩]
      rw [← hchildren_eq_b]; rfl
    have hmem : ((childrenOf (fullUnfoldN n a)).get ⟨i.val, _⟩, (childrenOf (fullUnfoldN n b)).get ⟨i.val, _⟩) ∈
                List.zip (childrenOf (fullUnfoldN n a)) (childrenOf (fullUnfoldN n b)) := by
      apply List.get_mem_zip
      rw [hchildren_eq_a, hchildren_eq_b]; simp [hlen]
    have hpair := hchildren _ hmem
    exact Or.inl ⟨fuel, visited_any, hvisited, hpair⟩

/-! ## Reachable Pairs -/

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
              have hbr := obsMatch_send_bisimAll_to_BranchesRelC hvisited hobs hk_a hk_b hchildren
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
              have hbr := obsMatch_recv_bisimAll_to_BranchesRelC hvisited hobs hk_a hk_b hchildren
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
noncomputable def maxUnfoldDepth (t : LocalTypeC) : Nat :=
  -- For regular types, this is bounded by the reachable set size
  -- since each unfolding visits a different node
  sorry

/-! ## Completeness (Optional) -/

/-- Completeness: EQ2C implies bisim = true.
    This is less critical but proves the check is exact. -/
theorem bisim_complete {a b : LocalTypeC} {ha : Regular a} {hb : Regular b} {bound : Nat}
    (heq : EQ2C a b) (hbound : bound ≥ maxUnfoldDepth a ∧ bound ≥ maxUnfoldDepth b) :
    bisim a b ha hb bound = true := by
  sorry

/-! ## Connection to EQ2CE -/

/-- Environment-aware bisimulation with resolution (local definition for this module).
    This matches the definition in RoundtripWIP.lean. -/
def EQ2CE_resolved'_local (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

/-- For environment-resolved EQ2CE, we can use bisim to eliminate the termination sorry.

    This theorem provides an alternative to `EQ2CE_resolved'_implies_EQ2C` in RoundtripWIP.lean
    that works for regular types. The proof strategy is:
    1. EQ2CE_resolved'_local implies types are bisimilar in the coinductive sense
    2. For regular types, this bisimilarity is witnessed by `bisim = true`
    3. By `bisim_sound`, we conclude EQ2C

    The termination is guaranteed because:
    - The types are regular (finite reachable set)
    - `bisim` uses fuel bounded by reachable pairs
    - Each step decreases fuel

    This mirrors the Coq proof in subject_reduction/theories/CoTypes/bisim.v
    where `bisim_sound` is used to convert decidable bisimilarity to EQ2. -/
theorem EQ2CE_resolved'_implies_EQ2C_via_bisim
    {a b : LocalTypeC} (ha : Regular a) (hb : Regular b)
    (h : EQ2CE_resolved'_local a b) :
    EQ2C a b := by
  -- Proof outline:
  -- 1. Show that EQ2CE_resolved'_local implies bisim returns true
  --    (this is completeness of bisim w.r.t. EQ2CE)
  -- 2. Apply bisim_sound to get EQ2C
  --
  -- The completeness direction requires showing that the observable
  -- structure of EQ2CE matches what bisim checks. This follows from:
  -- - EQ2CE unfolds mu to reveal observable heads
  -- - obsMatch checks the same observable structure
  -- - EQ2CE relates children, bisim checks children recursively
  --
  -- For now, we use sorry. The soundness theorem (bisim_sound) shows
  -- that the decidable approach is correct; completeness ensures it
  -- captures all EQ2C pairs for regular types.
  sorry

end RumpsteakV2.Coinductive
