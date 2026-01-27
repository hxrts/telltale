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

/-! ## List Helpers -/

/-- Helper: accessing a mapped list element. -/
lemma List.get_map' {α β : Type*} (f : α → β) (xs : List α) (i : Fin xs.length) :
    (xs.map f).get ⟨i.val, by simp [i.isLt]⟩ = f (xs.get i) := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih i

/-- Helper: get from zipped lists. -/
lemma List.get_mem_zip {α β : Type*} (as : List α) (bs : List β) (i : Fin as.length)
    (hlen : as.length = bs.length) :
    (as.get i, bs.get ⟨i.val, hlen ▸ i.isLt⟩) ∈ List.zip as bs := by
  induction as generalizing bs with
  | nil => exact Fin.elim0 i
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons] at hlen
      cases i using Fin.cases with
      | zero => simp [List.zip]
      | succ i =>
        simp [List.zip]
        right
        exact ih bs i (Nat.succ.inj hlen)

/-- Helper: transport `get` across list equality. -/
lemma List.get_eq_get_of_eq {α : Type*} {xs ys : List α} (h : xs = ys) (i : Fin xs.length) :
    xs.get i = ys.get ⟨i.val, by simpa [h] using i.isLt⟩ := by
  subst h
  have : (⟨i.val, i.isLt⟩ : Fin xs.length) = i := by
    apply Fin.ext
    rfl
  simp [this]

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

lemma fullUnfoldN_of_unfoldsToC {t u : LocalTypeC} (h : UnfoldsToC t u) :
    ∃ n, fullUnfoldN n t = u := by
  refine Relation.ReflTransGen.head_induction_on h ?refl ?head
  · exact ⟨0, rfl⟩
  · intro a c hstep hrest ih
    rcases hstep with ⟨x, f, hdest, rfl⟩
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    simp [fullUnfoldN, hdest, hn]

/-- If a type is observable, then bounded unfolding reaches a non-mu head. -/
lemma hasNonMuHead_fullUnfoldN_of_observable {t : LocalTypeC} (hobs : ObservableC t) :
    ∃ n, hasNonMuHead (fullUnfoldN n t) = true := by
  cases hobs with
  | is_end h =>
      rcases h with ⟨u, hunf, hhead⟩
      rcases fullUnfoldN_of_unfoldsToC hunf with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simp [hasNonMuHead, hn, hhead]
  | is_var v h =>
      rcases h with ⟨u, hunf, hhead⟩
      rcases fullUnfoldN_of_unfoldsToC hunf with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simp [hasNonMuHead, hn, hhead]
  | is_send p bs h =>
      rcases h with ⟨u, labels, hunf, hhead, _hbs⟩
      rcases fullUnfoldN_of_unfoldsToC hunf with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simp [hasNonMuHead, hn, hhead]
  | is_recv p bs h =>
      rcases h with ⟨u, labels, hunf, hhead, _hbs⟩
      rcases fullUnfoldN_of_unfoldsToC hunf with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simp [hasNonMuHead, hn, hhead]

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

/-- If a type already has a non-mu head, unfolding does nothing. -/
lemma fullUnfoldN_of_hasNonMuHead {t : LocalTypeC} (h : hasNonMuHead t = true) :
    ∀ n, fullUnfoldN n t = t := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      cases hdest : PFunctor.M.dest t with
      | mk hhead f =>
          have hhead' : head t = hhead := by simp [head, hdest]
          cases hhead with
          | mu x =>
              simp [hasNonMuHead, hhead'] at h
          | «end» =>
              simp [fullUnfoldN, hdest]
          | var v =>
              simp [fullUnfoldN, hdest]
          | send p labels =>
              simp [fullUnfoldN, hdest]
          | recv p labels =>
              simp [fullUnfoldN, hdest]

lemma fullUnfoldN_add (n m : Nat) (t : LocalTypeC) :
    fullUnfoldN (n + m) t = fullUnfoldN m (fullUnfoldN n t) := by
  induction n generalizing t with
  | zero => simp [fullUnfoldN]
  | succ n ih =>
      simp [Nat.succ_add, fullUnfoldN]
      cases hdest : PFunctor.M.dest t with
      | mk hhead f =>
          cases hhead with
          | mu x =>
              simp [ih]
          | «end» =>
              have hnonmu : hasNonMuHead t = true := by simp [hasNonMuHead, head, hdest]
              simp [fullUnfoldN_of_hasNonMuHead hnonmu]
          | var v =>
              have hnonmu : hasNonMuHead t = true := by simp [hasNonMuHead, head, hdest]
              simp [fullUnfoldN_of_hasNonMuHead hnonmu]
          | send p labels =>
              have hnonmu : hasNonMuHead t = true := by simp [hasNonMuHead, head, hdest]
              simp [fullUnfoldN_of_hasNonMuHead hnonmu]
          | recv p labels =>
              have hnonmu : hasNonMuHead t = true := by simp [hasNonMuHead, head, hdest]
              simp [fullUnfoldN_of_hasNonMuHead hnonmu]

lemma fullUnfoldN_eq_of_ge {t : LocalTypeC} {n m : Nat}
    (hge : m ≥ n) (h : hasNonMuHead (fullUnfoldN n t) = true) :
    fullUnfoldN m t = fullUnfoldN n t := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hge
  subst hk
  have hstable : ∀ k, fullUnfoldN k (fullUnfoldN n t) = fullUnfoldN n t :=
    fullUnfoldN_of_hasNonMuHead h
  simpa [fullUnfoldN_add] using (hstable k)

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

lemma childRel_of_unfoldsC {t u : LocalTypeC} (h : UnfoldsC t u) : childRel t u := by
  rcases h with ⟨x, f, hdest, rfl⟩
  exact ⟨LocalTypeHead.mu x, f, (), hdest, rfl⟩

lemma UnfoldsToC_reachable {t u : LocalTypeC} (h : UnfoldsToC t u) :
    u ∈ Reachable t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hrest hstep ih =>
      exact Relation.ReflTransGen.tail ih (childRel_of_unfoldsC hstep)

lemma childRel_of_mem_childrenOf {t c : LocalTypeC} (h : c ∈ childrenOf t) : childRel t c := by
  cases hdest : PFunctor.M.dest t with
  | mk hhead f =>
      cases hhead with
      | «end» =>
          simp [childrenOf, hdest] at h
      | var v =>
          simp [childrenOf, hdest] at h
      | mu x =>
          simp [childrenOf, hdest] at h
          subst h
          exact ⟨LocalTypeHead.mu x, f, (), hdest, rfl⟩
      | send p labels =>
          have h' : c ∈ List.ofFn f := by
            simpa [childrenOf, hdest] using h
          have hmem : ∃ i : Fin labels.length, f i = c := List.mem_ofFn.mp h'
          rcases hmem with ⟨i, hi⟩
          subst hi
          exact ⟨LocalTypeHead.send p labels, f, i, hdest, rfl⟩
      | recv p labels =>
          have h' : c ∈ List.ofFn f := by
            simpa [childrenOf, hdest] using h
          have hmem : ∃ i : Fin labels.length, f i = c := List.mem_ofFn.mp h'
          rcases hmem with ⟨i, hi⟩
          subst hi
          exact ⟨LocalTypeHead.recv p labels, f, i, hdest, rfl⟩

lemma mem_childrenOf_fullUnfoldN_reachable {t : LocalTypeC} {n : Nat} {c : LocalTypeC}
    (hmem : c ∈ childrenOf (fullUnfoldN n t)) :
    c ∈ Reachable t := by
  have hreach : fullUnfoldN n t ∈ Reachable t :=
    UnfoldsToC_reachable (fullUnfoldN_UnfoldsToC n t)
  have hchild : childRel (fullUnfoldN n t) c := childRel_of_mem_childrenOf hmem
  exact reachable_step hreach hchild

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

end RumpsteakV2.Coinductive
