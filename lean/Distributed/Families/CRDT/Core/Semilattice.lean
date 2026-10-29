set_option autoImplicit false

/-! # Distributed.Families.CRDT.Core.Semilattice

State-based CRDT algebra (Shapiro et al., "Conflict-free Replicated Data
Types", 2011): a join-semilattice with bottom. From the lattice laws we prove
that merging is inflationary and monotone, and strong eventual consistency:
replicas that merged the same *set* of states (in any order, with any
duplication) are equal.
-/

/-
The Problem. Convergence was previously stated as join commutativity or as
"same fold of the same list", neither of which captures order/duplication
independence.
Solution Structure. Characterize `mergeAll` as a least upper bound, then
derive convergence for equal delivered sets by antisymmetry.
-/

namespace Distributed
namespace CRDT

universe u

/-! ## Join-Semilattice Structure -/

/-- Reusable state-based CRDT algebra: a join-semilattice with bottom. -/
structure StateBasedCRDT (State : Type u) where
  le : State → State → Prop
  join : State → State → State
  bottom : State
  le_refl : ∀ s, le s s
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  join_left : ∀ a b, le a (join a b)
  join_right : ∀ a b, le b (join a b)
  join_lub : ∀ {a b c}, le a c → le b c → le (join a b) c
  bottom_le : ∀ a, le bottom a

variable {State : Type u} (S : StateBasedCRDT State)

/-- `join a b ≤ c` iff both `a ≤ c` and `b ≤ c`. -/
theorem StateBasedCRDT.join_le_iff {a b c : State} :
    S.le (S.join a b) c ↔ S.le a c ∧ S.le b c :=
  ⟨fun h => ⟨S.le_trans (S.join_left a b) h, S.le_trans (S.join_right a b) h⟩,
    fun h => S.join_lub h.1 h.2⟩

/-- Two states with the same upper bounds are equal. -/
theorem StateBasedCRDT.eq_of_le_iff {a b : State}
    (h : ∀ c, S.le a c ↔ S.le b c) : a = b :=
  S.le_antisymm ((h b).2 (S.le_refl b)) ((h a).1 (S.le_refl a))

/-- Join is commutative (derived from the lub characterization). -/
theorem StateBasedCRDT.join_comm (a b : State) : S.join a b = S.join b a :=
  S.eq_of_le_iff fun c => by rw [S.join_le_iff, S.join_le_iff, And.comm]

/-- Join is associative. -/
theorem StateBasedCRDT.join_assoc (a b c : State) :
    S.join (S.join a b) c = S.join a (S.join b c) :=
  S.eq_of_le_iff fun d => by simp only [S.join_le_iff, and_assoc]

/-- Join is idempotent. -/
theorem StateBasedCRDT.join_idem (a : State) : S.join a a = a :=
  S.eq_of_le_iff fun c => by rw [S.join_le_iff, and_self]

/-- Joining a state already below `b` leaves `b` unchanged (duplicate delivery). -/
theorem StateBasedCRDT.join_of_le {a b : State} (h : S.le a b) : S.join b a = b :=
  S.le_antisymm (S.join_lub (S.le_refl b) h) (S.join_left b a)

/-! ## Merge Properties -/

/-- Merge is inflationary in both inputs. -/
def MergeInflationary : Prop :=
  ∀ a b, S.le a (S.join a b) ∧ S.le b (S.join a b)

/-- Merge is monotone in both inputs. -/
def MergeMonotone : Prop :=
  ∀ {a b c d}, S.le a c → S.le b d → S.le (S.join a b) (S.join c d)

/-- Join laws imply inflationary merge. -/
theorem merge_inflationary_of_state_based_crdt : MergeInflationary S :=
  fun a b => ⟨S.join_left a b, S.join_right a b⟩

/-- Join laws imply merge monotonicity in both inputs. -/
theorem merge_monotone_of_state_based_crdt : MergeMonotone S := by
  intro a b c d hAC hBD
  exact S.join_lub (S.le_trans hAC (S.join_left c d)) (S.le_trans hBD (S.join_right c d))

/-! ## Strong Eventual Consistency -/

/-- Sequentially merge a finite delivered list of states into `base`. -/
def mergeAll (base : State) (updates : List State) : State :=
  updates.foldl S.join base

/-- `mergeAll base l` is the least upper bound of `base` and the members of `l`. -/
theorem mergeAll_le_iff (updates : List State) :
    ∀ (base c : State), S.le (mergeAll S base updates) c ↔
      S.le base c ∧ ∀ x ∈ updates, S.le x c := by
  induction updates with
  | nil => intro base c; simp [mergeAll]
  | cons x xs ih =>
      intro base c
      have h := ih (S.join base x) c
      simp only [mergeAll, List.foldl_cons] at h ⊢
      rw [h, S.join_le_iff]
      simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

/-- Strong eventual consistency: replicas starting from the same base that
merged the same set of updates (any order, any multiplicity) are equal. -/
def StrongEventualConvergence : Prop :=
  ∀ base (l₁ l₂ : List State), (∀ x, x ∈ l₁ ↔ x ∈ l₂) →
    mergeAll S base l₁ = mergeAll S base l₂

/-- Delivery-order independence: permuted delivery of the same updates converges. -/
def FiniteCausalDeliveryConverges : Prop :=
  ∀ base (l₁ l₂ : List State), l₁.Perm l₂ → mergeAll S base l₁ = mergeAll S base l₂

/-- SEC follows from the join-semilattice laws. -/
theorem strong_eventual_convergence_of_state_based_crdt : StrongEventualConvergence S := by
  intro base l₁ l₂ hMem
  apply S.eq_of_le_iff
  intro c
  rw [mergeAll_le_iff, mergeAll_le_iff]
  simp only [hMem]

/-- Permuted delivery converges (a special case of SEC). -/
theorem finite_causal_delivery_converges_of_state_based_crdt :
    FiniteCausalDeliveryConverges S :=
  fun base l₁ l₂ hPerm =>
    strong_eventual_convergence_of_state_based_crdt S base l₁ l₂ fun _ => hPerm.mem_iff

/-! ## Concrete Lattices -/

/-- `Nat` with `max` (a grow-only max register). -/
def natMaxCRDT : StateBasedCRDT Nat where
  le a b := a ≤ b
  join a b := max a b
  bottom := 0
  le_refl := Nat.le_refl
  le_trans := Nat.le_trans
  le_antisymm := Nat.le_antisymm
  join_left := Nat.le_max_left
  join_right := Nat.le_max_right
  join_lub h₁ h₂ := Nat.max_le.mpr ⟨h₁, h₂⟩
  bottom_le := Nat.zero_le

/-- Componentwise product of two state-based CRDTs. -/
def prodCRDT {A : Type u} {B : Type u} (SA : StateBasedCRDT A) (SB : StateBasedCRDT B) :
    StateBasedCRDT (A × B) where
  le p q := SA.le p.1 q.1 ∧ SB.le p.2 q.2
  join p q := (SA.join p.1 q.1, SB.join p.2 q.2)
  bottom := (SA.bottom, SB.bottom)
  le_refl p := ⟨SA.le_refl _, SB.le_refl _⟩
  le_trans h₁ h₂ := ⟨SA.le_trans h₁.1 h₂.1, SB.le_trans h₁.2 h₂.2⟩
  le_antisymm h₁ h₂ := Prod.ext (SA.le_antisymm h₁.1 h₂.1) (SB.le_antisymm h₁.2 h₂.2)
  join_left p q := ⟨SA.join_left _ _, SB.join_left _ _⟩
  join_right p q := ⟨SA.join_right _ _, SB.join_right _ _⟩
  join_lub h₁ h₂ := ⟨SA.join_lub h₁.1 h₂.1, SB.join_lub h₁.2 h₂.2⟩
  bottom_le p := ⟨SA.bottom_le _, SB.bottom_le _⟩

end CRDT
end Distributed
