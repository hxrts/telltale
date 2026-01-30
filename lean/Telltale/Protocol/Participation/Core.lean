import Mathlib.Logic.Function.Iterate
import Telltale.Protocol.GlobalType

/-!
The Problem. Define participation predicates that let projection proofs
distinguish between participants (roles that appear on some communication path)
and non-participants, and connect those predicates to branch-wise participation.

Solution Structure. We build one-step generators (`part_ofF`, `part_of_allF`),
take greatest fixed points to obtain `part_of2` and `part_of_all2`, and then
prove equivalence lemmas and classification results used throughout the projection
and safety proofs.
-/

/-! # Telltale.Protocol.Participation

Participation predicates for projection proofs.

These predicates classify whether a role is a "participant" in a global protocol
(appears on a communication path) or a "non-participant" (not involved in any
communication). This classification is crucial for projection soundness proofs.

## Expose

The following definitions form the semantic interface for proofs:

- `part_of2`: role participates in the protocol (exists path to communication)
- `part_of_all2`: role participates on all branches (for coherence proofs)
- `part_of2_or_not`: classification lemma (participant or not)
- `comp_dir`: direction of participation (sender, receiver, or none)
-/

namespace Telltale.Protocol.Participation

open Telltale.Protocol.GlobalType

/-- Direction of participation: sender, receiver, or non-participant. -/
inductive Dir where
  | sender : Dir
  | receiver : Dir
  deriving Repr, DecidableEq, Inhabited

/-- Compute participation direction for a role in a communication.
    Returns `some sender` if role is the sender, `some receiver` if role
    is the receiver, `none` if the role is not a direct participant. -/
def comp_dir (role : String) (sender receiver : String) : Option Dir :=
  if role == sender then some .sender
  else if role == receiver then some .receiver
  else none

/-- Helper: check if role participates as sender or receiver. -/
def is_participant (role : String) (sender receiver : String) : Bool :=
  role == sender || role == receiver

/-! ## One-step participation (part_ofF)

The one-step predicate captures when a role directly participates at the
top level of a global type, or when a recursive predicate R holds on
the continuation. -/

/-- One-step participation predicate.
    `R` is the recursive predicate for continuations. -/
inductive part_ofF (role : String) (R : GlobalType → Prop) : GlobalType → Prop where
  /-- Direct participation: role is sender or receiver of this communication. -/
  | comm_direct (sender receiver : String) (branches : List (Label × GlobalType)) :
      is_participant role sender receiver →
      part_ofF role R (.comm sender receiver branches)
  /-- Transitive participation: role participates in some continuation. -/
  | comm_branch (sender receiver : String) (label : Label) (cont : GlobalType)
      (branches : List (Label × GlobalType)) :
      (label, cont) ∈ branches →
      R cont →
      part_ofF role R (.comm sender receiver branches)
  /-- Participation through mu unfolding. -/
  | mu (t : String) (body : GlobalType) :
      R body →
      part_ofF role R (.mu t body)

/-- One-step participation on all branches (forall instead of exists). -/
inductive part_of_allF (role : String) (R : GlobalType → Prop) : GlobalType → Prop where
  /-- Direct participation: role is sender or receiver. -/
  | comm_direct (sender receiver : String) (branches : List (Label × GlobalType)) :
      is_participant role sender receiver →
      part_of_allF role R (.comm sender receiver branches)
  /-- Transitive participation through ALL branches. -/
  | comm_all_branches (sender receiver : String) (branches : List (Label × GlobalType)) :
      (∀ pair, pair ∈ branches → R pair.2) →
      part_of_allF role R (.comm sender receiver branches)
  /-- Participation through mu unfolding. -/
  | mu (t : String) (body : GlobalType) :
      R body →
      part_of_allF role R (.mu t body)

/-! ## Transitive participation (part_of2)

The inductive predicate captures role participation at any depth in
the global type, allowing unfolding through mu types and following
communication branches. -/

/-- Role participates in the global type (exists a path to communication). -/
inductive part_of2 (role : String) : GlobalType → Prop where
  | intro (g : GlobalType) :
      part_ofF role (part_of2 role) g →
      part_of2 role g

/-- Role participates through all branches (for coherence/uniformity). -/
inductive part_of_all2 (role : String) : GlobalType → Prop where
  | intro (g : GlobalType) :
      part_of_allF role (part_of_all2 role) g →
      part_of_all2 role g

/-! ## Inversion lemmas for part_of2 -/

theorem part_of2_comm_inv {role sender receiver : String} {branches : List (Label × GlobalType)}
    (h : part_of2 role (.comm sender receiver branches)) :
    is_participant role sender receiver ∨
    ∃ label cont, (label, cont) ∈ branches ∧ part_of2 role cont := by
  cases h with
  | intro _ hf =>
      cases hf with
      | comm_direct _ _ _ hpart =>
          left; exact hpart
      | comm_branch _ _ label cont _ hmem hcont =>
          right; exact ⟨label, cont, hmem, hcont⟩

theorem part_of2_mu_inv {role t : String} {body : GlobalType}
    (h : part_of2 role (.mu t body)) :
    part_of2 role body := by
  cases h with
  | intro _ hf =>
      cases hf with
      | mu _ _ hbody => exact hbody

/-- End and var types have no participants. -/
theorem not_part_of2_end (role : String) : ¬ part_of2 role .end := by
  intro h
  cases h with
  | intro _ hf => cases hf

theorem not_part_of2_var (role : String) (t : String) : ¬ part_of2 role (.var t) := by
  intro h
  cases h with
  | intro _ hf => cases hf

/-! ## part_of_all2 inversion lemmas -/

theorem part_of_all2_comm_inv {role sender receiver : String} {branches : List (Label × GlobalType)}
    (h : part_of_all2 role (.comm sender receiver branches)) :
    is_participant role sender receiver ∨
    ∀ pair, pair ∈ branches → part_of_all2 role pair.2 := by
  cases h with
  | intro _ hf =>
      cases hf with
      | comm_direct _ _ _ hpart =>
          left; exact hpart
      | comm_all_branches _ _ _ hall =>
          right; exact hall

theorem part_of_all2_mu_inv {role t : String} {body : GlobalType}
    (h : part_of_all2 role (.mu t body)) :
    part_of_all2 role body := by
  cases h with
  | intro _ hf =>
      cases hf with
      | mu _ _ hbody => exact hbody

/-- End and var types have no participants. -/
theorem not_part_of_all2_end (role : String) : ¬ part_of_all2 role .end := by
  intro h
  cases h with
  | intro _ hf => cases hf

theorem not_part_of_all2_var (role : String) (t : String) : ¬ part_of_all2 role (.var t) := by
  intro h
  cases h with
  | intro _ hf => cases hf

private theorem sizeOf_bs_lt_comm (sender receiver : String) (bs : List (Label × GlobalType)) :
    sizeOf bs < sizeOf (GlobalType.comm sender receiver bs) := by
  simp only [GlobalType.comm.sizeOf_spec]
  have h : 0 < 1 + sizeOf sender + sizeOf receiver := by omega
  omega

private theorem sizeOf_elem_snd_lt_list {α β : Type _} [SizeOf α] [SizeOf β]
    (xs : List (α × β)) (x : α × β) (h : x ∈ xs) :
    sizeOf x.2 < sizeOf xs := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
      have hmem := (List.mem_cons).1 h
      cases hmem with
      | inl hEq =>
          cases hEq
          simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]; omega
      | inr hmem =>
          have := ih hmem
          simp only [sizeOf, List._sizeOf_1] at *
          omega

private theorem sizeOf_elem_snd_lt_comm (sender receiver : String)
    (gbs : List (Label × GlobalType)) (gb : Label × GlobalType) (h : gb ∈ gbs) :
    sizeOf gb.2 < sizeOf (GlobalType.comm sender receiver gbs) := by
  have h1 := sizeOf_elem_snd_lt_list gbs gb h
  have h2 := sizeOf_bs_lt_comm sender receiver gbs
  omega

private theorem sizeOf_body_lt_mu (t : String) (body : GlobalType) :
    sizeOf body < sizeOf (GlobalType.mu t body) := by
  have hk : 0 < 1 + sizeOf t := by
    simp only [Nat.one_add]
    exact Nat.succ_pos (sizeOf t)
  have h : sizeOf body < (1 + sizeOf t) + sizeOf body :=
    Nat.lt_add_of_pos_left (n := sizeOf body) (k := 1 + sizeOf t) hk
  simp only [sizeOf, GlobalType._sizeOf_1]
  omega

/-! ## Induction principle for part_of_all2

This mirrors the Coq `part_of_all2_ind2` lemma used in projection proofs.
It gives a structural recursion on the global type, with explicit cases
for direct participation, all-branches participation, and mu unfolding. -/

private abbrev CommDirect (role : String) (P : GlobalType → Prop) : Prop :=
  -- Direct comm participation hypothesis.
  ∀ sender receiver branches, is_participant role sender receiver →
    P (.comm sender receiver branches)

private abbrev CommAll (role : String) (P : GlobalType → Prop) : Prop :=
  -- All-branches comm participation hypothesis.
  ∀ sender receiver branches,
    (∀ pair, pair ∈ branches → part_of_all2 role pair.2) →
    (∀ pair, pair ∈ branches → part_of_all2 role pair.2 → P pair.2) →
    P (.comm sender receiver branches)

theorem part_of_all2_ind2 (role : String) (P : GlobalType → Prop)
    (h_comm_direct : CommDirect role P)
    (h_comm_all : CommAll role P)
    (h_mu : ∀ t body, part_of_all2 role body → P body → P (.mu t body)) :
    ∀ g, part_of_all2 role g → P g := by
  intro g h
  match g with  -- structural recursion on g
  | .end => exact (not_part_of_all2_end role h).elim
  | .var t => exact (not_part_of_all2_var role t h).elim
  | .mu t body =>
      have hbody : part_of_all2 role body := part_of_all2_mu_inv h
      have ih : P body :=
        part_of_all2_ind2 role P h_comm_direct h_comm_all h_mu body hbody
      exact h_mu t body hbody ih
  | .comm sender receiver branches =>
      have hcases := part_of_all2_comm_inv (role := role) (sender := sender)
        (receiver := receiver) (branches := branches) h
      cases hcases with
      | inl hpart =>
          exact h_comm_direct sender receiver branches hpart
      | inr hall =>
          have ih :
              ∀ pair, pair ∈ branches → part_of_all2 role pair.2 → P pair.2 := by
            intro pair hmem hpoa
            exact part_of_all2_ind2 role P h_comm_direct h_comm_all h_mu pair.2 hpoa
          exact h_comm_all sender receiver branches hall ih
termination_by g _ => sizeOf g
decreasing_by
  all_goals
    simp_wf
    try
      (simpa [GlobalType.comm.sizeOf_spec] using
        (sizeOf_elem_snd_lt_comm _ _ _ _ (by assumption)))
    try
      (simp only [sizeOf, GlobalType._sizeOf_1] at *; omega)

/-! ## Non-participation lemmas

These lemmas capture what we can conclude when a role is NOT a participant. -/

/-- If role doesn't participate in a comm, it doesn't directly participate and
    doesn't participate in any continuation. -/
theorem not_part_of2_comm {role sender receiver : String} {branches : List (Label × GlobalType)}
    (h : ¬ part_of2 role (.comm sender receiver branches)) :
    ¬ is_participant role sender receiver ∧
    ∀ pair, pair ∈ branches → ¬ part_of2 role pair.2 := by
  constructor
  · intro hpart
    apply h
    exact .intro _ (.comm_direct _ _ _ hpart)
  · intro pair hmem hcont
    apply h
    exact .intro _ (.comm_branch _ _ pair.1 pair.2 _ hmem hcont)

/-- If role doesn't participate in mu, it doesn't participate in body. -/
theorem not_part_of2_mu {role t : String} {body : GlobalType}
    (h : ¬ part_of2 role (.mu t body)) :
    ¬ part_of2 role body := by
  intro hbody
  apply h
  exact .intro _ (.mu _ _ hbody)

end Telltale.Protocol.Participation
