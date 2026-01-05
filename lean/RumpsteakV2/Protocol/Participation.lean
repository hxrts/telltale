import RumpsteakV2.Protocol.GlobalType

/-! # RumpsteakV2.Protocol.Participation

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

namespace RumpsteakV2.Protocol.Participation

open RumpsteakV2.Protocol.GlobalType

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

/-! ## Classification: participant or non-participant

This is the key lemma used in projection proofs. For closed, well-formed
global types, a role either:
1. Participates (part_of_all2 holds), or
2. Does not participate (and trans projects to EEnd)

Note: This requires well-formedness and closedness assumptions in the
full proof. We provide a simpler decidable version for finite global types. -/

mutual
  /-- Decidable participation check (for finite, unguarded global types).
      For recursive types, this only checks the body once to avoid divergence. -/
  def participates (role : String) : GlobalType → Bool
    | .end => false
    | .var _ => false
    | .mu _ body => participates role body
    | .comm sender receiver branches =>
        is_participant role sender receiver ||
        participatesBranches role branches

  /-- Helper for participates on branches. -/
  def participatesBranches (role : String) : List (Label × GlobalType) → Bool
    | [] => false
    | (_, cont) :: rest =>
        participates role cont || participatesBranches role rest
end

theorem participates_comm_iff {role sender receiver : String} {branches : List (Label × GlobalType)} :
    participates role (.comm sender receiver branches) =
      (is_participant role sender receiver || participatesBranches role branches) := by
  rfl

theorem participates_mu_iff {role t : String} {body : GlobalType} :
    participates role (.mu t body) = participates role body := by
  rfl

/-- If participates returns false, the role is not a direct participant. -/
theorem not_participates_imp_not_participant {role sender receiver : String}
    {branches : List (Label × GlobalType)}
    (h : participates role (.comm sender receiver branches) = false) :
    ¬ is_participant role sender receiver := by
  simp only [participates, Bool.or_eq_false_iff] at h
  exact Bool.eq_false_iff.mp h.1

end RumpsteakV2.Protocol.Participation
