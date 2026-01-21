import Mathlib.Logic.Function.Iterate
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

/-! ## Induction principle for part_of_all2

This mirrors the Coq `part_of_all2_ind2` lemma used in projection proofs.
It gives a structural recursion on the global type, with explicit cases
for direct participation, all-branches participation, and mu unfolding. -/

theorem part_of_all2_ind2 (role : String) (P : GlobalType → Prop)
    (h_comm_direct :
      ∀ sender receiver branches, is_participant role sender receiver →
        P (.comm sender receiver branches))
    (h_comm_all :
      ∀ sender receiver branches,
        (∀ pair, pair ∈ branches → part_of_all2 role pair.2) →
        (∀ pair, pair ∈ branches → part_of_all2 role pair.2 → P pair.2) →
        P (.comm sender receiver branches))
    (h_mu :
      ∀ t body, part_of_all2 role body → P body → P (.mu t body)) :
    ∀ g, part_of_all2 role g → P g := by
  intro g h
  match g with
  | .end =>
      exact (not_part_of_all2_end role h).elim
  | .var t =>
      exact (not_part_of_all2_var role t h).elim
  | .mu t body =>
      have hbody : part_of_all2 role body := part_of_all2_mu_inv h
      have ih : P body := part_of_all2_ind2 role P h_comm_direct h_comm_all h_mu body hbody
      exact h_mu t body hbody ih
  | .comm sender receiver branches =>
      have hcases := part_of_all2_comm_inv (role := role) (sender := sender) (receiver := receiver)
        (branches := branches) h
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
    all_goals
      first
      | (simpa [GlobalType.comm.sizeOf_spec] using
          (sizeOf_elem_snd_lt_comm _ _ _ _ (by assumption)))
      | (simp only [sizeOf, GlobalType._sizeOf_1] at *; omega)

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

/-! ## Participation and substitution/unfolding

These lemmas show that participation is preserved under unfolding. They are
useful for reasoning about `fullUnfoldIter` in projection proofs. -/

private theorem mem_substituteBranches_iff
    {branches : List (Label × GlobalType)} {t : String} {repl : GlobalType}
    {label : Label} {cont' : GlobalType} :
    (label, cont') ∈ GlobalType.substituteBranches branches t repl ↔
      ∃ cont, cont' = cont.substitute t repl ∧ (label, cont) ∈ branches := by
  induction branches with
  | nil =>
      simp [GlobalType.substituteBranches]
  | cons head tail ih =>
      cases head with
      | mk hlabel hcont =>
          constructor
          · intro hmem
            have hmem' :
                (label, cont') = (hlabel, hcont.substitute t repl) ∨
                  (label, cont') ∈ GlobalType.substituteBranches tail t repl := by
              simpa [GlobalType.substituteBranches] using (List.mem_cons).1 hmem
            cases hmem' with
            | inl hEq =>
                cases hEq
                exact ⟨hcont, rfl, by simp⟩
            | inr hmemTail =>
                rcases (ih.mp hmemTail) with ⟨cont, hcont_eq, hmem''⟩
                exact ⟨cont, hcont_eq, by simp [hmem'']⟩
          · rintro ⟨cont, hcont_eq, hmem⟩
            have hmem' :
                (label, cont) = (hlabel, hcont) ∨ (label, cont) ∈ tail := by
              simpa using (List.mem_cons).1 hmem
            cases hmem' with
            | inl hEq =>
                cases hEq
                -- head case
                simp [GlobalType.substituteBranches, hcont_eq]
            | inr hmemTail =>
                have hmemSub :
                    (label, cont') ∈ GlobalType.substituteBranches tail t repl :=
                  ih.mpr ⟨cont, hcont_eq, hmemTail⟩
                exact List.mem_cons_of_mem _ hmemSub

theorem part_of2_substitute (role : String) :
    ∀ g t repl, part_of2 role (g.substitute t repl) →
      part_of2 role g ∨ part_of2 role repl := by
  intro g t repl h
  match g with
  | .end =>
      exact (not_part_of2_end role h).elim
  | .var v =>
      by_cases hvt : v = t
      · right
        simpa [GlobalType.substitute, hvt] using h
      · exact (not_part_of2_var role v (by simpa [GlobalType.substitute, hvt] using h)).elim
  | .comm sender receiver branches =>
      have hcases := part_of2_comm_inv (role := role)
        (sender := sender) (receiver := receiver) (branches := GlobalType.substituteBranches branches t repl) h
      cases hcases with
      | inl hpart =>
          left
          exact .intro _ (.comm_direct _ _ _ hpart)
      | inr hbranch =>
          rcases hbranch with ⟨label, cont', hmem, hcont'⟩
          rcases (mem_substituteBranches_iff.mp hmem) with ⟨cont, hcont_eq, hmem'⟩
          have hcont_subst : part_of2 role (cont.substitute t repl) := by
            simpa [hcont_eq] using hcont'
          have hih := part_of2_substitute role cont t repl hcont_subst
          cases hih with
          | inl hcont =>
              left
              exact .intro _ (.comm_branch _ _ label cont branches hmem' hcont)
          | inr hrepl =>
              right
              exact hrepl
  | .mu s body =>
      by_cases hst : s = t
      · left
        simpa [GlobalType.substitute, hst] using h
      · have hbody : part_of2 role (body.substitute t repl) := by
          have hmu : part_of2 role (.mu s (body.substitute t repl)) := by
            simpa [GlobalType.substitute, hst] using h
          exact part_of2_mu_inv hmu
        have hih := part_of2_substitute role body t repl hbody
        cases hih with
        | inl hbody_part =>
            left
            exact .intro _ (.mu _ _ hbody_part)
        | inr hrepl =>
            right
            exact hrepl
termination_by g _ _ _ => sizeOf g
decreasing_by
  all_goals
    simp_wf
    all_goals
      first
      | (simpa [GlobalType.comm.sizeOf_spec] using
          (sizeOf_elem_snd_lt_comm _ _ _ _ (by assumption)))
      | (simp only [sizeOf, GlobalType._sizeOf_1] at *; omega)

theorem part_of2_unfold (role : String) (g : GlobalType) :
    part_of2 role (GlobalType.unfold g) → part_of2 role g := by
  cases g with
  | «end» =>
      intro h
      simpa [GlobalType.unfold] using h
  | var v =>
      intro h
      simpa [GlobalType.unfold] using h
  | comm sender receiver branches =>
      intro h
      simpa [GlobalType.unfold] using h
  | mu t body =>
      intro h
      have hsub : part_of2 role (body.substitute t (.mu t body)) := by
        simpa [GlobalType.unfold] using h
      have hcases := part_of2_substitute role body t (.mu t body) hsub
      cases hcases with
      | inl hbody =>
          exact .intro _ (.mu _ _ hbody)
      | inr hmu =>
          exact hmu

theorem part_of2_unfold_iter (role : String) (g : GlobalType) :
    ∀ n, part_of2 role (Nat.rec g (fun _ acc => GlobalType.unfold acc) n) → part_of2 role g := by
  intro n
  induction n generalizing g with
  | zero =>
      intro h
      simpa using h
  | succ n ih =>
      intro h
      have h' : part_of2 role (GlobalType.unfold (Nat.rec g (fun _ acc => GlobalType.unfold acc) n)) := by
        simpa using h
      have h'' : part_of2 role (Nat.rec g (fun _ acc => GlobalType.unfold acc) n) :=
        part_of2_unfold role (Nat.rec g (fun _ acc => GlobalType.unfold acc) n) h'
      exact ih (g := g) h''

theorem part_of2_fullUnfoldIter (role : String) (g : GlobalType) :
    part_of2 role (GlobalType.fullUnfoldIter g) → part_of2 role g := by
  simpa [GlobalType.fullUnfoldIter] using
    (part_of2_unfold_iter role g g.muHeight)

theorem not_part_of2_fullUnfoldIter (role : String) (g : GlobalType)
    (h : ¬ part_of2 role g) : ¬ part_of2 role (GlobalType.fullUnfoldIter g) := by
  intro hfull
  exact h (part_of2_fullUnfoldIter role g hfull)

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

/-! ## Boolean participation equivalence -/

mutual
  /-- `participates` is equivalent to `part_of2`. -/
  theorem part_of2_iff_participates (role : String) :
      ∀ g, part_of2 role g ↔ participates role g = true := by
    intro g
    cases g with
    | «end» =>
        constructor
        · intro h; exact (not_part_of2_end role h).elim
        · intro h; simp [participates] at h
    | var t =>
        constructor
        · intro h; exact (not_part_of2_var role t h).elim
        · intro h; simp [participates] at h
    | mu t body =>
        constructor
        · intro h
          have hbody : part_of2 role body := part_of2_mu_inv (t := t) h
          have ih := (part_of2_iff_participates role body).1 hbody
          simpa [participates] using ih
        · intro h
          simp [participates] at h
          have hbody : part_of2 role body :=
            (part_of2_iff_participates role body).2 h
          exact .intro _ (.mu _ _ hbody)
    | comm sender receiver branches =>
        constructor
        · intro h
          have hcases := part_of2_comm_inv (role := role) (sender := sender) (receiver := receiver)
            (branches := branches) h
          cases hcases with
          | inl hpart =>
              have hpart' : is_participant role sender receiver = true := by
                simpa using hpart
              simp [participates, hpart']  -- left disjunct
          | inr hbranch =>
              obtain ⟨label, cont, hmem, hcont⟩ := hbranch
              have hbranches :
                  participatesBranches role branches = true := by
                have hexists : ∃ pair, pair ∈ branches ∧ part_of2 role pair.2 :=
                  ⟨(label, cont), hmem, hcont⟩
                exact (participatesBranches_iff_part_of2 role branches).2 hexists
              simp [participates, hbranches]
        · intro h
          simp [participates] at h
          cases h with
          | inl hpart =>
              -- direct participation
              exact .intro _ (.comm_direct _ _ _ hpart)
          | inr hbranches =>
              -- participation through a branch
              have hexists :
                  ∃ pair, pair ∈ branches ∧ part_of2 role pair.2 :=
                (participatesBranches_iff_part_of2 role branches).1 hbranches
              obtain ⟨pair, hmem, hcont⟩ := hexists
              exact .intro _ (.comm_branch _ _ pair.1 pair.2 _ hmem hcont)

  /-- `participatesBranches` is equivalent to existence of a participating branch. -/
  theorem participatesBranches_iff_part_of2 (role : String) :
      ∀ branches,
        participatesBranches role branches = true ↔
          ∃ pair, pair ∈ branches ∧ part_of2 role pair.2 := by
    intro branches
    cases branches with
    | nil =>
        simp [participatesBranches]
    | cons hd tl =>
        obtain ⟨label, cont⟩ := hd
        constructor
        · intro h
          simp [participatesBranches, Bool.or_eq_true] at h
          cases h with
          | inl hcont =>
              have hpo : part_of2 role cont :=
                (part_of2_iff_participates role cont).2 hcont
              exact ⟨(label, cont), by simp, hpo⟩
          | inr hrest =>
              have hrest' :=
                (participatesBranches_iff_part_of2 role tl).1 hrest
              obtain ⟨pair, hmem, hpo⟩ := hrest'
              exact ⟨pair, by simp [hmem], hpo⟩
        · intro h
          obtain ⟨pair, hmem, hpo⟩ := h
          simp [participatesBranches]  -- reduces to head/tail cases
          have hmem' := (List.mem_cons).1 hmem
          cases hmem' with
          | inl hEq =>
              cases hEq
              have hcont : participates role cont = true :=
                (part_of2_iff_participates role cont).1 hpo
              exact Or.inl hcont
          | inr hmemTail =>
              have hrest :
                  participatesBranches role tl = true :=
                (participatesBranches_iff_part_of2 role tl).2 ⟨pair, hmemTail, hpo⟩
              exact Or.inr hrest
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
