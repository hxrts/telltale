import SessionTypes.GlobalType.ProductivityLemmas

set_option linter.dupNamespace false

/-! # SessionTypes.GlobalType.Closedness

Closedness predicates, free-variable subset lemmas, closedness preservation,
and GlobalType unfolding definitions.
-/

/-
The Problem. Global types with free type variables can't be projected or executed.
We need a closedness predicate and lemmas showing closedness is preserved by
operations like substitution and mu-unfolding.

Solution Structure. Defines `GlobalType.isClosed` checking if freeVars is empty.
Proves `allVarsBound_implies_freeVars_subset` via mutual recursion on type/branches.
Derives closedness preservation for substitution and unfolding. Provides
GlobalType unfolding definitions for mu-types.
-/

namespace SessionTypes.GlobalType
/-! ## Closedness Predicate (Coq-style)

A global type is closed if it has no free type variables.
This matches Coq's approach and is used for projection preservation. -/

/-- A global type is closed if it has no free type variables. -/
def GlobalType.isClosed (g : GlobalType) : Bool := g.freeVars.isEmpty

-- Helper: allVarsBound implies freeVars are contained in bound list.
-- Uses mutual well-founded recursion on global type/branches size.
mutual
  private def allVarsBound_implies_freeVars_subset_aux (g : GlobalType) (bound : List String)
      (h : g.allVarsBound bound = true) (x : String) (hx : x ∈ g.freeVars) : x ∈ bound :=
    match g with
    | .end => by
        simp only [GlobalType.freeVars, List.not_mem_nil] at hx
    | .var t => by
        simp only [GlobalType.freeVars, List.mem_singleton] at hx
        simp only [GlobalType.allVarsBound] at h
        rw [hx]
        exact List.contains_iff_mem.mp h
    | .comm _ _ branches => by
        simp only [GlobalType.freeVars] at hx
        simp only [GlobalType.allVarsBound] at h
        exact allVarsBoundBranches_implies_freeVars_subset_aux branches bound h x hx
    | .mu t body => by
        simp only [GlobalType.freeVars] at hx
        rw [List.mem_filter] at hx
        simp only [bne_iff_ne, ne_eq] at hx
        have ⟨hxbody, hxnet⟩ := hx
        simp only [GlobalType.allVarsBound] at h
        -- IH gives: x ∈ t :: bound
        have hmem := allVarsBound_implies_freeVars_subset_aux body (t :: bound) h x hxbody
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl hxt => exact absurd hxt hxnet
        | inr hbound => exact hbound
    | .delegate _ _ _ _ cont => by
        simp only [GlobalType.freeVars] at hx
        simp only [GlobalType.allVarsBound] at h
        exact allVarsBound_implies_freeVars_subset_aux cont bound h x hx
  termination_by sizeOf g

  private def allVarsBoundBranches_implies_freeVars_subset_aux
      (branches : List (Label × GlobalType)) (bound : List String)
      (h : GlobalType.allVarsBoundBranches branches bound = true) (x : String)
      (hx : x ∈ GlobalType.freeVarsOfBranches branches) : x ∈ bound :=
    match branches with
    | [] => by
        simp only [GlobalType.freeVarsOfBranches, List.not_mem_nil] at hx
    | (_, cont) :: rest => by
        simp only [GlobalType.freeVarsOfBranches, List.mem_append] at hx
        simp only [GlobalType.allVarsBoundBranches, Bool.and_eq_true] at h
        cases hx with
        | inl hxcont => exact allVarsBound_implies_freeVars_subset_aux cont bound h.1 x hxcont
        | inr hxrest => exact allVarsBoundBranches_implies_freeVars_subset_aux rest bound h.2 x hxrest
  termination_by sizeOf branches
end

/-! ## Closedness and Well-Formedness Lemmas -/

private theorem allVarsBound_nil_implies_freeVars_nil (g : GlobalType)
    (h : g.allVarsBound [] = true) :
    g.freeVars = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have hmem := allVarsBound_implies_freeVars_subset_aux g [] h x hx
  simp only [List.not_mem_nil] at hmem

/-- Well-formed globals are closed (no free variables). -/
theorem GlobalType.isClosed_of_wellFormed (g : GlobalType)
    (hwf : g.wellFormed = true) : g.isClosed = true := by
  -- wellFormed = (((allVarsBound && allCommsNonEmpty) && noSelfComm) && isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  have hbound : g.allVarsBound = true := hwf.1.1.1
  have hfree : g.freeVars = [] := allVarsBound_nil_implies_freeVars_nil g hbound
  simp [GlobalType.isClosed, hfree]

/-! ## Closedness Lemmas

These lemmas establish structural properties of closedness, following the Coq approach
in `coGlobal.v` and `coLocal.v`. The key insight is that:
- `freeVars` for `comm` is the concatenation of branch continuations' free vars
- Substitution with a closed term doesn't introduce new free variables -/

/-- Helper: if a list is empty, all appended sublists must be empty. -/
private theorem freeVarsOfBranches_nil_iff (branches : List (Label × GlobalType)) :
    freeVarsOfBranches branches = [] ↔ ∀ p ∈ branches, p.2.freeVars = [] := by
  induction branches with
  | nil =>
      simp only [freeVarsOfBranches, List.not_mem_nil, false_implies, implies_true]
  | cons hd tl ih =>
      simp only [freeVarsOfBranches, List.append_eq_nil_iff, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro h
        exact ⟨h.1, ih.mp h.2⟩
      · intro h
        exact ⟨h.1, ih.mpr h.2⟩

/-! ## Closedness of Communication Branches -/

/-- A closed comm has closed branch continuations.

If `(comm sender receiver branches).isClosed = true`, then each branch continuation is closed.
This follows directly from the definition: freeVars of comm is the concatenation of branch freeVars.

**Coq reference:** Follows from `gType_fv` definition in `coGlobal.v`. -/
theorem GlobalType.isClosed_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hclosed : (GlobalType.comm sender receiver branches).isClosed = true) :
    ∀ p ∈ branches, p.2.isClosed = true := by
  simp only [GlobalType.isClosed, GlobalType.freeVars, List.isEmpty_iff] at hclosed
  have hbranches := freeVarsOfBranches_nil_iff branches
  intro p hp
  simp only [GlobalType.isClosed, List.isEmpty_iff]
  exact (hbranches.mp hclosed) p hp

/-! ## allCommsNonEmpty Branch Lifting -/

/-- Helper: allCommsNonEmptyBranches ensures each branch has allCommsNonEmpty. -/
private theorem allCommsNonEmptyBranches_forall (branches : List (Label × GlobalType))
    (h : allCommsNonEmptyBranches branches = true) :
    ∀ p ∈ branches, p.2.allCommsNonEmpty = true := by
  induction branches with
  | nil => intro p hp; cases hp
  | cons hd tl ih =>
      simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at h
      intro p hp
      cases hp with
      | head _ => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- A comm with allCommsNonEmpty has all branch continuations with allCommsNonEmpty.

If `(comm sender receiver branches).allCommsNonEmpty = true`, then each branch continuation
has `allCommsNonEmpty = true`. This follows from the definition: allCommsNonEmpty of comm
requires allCommsNonEmptyBranches, which recursively checks each branch. -/
theorem GlobalType.allCommsNonEmpty_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hallcomms : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true) :
    ∀ p ∈ branches, p.2.allCommsNonEmpty = true := by
  simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true] at hallcomms
  exact allCommsNonEmptyBranches_forall branches hallcomms.2

/-! ## noSelfComm Branch Lifting -/

private theorem noSelfCommBranches_forall (branches : List (Label × GlobalType))
    (h : noSelfCommBranches branches = true) :
    ∀ p ∈ branches, p.2.noSelfComm = true := by
  induction branches with
  | nil => intro p hp; cases hp
  | cons hd tl ih =>
      simp only [noSelfCommBranches, Bool.and_eq_true] at h
      intro p hp
      cases hp with
      | head _ => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- A comm with noSelfComm has all branch continuations with noSelfComm. -/
theorem GlobalType.noSelfComm_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hns : (GlobalType.comm sender receiver branches).noSelfComm = true) :
    ∀ p ∈ branches, p.2.noSelfComm = true := by
  simp only [GlobalType.noSelfComm, Bool.and_eq_true] at hns
  exact noSelfCommBranches_forall branches hns.2

/-! ## Productivity and Well-Formed Branch Lifting -/

private theorem isProductiveBranches_forall (branches : List (Label × GlobalType))
    (unguarded : List String)
    (h : isProductiveBranches branches unguarded = true) :
    ∀ p ∈ branches, p.2.isProductive unguarded = true := by
  induction branches with
  | nil => intro p hp; cases hp
  | cons hd tl ih =>
      simp only [isProductiveBranches, Bool.and_eq_true] at h
      intro p hp
      cases hp with
      | head _ => exact h.1
      | tail _ hmem => exact ih h.2 p hmem

/-- A comm that is productive has productive branch continuations. -/
theorem GlobalType.isProductive_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hprod : (GlobalType.comm sender receiver branches).isProductive = true) :
    ∀ p ∈ branches, p.2.isProductive = true := by
  simp only [GlobalType.isProductive] at hprod
  exact isProductiveBranches_forall branches [] hprod

/-- A well-formed comm has well-formed branch continuations. -/
theorem GlobalType.wellFormed_comm_branches (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hwf : (GlobalType.comm sender receiver branches).wellFormed = true) :
    ∀ b ∈ branches, b.2.wellFormed = true := by
  intro b hb
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨hvars, hallcomms⟩, hnoself⟩, hprod⟩ := hwf
  have hvars_b : b.2.allVarsBound = true :=
    allVarsBound_comm_branches sender receiver branches hvars b hb
  have hallcomms_b : b.2.allCommsNonEmpty = true :=
    GlobalType.allCommsNonEmpty_comm_branches sender receiver branches hallcomms b hb
  have hnoself_b : b.2.noSelfComm = true :=
    GlobalType.noSelfComm_comm_branches sender receiver branches hnoself b hb
  have hprod_b : b.2.isProductive = true :=
    GlobalType.isProductive_comm_branches sender receiver branches hprod b hb
  simp [GlobalType.wellFormed, hvars_b, hallcomms_b, hnoself_b, hprod_b]


end SessionTypes.GlobalType
