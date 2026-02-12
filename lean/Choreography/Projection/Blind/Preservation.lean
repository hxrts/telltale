import Choreography.Projection.Blind.Core

/-! # Choreography.Projection.Blind.Preservation

Step-preservation helper lemmas for blindness.
-/

/-
The Problem. When a global type takes a step (e.g., comm_head selecting a branch,
or mu_unfold substituting), we need blindness to be preserved. Without this,
the projectability guarantee from blindness would not extend through execution.

Solution Structure. We prove preservation lemmas for each step kind:
1. `isBlind_step_comm_head`: stepping into a branch preserves blindness
2. `isBlind_substitute`: substitution (for mu-unfolding) preserves blindness
The key insight is that substitution is uniform across branches.
-/

namespace Choreography.Projection.Blind

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb

section
open Classical

/-! ## Step Preservation Helpers -/

/-- Blindness propagates to branch continuations. -/
theorem isBlind_of_mem_branches {sender receiver : String} {branches : List (Label × GlobalType)}
    (hblind : isBlind (GlobalType.comm sender receiver branches) = true)
    {label : Label} {cont : GlobalType} (hmem : (label, cont) ∈ branches) :
    isBlind cont = true := by
  have hblind_branches := isBlind_comm_branches hblind
  exact hblind_branches (label, cont) hmem

/-- comm_head step preserves blindness: stepping to a branch continuation. -/
theorem isBlind_step_comm_head {sender receiver : String} {branches : List (Label × GlobalType)}
    {label : Label} {cont : GlobalType}
    (hblind : isBlind (GlobalType.comm sender receiver branches) = true)
    (hmem : (label, cont) ∈ branches) :
    isBlind cont = true :=
  isBlind_of_mem_branches hblind hmem

/-! ## Substitution Preservation: Branch Auxiliary -/

/-- Helper: isBlindBranches is preserved by substitution.
    Uses well-founded recursion on branch list size. -/
private theorem isBlindBranches_substitute_aux (bs : List (Label × GlobalType))
    (t : String) (repl : GlobalType) (hrepl : isBlind repl = true)
    (hrepl_closed : repl.isClosed = true)
    (hbs : isBlindBranches bs = true)
    (ih : ∀ g, sizeOf g < sizeOf bs → isBlind g = true → isBlind (g.substitute t repl) = true) :
    isBlindBranches (SessionTypes.GlobalType.substituteBranches bs t repl) = true := by
  match bs with
  | [] => simp [SessionTypes.GlobalType.substituteBranches, isBlindBranches]
  | (label, cont) :: rest =>
      simp only [SessionTypes.GlobalType.substituteBranches, isBlindBranches, Bool.and_eq_true]
      simp only [isBlindBranches, Bool.and_eq_true] at hbs
      constructor
      · have hsize : sizeOf cont < sizeOf ((label, cont) :: rest) := by
          simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
          omega
        exact ih cont hsize hbs.1
      · have hrest_size : ∀ (g : GlobalType), sizeOf g < sizeOf rest →
            sizeOf g < sizeOf ((label, cont) :: rest) := by
          intro g hg
          simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
          omega
        exact isBlindBranches_substitute_aux rest t repl hrepl hrepl_closed hbs.2
          (fun g hg hblind => ih g (hrest_size g hg) hblind)

/-! ## Substitution Preservation: Uniformity Helpers -/

/-! ## Uniformity Helper: Rest -/

/-- Uniformity over branch tails is preserved by substitution. -/
private theorem branchesUniformFor_substitute_rest
    (rest : List (Label × GlobalType)) (cont : GlobalType)
    (role t : String) (repl : GlobalType)
    (hrepl_closed : repl.isClosed = true)
    (hrest_uniform :
      rest.all (fun p => localTypeRBEq (Trans.trans p.2 role) (Trans.trans cont role)) = true) :
    (SessionTypes.GlobalType.substituteBranches rest t repl).all
      (fun p => localTypeRBEq (Trans.trans p.2 role) (Trans.trans (cont.substitute t repl) role)) = true := by
  induction rest with
  | nil =>
      simp [SessionTypes.GlobalType.substituteBranches]
  | cons rhd rtl ih =>
      simp only [SessionTypes.GlobalType.substituteBranches, List.all, Bool.and_eq_true]
      simp only [List.all, Bool.and_eq_true] at hrest_uniform
      constructor
      · apply (localTypeRBEq_eq_true_iff _ _).2
        have heq : Trans.trans rhd.2 role = Trans.trans cont role :=
          localTypeRBEq_eq_true hrest_uniform.1
        have h1 : Trans.trans (rhd.2.substitute t repl) role =
            (Trans.trans rhd.2 role).substitute t (Trans.trans repl role) :=
          ProjSubst.proj_subst rhd.2 t repl role hrepl_closed
        have h2 : Trans.trans (cont.substitute t repl) role =
            (Trans.trans cont role).substitute t (Trans.trans repl role) :=
          ProjSubst.proj_subst cont t repl role hrepl_closed
        rw [h1, h2, heq]
      · exact ih hrest_uniform.2

/-! ## Uniformity Helper: Branches -/

/-- Uniformity on branches is preserved by substitution. -/
private theorem branchesUniformFor_substitute
    (branches : List (Label × GlobalType))
    (role t : String) (repl : GlobalType)
    (hrepl_closed : repl.isClosed = true)
    (horiginal : branchesUniformFor branches role = true) :
    branchesUniformFor (SessionTypes.GlobalType.substituteBranches branches t repl) role = true := by
  simp only [branchesUniformFor] at horiginal ⊢
  cases branches with
  | nil =>
      simp [SessionTypes.GlobalType.substituteBranches]
  | cons head rest =>
      cases head with
      | mk label cont =>
          have hrest_uniform :
              rest.all (fun p => localTypeRBEq (Trans.trans p.2 role) (Trans.trans cont role)) = true := by
            simpa [branchesUniformFor] using horiginal
          simpa [SessionTypes.GlobalType.substituteBranches] using
            branchesUniformFor_substitute_rest rest cont role t repl hrepl_closed hrest_uniform

/-! ## Uniformity Helper: commBlindFor -/

/-- commBlindFor is preserved by uniform substitution in branches. -/
private theorem commBlindFor_substitute
    (sender receiver : String) (branches : List (Label × GlobalType))
    (t : String) (repl : GlobalType)
    (hcomm : commBlindFor sender receiver branches = true)
    (hrepl_closed : repl.isClosed = true) :
    commBlindFor sender receiver (SessionTypes.GlobalType.substituteBranches branches t repl) = true := by
  simp only [commBlindFor]
  rw [decide_eq_true_iff]
  intro role hns hnr
  have horiginal : branchesUniformFor branches role = true := by
    exact (of_decide_eq_true hcomm) role hns hnr
  exact branchesUniformFor_substitute branches role t repl hrepl_closed horiginal

/-! ## Substitution Preservation: Main Theorem -/

/-- Substitution preserves blindness.

    The key insight: substitution is uniform across all branches, so if branches
    projected uniformly before, they project uniformly after. For isBlindBranches,
    we use structural recursion on the branch list.

    Requires `repl.isClosed = true` for the proj_subst theorem used in the
    uniformity preservation argument. This matches the actual use case (mu unfolding). -/
theorem isBlind_substitute (g : GlobalType) (t : String) (repl : GlobalType)
    (hg : isBlind g = true) (hrepl : isBlind repl = true)
    (hrepl_closed : repl.isClosed = true) :
    isBlind (g.substitute t repl) = true := by
  match g with
  | .end =>
      simp [GlobalType.substitute, isBlind]
  | .var s =>
      simp only [GlobalType.substitute]
      split
      · exact hrepl
      · simp [isBlind]
  | .mu s body =>
      simp only [GlobalType.substitute]
      split
      · exact hg
      · simp only [isBlind]
        have hbody : isBlind body = true := isBlind_mu_body hg
        exact isBlind_substitute body t repl hbody hrepl hrepl_closed
  | .comm sender receiver branches =>
      simp only [GlobalType.substitute, isBlind, Bool.and_eq_true]
      have hblind_comm := hg
      simp only [isBlind, Bool.and_eq_true] at hblind_comm
      constructor
      · exact commBlindFor_substitute sender receiver branches t repl hblind_comm.1 hrepl_closed
      · have hsize : ∀ g, sizeOf g < sizeOf branches →
            isBlind g = true → isBlind (g.substitute t repl) = true := by
          intro g hg_size hg_blind
          have hcomm_size : sizeOf branches < sizeOf (GlobalType.comm sender receiver branches) := by
            simp only [GlobalType.comm.sizeOf_spec]
            omega
          have htotal : sizeOf g < sizeOf (GlobalType.comm sender receiver branches) := by
            omega
          exact isBlind_substitute g t repl hg_blind hrepl hrepl_closed
        exact isBlindBranches_substitute_aux branches t repl hrepl hrepl_closed hblind_comm.2 hsize
  | .delegate p q sid r cont =>
      simp only [GlobalType.substitute, isBlind]
      have hcont : isBlind cont = true := isBlind_delegate_cont hg
      exact isBlind_substitute cont t repl hcont hrepl hrepl_closed
termination_by g

/-! ## Step Preservation on Branch Lists -/

/-- BranchesStep preserves isBlindBranches.

    If all branches are blind and they all step via BranchesStep,
    then the resulting branches are also all blind. -/
theorem isBlindBranches_step {branches branches' : List (Label × GlobalType)} {act : GlobalActionR}
    (hstep : BranchesStep step branches act branches')
    (hblind : isBlindBranches branches = true)
    (ih : ∀ g g', step g act g' → isBlind g = true → isBlind g' = true) :
    isBlindBranches branches' = true := by
  induction hstep with
  | nil => simp [isBlindBranches]
  | cons label g g' rest rest' act hstep_g _hstep_rest ih_rest =>
      simp only [isBlindBranches, Bool.and_eq_true] at hblind ⊢
      constructor
      · exact ih g g' hstep_g hblind.1
      · exact ih_rest hblind.2 ih

end

end Choreography.Projection.Blind
