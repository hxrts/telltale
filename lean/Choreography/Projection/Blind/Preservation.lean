import Choreography.Projection.Blind.Core

/-! # Choreography.Projection.Blind.Preservation

Step-preservation helper lemmas for blindness.
-/

namespace Choreography.Projection.Blind

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb

noncomputable section
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
      · -- isBlind (cont.substitute t repl)
        have hsize : sizeOf cont < sizeOf ((label, cont) :: rest) := by
          simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
          omega
        exact ih cont hsize hbs.1
      · -- isBlindBranches (substituteBranches rest t repl)
        have hrest_size : ∀ (g : GlobalType), sizeOf g < sizeOf rest →
            sizeOf g < sizeOf ((label, cont) :: rest) := by
          intro g hg
          simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
          omega
        exact isBlindBranches_substitute_aux rest t repl hrepl hrepl_closed hbs.2
          (fun g hg hblind => ih g (hrest_size g hg) hblind)

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
  | .end => simp [GlobalType.substitute, isBlind]
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
      · -- commBlindFor preserved: uniformity is preserved under uniform substitution
        simp only [commBlindFor]
        rw [decide_eq_true_iff]
        intro role hns hnr
        have horiginal : branchesUniformFor branches role = true := by
          have hdec := of_decide_eq_true hblind_comm.1
          exact hdec role hns hnr
        -- Show uniformity is preserved under substitution
        simp only [branchesUniformFor] at horiginal ⊢
        cases hbranches : SessionTypes.GlobalType.substituteBranches branches t repl with
        | nil => simp
        | cons head' rest' =>
            -- The substituted branches have the same structure
            cases horiginal_branches : branches with
            | nil =>
                -- branches = [] means substituteBranches = []
                simp [SessionTypes.GlobalType.substituteBranches, horiginal_branches] at hbranches
            | cons head rest =>
                cases head with
                | mk label cont =>
                    -- substituteBranches ((l,c)::rest) = (l, c.sub)::substituteBranches rest
                    simp [SessionTypes.GlobalType.substituteBranches, horiginal_branches] at hbranches
                    cases head' with
                    | mk label' cont' =>
                        simp only [Prod.mk.injEq] at hbranches
                        have hlabel : label' = label := hbranches.1.1.symm
                        have hcont : cont' = cont.substitute t repl := hbranches.1.2.symm
                        have hrest' : rest' = SessionTypes.GlobalType.substituteBranches rest t repl := hbranches.2.symm
                        subst hlabel hcont hrest'
                        -- Need: rest'.all (fun p => decide (trans p.2 role = trans cont' role))
                        -- Original: rest.all (fun p => decide (trans p.2 role = trans cont role)) = true
                        have hrest_uniform : rest.all (fun p => decide (Trans.trans p.2 role = Trans.trans cont role)) = true := by
                          simpa [branchesUniformFor, horiginal_branches] using horiginal
                        -- For each p in rest, trans p.2 role = trans cont role
                        -- After substitution, for each p' in rest', trans p'.2 role = trans cont' role
                        -- where p'.2 = p.2.substitute t repl and cont' = cont.substitute t repl
                        -- This follows if substitution commutes with trans uniformly
                        -- Since all original projections are equal, and substitution is uniform,
                        -- all substituted projections are also equal
                        clear horiginal hbranches horiginal_branches hblind_comm hg
                        induction rest with
                        | nil => simp [SessionTypes.GlobalType.substituteBranches]
                        | cons rhd rtl ih_rest =>
                            simp only [SessionTypes.GlobalType.substituteBranches, List.all, Bool.and_eq_true]
                            simp only [List.all, Bool.and_eq_true] at hrest_uniform
                            constructor
                            · -- decide (trans (rhd.2.substitute t repl) role = trans (cont.substitute t repl) role)
                              rw [decide_eq_true_iff]
                              -- From hrest_uniform.1: trans rhd.2 role = trans cont role
                              have heq : Trans.trans rhd.2 role = Trans.trans cont role := of_decide_eq_true hrest_uniform.1
                              -- Use proj_subst to show substitution commutes with trans
                              have h1 : Trans.trans (rhd.2.substitute t repl) role =
                                  (Trans.trans rhd.2 role).substitute t (Trans.trans repl role) :=
                                ProjSubst.proj_subst rhd.2 t repl role hrepl_closed
                              have h2 : Trans.trans (cont.substitute t repl) role =
                                  (Trans.trans cont role).substitute t (Trans.trans repl role) :=
                                ProjSubst.proj_subst cont t repl role hrepl_closed
                              -- Since trans rhd.2 role = trans cont role, the substituted results are equal
                              rw [h1, h2, heq]
                            · exact ih_rest hrest_uniform.2
      · -- isBlindBranches preserved
        have hsize : ∀ g, sizeOf g < sizeOf branches →
            isBlind g = true → isBlind (g.substitute t repl) = true := by
          intro g hg_size hg_blind
          have hcomm_size : sizeOf branches < sizeOf (GlobalType.comm sender receiver branches) := by
            simp only [GlobalType.comm.sizeOf_spec]
            omega
          have htotal : sizeOf g < sizeOf (GlobalType.comm sender receiver branches) := by
            omega
          exact isBlind_substitute g t repl hg_blind hrepl hrepl_closed
        exact isBlindBranches_substitute_aux branches t repl hrepl hrepl_closed hblind_comm.2 hsize
termination_by g

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
