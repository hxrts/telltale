import Choreography.Projection.Project.Core
import Choreography.Projection.Projectb
import SessionTypes.Participation
import SessionCoTypes.EQ2
import SessionCoTypes.EQ2Props

/-! # Choreography.Projection.Project.Muve

Muve (mu-var-end) infrastructure and non-participant projection results.

## Expose

The following definitions form the semantic interface for proofs:

- `isMuve`: mu-var-end predicate on local types
- `EQ_end`: non-participants project to EEnd (EQ2)
- `CProject_muve_of_not_part_of2`: non-participant projections are muve
- `part_of2_or_end`: participant-or-end classification
-/

/-
The Problem. Non-participants project to mu-var-end chains. We need a reusable
library that connects muve structure, closedness, and EQ2-equivalence to .end.

Solution Structure. Build muve lemmas, show closed muve types are EQ2 to .end,
then use CProject structure + participation to classify roles as participating
or end-producing.
-/

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Projectb
open SessionTypes.Participation
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props

/-! ## Muve Types: mu-var-end chains

A "muve" (mu-var-end) type is a local type that consists only of mu-wrappers
around end or var constructors. These types arise from projecting non-participants:
the trans function produces muve types when the role doesn't participate.

Key property: closed muve types (no free variables) are EQ2-equivalent to .end. -/

/-- A local type is "muve" if it consists only of mu/var/end constructors.
    Such types arise from projecting non-participants. -/
def isMuve : LocalTypeR → Bool
  | .end => true
  | .var _ => true
  | .mu _ body => isMuve body
  | .send _ _ => false
  | .recv _ _ => false

/-- If a local type is unguarded at some variable, it must be a muve type. -/
theorem isMuve_of_not_guarded : ∀ lt v, lt.isGuarded v = false → isMuve lt = true
  | .end, _, _ => by simp [isMuve]
  | .var _, _, _ => by simp [isMuve]
  | .send _ _, _, h => by
      have : False := by
        simp [LocalTypeR.isGuarded] at h
      exact False.elim this
  | .recv _ _, _, h => by
      have : False := by
        simp [LocalTypeR.isGuarded] at h
      exact False.elim this
  | .mu t body, v, h => by
      by_cases htv : v == t
      · have : False := by
          simp [LocalTypeR.isGuarded, htv] at h
        exact False.elim this
      · have hbody : body.isGuarded v = false := by
          simp [LocalTypeR.isGuarded, htv] at h
          exact h
        have ih' := isMuve_of_not_guarded body v hbody
        simp [isMuve, ih']

/-- A local type is closed if it has no free variables. -/
def isClosed (lt : LocalTypeR) : Bool := lt.freeVars == []

/-! ## FreeVars lemmas for substitution -/
/-! ## Substitution Free-Variable Base Helpers -/
private theorem freeVars_substitute_subset_end (varName : String) (repl : LocalTypeR)
    (x : String) (hx : x ∈ (LocalTypeR.end.substitute varName repl).freeVars) :
    x ∈ repl.freeVars ∨ (x ∈ LocalTypeR.end.freeVars ∧ x ≠ varName) := by
  -- end has no free vars, so this case is impossible.
  simp only [LocalTypeR.substitute, LocalTypeR.freeVars, List.not_mem_nil] at hx

private theorem freeVars_substitute_subset_var
    (t varName : String) (repl : LocalTypeR) (x : String)
    (hx : x ∈ ((LocalTypeR.var t).substitute varName repl).freeVars) :
    x ∈ repl.freeVars ∨ (x ∈ (LocalTypeR.var t).freeVars ∧ x ≠ varName) := by
  -- Split on whether the substituted variable matches the var.
  simp only [LocalTypeR.substitute] at hx
  by_cases heq : t = varName
  · -- Match: result is repl.
    have hbool : (t == varName) = true := by
      simp [heq]
    simp only [hbool, ↓reduceIte] at hx
    exact Or.inl hx
  · -- No match: result is .var t.
    have hbool : (t == varName) = false := (beq_eq_false_iff_ne).2 heq
    simp only [hbool, Bool.false_eq_true, ↓reduceIte, LocalTypeR.freeVars,
      List.mem_singleton] at hx
    refine Or.inr ?_
    constructor
    · simp [LocalTypeR.freeVars, hx]
    · simpa [hx] using heq

private theorem freeVars_substitute_subset_mu_shadow
    (t varName : String) (body repl : LocalTypeR) (x : String)
    (heq : (t == varName) = true)
    (hx : x ∈ body.freeVars.filter (fun v => v != t)) :
    x ∈ repl.freeVars ∨ (x ∈ (LocalTypeR.mu t body).freeVars ∧ x ≠ varName) := by
  -- Shadowed binder: free vars are the filtered body vars.
  have hxpair : x ∈ body.freeVars ∧ x ≠ t := by
    simpa [List.mem_filter, bne_iff_ne] using hx
  have hxne_t : x ≠ t := hxpair.2
  have htv : t = varName := by simpa [beq_iff_eq] using heq
  refine Or.inr ?_
  constructor
  · simpa [LocalTypeR.freeVars] using hx
  · simpa [htv] using hxne_t

/-! ## Substitution Under Mu (Shadowing Cases) -/
private theorem freeVars_substitute_subset_mu_noshadow
    (t varName : String) (body repl : LocalTypeR) (x : String)
    (hx : x ∈ (body.substitute varName repl).freeVars.filter (fun v => v != t))
    (ih : x ∈ repl.freeVars ∨ (x ∈ body.freeVars ∧ x ≠ varName)) :
    x ∈ repl.freeVars ∨ (x ∈ (LocalTypeR.mu t body).freeVars ∧ x ≠ varName) := by
  -- Not shadowed: recurse into the body and re-wrap the filter.
  cases ih with
  | inl hrepl => exact Or.inl hrepl
  | inr hpair =>
      have hxpair' : x ∈ (body.substitute varName repl).freeVars ∧ x ≠ t := by
        simpa [List.mem_filter, bne_iff_ne] using hx
      have hxne_t : x ≠ t := hxpair'.2
      refine Or.inr ?_
      constructor
      · apply List.mem_filter.mpr
        exact ⟨hpair.1, by simpa [bne_iff_ne] using hxne_t⟩
      · exact hpair.2

/-! ## Mutual Substitution Recursion -/
mutual
private def freeVars_substitute_subset_aux (lt : LocalTypeR) (varName : String) (repl : LocalTypeR)
    (x : String) (hx : x ∈ (lt.substitute varName repl).freeVars) :
    x ∈ repl.freeVars ∨ (x ∈ lt.freeVars ∧ x ≠ varName) :=
  -- Reduce by cases on lt, delegating to focused helpers.
  match lt with
  | .end =>
      freeVars_substitute_subset_end varName repl x hx
  | .var t =>
      freeVars_substitute_subset_var t varName repl x hx
  | .send _ branches => by
      simp only [LocalTypeR.substitute, LocalTypeR.freeVars] at hx ⊢;
        exact freeVars_substituteBranches_subset_aux branches varName repl x hx
  | .recv _ branches => by
      simp only [LocalTypeR.substitute, LocalTypeR.freeVars] at hx ⊢;
        exact freeVars_substituteBranches_subset_aux branches varName repl x hx
    | .mu t body => by
        simp only [LocalTypeR.substitute] at hx
        by_cases heq : t = varName
        · have hbool : (t == varName) = true := by simp [heq]
          have hx' : x ∈ body.freeVars.filter (fun v => v != t) := by
            simpa [hbool, LocalTypeR.freeVars] using hx
          exact freeVars_substitute_subset_mu_shadow t varName body repl x hbool hx'
        · have hbool : (t == varName) = false := (beq_eq_false_iff_ne).2 heq
          have hx' : x ∈ (body.substitute varName repl).freeVars.filter (fun v => v != t) := by
            simpa [hbool, LocalTypeR.freeVars] using hx
          have ih := freeVars_substitute_subset_aux body varName repl x (by
            exact (List.mem_filter.mp hx').1)
          exact freeVars_substitute_subset_mu_noshadow t varName body repl x hx' ih
termination_by sizeOf lt

/-! ## Branch Substitution Recursion -/
private def freeVars_substituteBranches_subset_aux
    (branches : List BranchR) (varName : String) (repl : LocalTypeR)
    (x : String) (hx : x ∈ SessionTypes.LocalTypeR.freeVarsOfBranches (SessionTypes.LocalTypeR.substituteBranches branches varName repl)) :
    x ∈ repl.freeVars ∨ (x ∈ SessionTypes.LocalTypeR.freeVarsOfBranches branches ∧ x ≠ varName) :=
  match branches with
  | [] => by simp only [SessionTypes.LocalTypeR.substituteBranches, SessionTypes.LocalTypeR.freeVarsOfBranches, List.not_mem_nil] at hx
  | (label, _vt, cont) :: rest => by
      simp only [SessionTypes.LocalTypeR.substituteBranches, SessionTypes.LocalTypeR.freeVarsOfBranches, List.mem_append] at hx
      cases hx with
      | inl hxcont =>
          have ih := freeVars_substitute_subset_aux cont varName repl x hxcont
          cases ih with
          | inl hrepl => left; exact hrepl
          | inr hpair =>
              right
              simp only [SessionTypes.LocalTypeR.freeVarsOfBranches, List.mem_append]
              exact ⟨Or.inl hpair.1, hpair.2⟩
      | inr hxrest =>
          have ih := freeVars_substituteBranches_subset_aux rest varName repl x hxrest
          cases ih with
          | inl hrepl => left; exact hrepl
          | inr hpair =>
              right
              simp only [SessionTypes.LocalTypeR.freeVarsOfBranches, List.mem_append]
              exact ⟨Or.inr hpair.1, hpair.2⟩
termination_by sizeOf branches
end

/-! ## Substitution Free-Variable Superset Theorem -/
theorem freeVars_substitute_subset (lt : LocalTypeR) (varName : String) (repl : LocalTypeR) :
    ∀ x, x ∈ (lt.substitute varName repl).freeVars →
         x ∈ repl.freeVars ∨ (x ∈ lt.freeVars ∧ x ≠ varName) :=
  fun x hx => freeVars_substitute_subset_aux lt varName repl x hx

/-! ## Substitution Closedness Lemma -/
theorem substitute_closed_when_only_var (lt : LocalTypeR) (varName : String) (repl : LocalTypeR)
    (hlt : ∀ x, x ∈ lt.freeVars → x = varName)
    (hrepl : repl.freeVars = []) :
    (lt.substitute varName repl).freeVars = [] := by
  -- Show the list is empty by proving no element can be in it
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  -- By freeVars_substitute_subset, x ∈ repl.freeVars ∨ (x ∈ lt.freeVars ∧ x ≠ varName)
  have hsub := freeVars_substitute_subset lt varName repl x hx
  cases hsub with
  | inl hrepl_mem =>
      -- x ∈ repl.freeVars contradicts hrepl : repl.freeVars = []
      simp only [hrepl, List.not_mem_nil] at hrepl_mem
  | inr hpair =>
      -- x ∈ lt.freeVars ∧ x ≠ varName
      -- But hlt says x = varName, contradicting x ≠ varName
      have hxeq := hlt x hpair.1
      exact hpair.2 hxeq

/-! ## Closed Mu Body Variable Constraint -/
theorem mu_closed_body_freeVars (t : String) (body : LocalTypeR)
    (hclosed : (.mu t body : LocalTypeR).freeVars = []) :
    ∀ x, x ∈ body.freeVars → x = t := by
  intro x hx
  simp only [LocalTypeR.freeVars] at hclosed
  -- hclosed : body.freeVars.filter (· != t) = []
  -- If x ∈ body.freeVars and x ≠ t, then x would be in the filter
  by_contra hne
  have hfilter : x ∈ body.freeVars.filter (· != t) := by
    rw [List.mem_filter]
    constructor
    · exact hx
    · simp only [bne_iff_ne, ne_eq]
      exact hne
  simp only [hclosed, List.not_mem_nil] at hfilter

/-! ## Filter Helper for Uniform Variables -/
private theorem filter_all_eq_nil {L : List String} {t : String}
    (h : ∀ x, x ∈ L → x = t) :
    L.filter (· != t) = [] := by
  match L with
  | [] => rfl
  | hd :: tl =>
      have hmem_hd : hd ∈ hd :: tl := by simp
      have hhd : hd = t := h hd hmem_hd
      have htl : ∀ x, x ∈ tl → x = t := by
        intro x hx
        have hmem : x ∈ hd :: tl := List.mem_cons_of_mem hd hx
        exact h x hmem
      simp only [List.filter, hhd, bne_self_eq_false]
      exact filter_all_eq_nil htl
termination_by L.length

/-! ## allVarsBound Implies Free-Variable Inclusion -/
mutual
private def allVarsBound_implies_freeVars_subset_aux (g : GlobalType) (bound : List String)
    (h : g.allVarsBound bound = true) (x : String) (hx : x ∈ g.freeVars) : x ∈ bound :=
  match g with
  | .end => by simp only [GlobalType.freeVars, List.not_mem_nil] at hx
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
termination_by sizeOf g

private def allVarsBoundBranches_implies_freeVars_subset_aux
    (branches : List (Label × GlobalType)) (bound : List String)
    (h : allVarsBoundBranches branches bound = true) (x : String)
    (hx : x ∈ SessionTypes.GlobalType.freeVarsOfBranches branches) : x ∈ bound :=
  match branches with
  | [] => by simp only [SessionTypes.GlobalType.freeVarsOfBranches, List.not_mem_nil] at hx
  | (_, cont) :: rest => by
      simp only [SessionTypes.GlobalType.freeVarsOfBranches, List.mem_append] at hx
      simp only [allVarsBoundBranches, Bool.and_eq_true] at h
      cases hx with
      | inl hxcont => exact allVarsBound_implies_freeVars_subset_aux cont bound h.1 x hxcont
      | inr hxrest => exact allVarsBoundBranches_implies_freeVars_subset_aux rest bound h.2 x hxrest
termination_by sizeOf branches
end

/-- If all variables are bound with empty context, there are no free variables. -/
theorem allVarsBound_nil_implies_freeVars_nil (g : GlobalType)
    (h : g.allVarsBound [] = true) :
    g.freeVars = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have hmem := allVarsBound_implies_freeVars_subset_aux g [] h x hx
  simp only [List.not_mem_nil] at hmem

/-! ## Muve Preservation Under Substitution -/
theorem isMuve_substitute (lt : LocalTypeR) (varName : String) (repl : LocalTypeR)
    (hlt : isMuve lt = true) (hrepl : isMuve repl = true) :
    isMuve (lt.substitute varName repl) = true := by
  -- Follow the structure of lt and preserve the muve invariant.
  match lt with
  | .end => simp [LocalTypeR.substitute, isMuve]
  | .var t =>
      by_cases heq : t == varName <;>
        simp [LocalTypeR.substitute, heq, hrepl, isMuve]
  | .mu t body =>
      simp only [isMuve] at hlt
      by_cases heq : t == varName
      · simp [LocalTypeR.substitute, heq, isMuve, hlt]
      · simp [LocalTypeR.substitute, heq, isMuve]
        exact isMuve_substitute body varName repl hlt hrepl
  | .send _ _ =>
      have : False := by
        simp [isMuve] at hlt
      exact this.elim
  | .recv _ _ =>
      have : False := by
        simp [isMuve] at hlt
      exact this.elim
termination_by sizeOf lt

/-! ## Structural Well-Formedness

Following the Coq development, we separate structural properties (allCommsNonEmpty, noSelfComm)
from variable binding (allVarsBound). The structural properties compose well with mu bodies,
while allVarsBound does not (body.allVarsBound [t] doesn't imply body.allVarsBound []).

This avoids the semantic gap that arises from using full wellFormed. -/

/-! ## Mu Structural Well-Formedness Helper -/
private theorem wellFormed_mu_body (t : String) (body : GlobalType)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    body.allCommsNonEmpty = true ∧ body.noSelfComm = true := by
  unfold GlobalType.wellFormed at hwf
  simp only [GlobalType.allCommsNonEmpty, GlobalType.noSelfComm, Bool.and_eq_true] at hwf
  simp_all only [and_self]

/-! ## Size Decrease Helper for Comm Branches -/
private theorem sizeOf_pair_snd_lt_comm (sender receiver : String) (pair : Label × GlobalType)
    (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (GlobalType.comm sender receiver (pair :: rest)) := by
  -- sizeOf (comm s r bs) = 1 + sizeOf s + sizeOf r + sizeOf bs
  -- sizeOf (pair :: rest) = 1 + sizeOf pair + sizeOf rest
  -- sizeOf pair = 1 + sizeOf pair.1 + sizeOf pair.2
  -- So sizeOf pair.2 < 1 + sizeOf s + sizeOf r + (1 + (1 + sizeOf pair.1 + sizeOf pair.2) + sizeOf rest)
  --               = 3 + sizeOf s + sizeOf r + sizeOf pair.1 + sizeOf pair.2 + sizeOf rest
  -- Which is: sizeOf pair.2 < sizeOf pair.2 + (3 + sizeOf s + sizeOf r + sizeOf pair.1 + sizeOf rest)
  -- Since 3 + ... > 0, this is true
  simp only [GlobalType.comm.sizeOf_spec]
  have hp : sizeOf pair = 1 + sizeOf pair.1 + sizeOf pair.2 := by rfl
  simp only [List.cons.sizeOf_spec, hp]
  omega

/-! ## Comm Branch Well-Formedness Helper -/
private theorem wellFormed_comm_cont (sender receiver : String) (pair : Label × GlobalType)
    (rest : List (Label × GlobalType))
    (hwf : (GlobalType.comm sender receiver (pair :: rest)).wellFormed = true) :
    pair.2.wellFormed = true := by
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf ⊢
  simp only [GlobalType.allVarsBound, allVarsBoundBranches,
             GlobalType.allCommsNonEmpty, allCommsNonEmptyBranches,
             GlobalType.noSelfComm, noSelfCommBranches,
             GlobalType.isProductive, isProductiveBranches,
             Bool.and_eq_true] at hwf ⊢
  tauto

/-! ## Auxiliary Muve Projection Theorems -/
private theorem trans_muve_of_not_part_of2_aux_base (g : GlobalType) (role : String) :
    g = .end ∨ (∃ t, g = .var t) → isMuve (trans g role) = true := by
  -- Base cases follow directly from trans and isMuve definitions.
  intro h
  cases h with
  | inl hEnd => cases hEnd; simp [trans, isMuve]
  | inr hVar => rcases hVar with ⟨t, rfl⟩; simp [trans, isMuve]

/-! ## Auxiliary Mu Case -/
private theorem trans_muve_of_not_part_of2_aux_mu (t : String) (body : GlobalType) (role : String)
    (_hnotpart : ¬ part_of2 role (.mu t body))
    (_hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (_hnsc : (GlobalType.mu t body).noSelfComm = true)
    (hbody : isMuve (trans body role) = true) :
    isMuve (trans (.mu t body) role) = true := by
  -- The mu case reduces to the body when the projection is guarded.
  rw [trans.eq_3]
  by_cases hguard : (trans body role).isGuarded t
  · simp only [hguard, ↓reduceIte, isMuve]
    exact hbody
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, isMuve]

/-! ## Main Auxiliary Recursor -/
private theorem trans_muve_of_not_part_of2_aux (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g)
    (hne : g.allCommsNonEmpty = true) (hnsc : g.noSelfComm = true) :
    isMuve (trans g role) = true := by
  -- Dispatch on g and delegate to the focused helpers.
  match g with
  | .end => exact trans_muve_of_not_part_of2_aux_base .end role (Or.inl rfl)
  | .var t => exact trans_muve_of_not_part_of2_aux_base (.var t) role (Or.inr ⟨t, rfl⟩)
  | .mu t body =>
      have hnotpart_body : ¬ part_of2 role body := by
        intro hbody
        exact hnotpart (part_of2.intro _ (part_ofF.mu t body hbody))
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have hnsc_body : body.noSelfComm = true := by
        simpa [GlobalType.noSelfComm] using hnsc
      have hbody : isMuve (trans body role) = true :=
        trans_muve_of_not_part_of2_aux body role hnotpart_body hne_body hnsc_body
      exact trans_muve_of_not_part_of2_aux_mu t body role hnotpart hne hnsc hbody
  /-! ## Auxiliary Recursor: Comm Case -/
  | .comm sender receiver branches =>
      -- Participants contradict the non-participation hypothesis; non-participants recurse.
      cases hrole_sender : role == sender with
      | true =>
          have hpart : part_of2 role (GlobalType.comm sender receiver branches) := by
            apply part_of2.intro; apply part_ofF.comm_direct
            simp [is_participant, hrole_sender]
          exact (hnotpart hpart).elim
      | false =>
          cases hrole_receiver : role == receiver with
          | true =>
              have hpart : part_of2 role (GlobalType.comm sender receiver branches) := by
                apply part_of2.intro; apply part_ofF.comm_direct
                simp [is_participant, hrole_sender, hrole_receiver]
              exact (hnotpart hpart).elim
          | false =>
              cases branches with
              | nil =>
                  simp [trans, hrole_sender, hrole_receiver, isMuve]
              | cons first rest =>
                  rw [trans.eq_5]
                  simp only [hrole_sender, Bool.false_eq_true, ↓reduceIte, hrole_receiver]
                  have hnotpart_cont : ¬ part_of2 role first.2 := by
                    intro hcont
                    have hmem : (first.1, first.2) ∈ first :: rest := by simp
                    exact hnotpart (part_of2.intro _ (part_ofF.comm_branch sender receiver
                      first.1 first.2 (first :: rest) hmem hcont))
                  have hne_cont : first.2.allCommsNonEmpty = true := by
                    simp only [GlobalType.allCommsNonEmpty, allCommsNonEmptyBranches,
                      Bool.and_eq_true] at hne
                    exact hne.2.1
                  have hnsc_cont : first.2.noSelfComm = true := by
                    simp only [GlobalType.noSelfComm, noSelfCommBranches,
                      Bool.and_eq_true] at hnsc
                    exact hnsc.2.1
                  exact trans_muve_of_not_part_of2_aux first.2 role hnotpart_cont hne_cont hnsc_cont
termination_by sizeOf g
decreasing_by
  all_goals
    simp_wf
    subst_vars
    first
    | omega
    | exact sizeOf_body_lt_mu _ _
    | simpa [GlobalType.comm.sizeOf_spec] using sizeOf_pair_snd_lt_comm _ _ _ _

/-! ## Non-Participant Muve Projection Theorem -/
theorem trans_muve_of_not_part_of2 (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g) (hwf : g.wellFormed = true) :
    isMuve (trans g role) = true := by
  -- Extract structural properties from wellFormed
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact trans_muve_of_not_part_of2_aux g role hnotpart hwf.1.1.2 hwf.1.2

end Choreography.Projection.Project
