import RumpsteakV2.Protocol.Projection.Project.Core
import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.Participation
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.EQ2Props

/-! # RumpsteakV2.Protocol.Projection.Project.Muve

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

namespace RumpsteakV2.Protocol.Projection.Project

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.Participation
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Props

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

-- Helper: free variables after substitution are either from the replacement or
-- free variables not equal to the substituted variable.
-- Proven by mutual well-founded recursion on local type / branches size.

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

private def freeVars_substituteBranches_subset_aux
    (branches : List (Label × LocalTypeR)) (varName : String) (repl : LocalTypeR)
    (x : String) (hx : x ∈ LocalTypeR.freeVarsOfBranches (LocalTypeR.substituteBranches branches varName repl)) :
    x ∈ repl.freeVars ∨ (x ∈ LocalTypeR.freeVarsOfBranches branches ∧ x ≠ varName) :=
  match branches with
  | [] => by simp only [LocalTypeR.substituteBranches, LocalTypeR.freeVarsOfBranches, List.not_mem_nil] at hx
  | (label, cont) :: rest => by
      simp only [LocalTypeR.substituteBranches, LocalTypeR.freeVarsOfBranches, List.mem_append] at hx
      cases hx with
      | inl hxcont =>
          have ih := freeVars_substitute_subset_aux cont varName repl x hxcont
          cases ih with
          | inl hrepl => left; exact hrepl
          | inr hpair =>
              right
              simp only [LocalTypeR.freeVarsOfBranches, List.mem_append]
              exact ⟨Or.inl hpair.1, hpair.2⟩
      | inr hxrest =>
          have ih := freeVars_substituteBranches_subset_aux rest varName repl x hxrest
          cases ih with
          | inl hrepl => left; exact hrepl
          | inr hpair =>
              right
              simp only [LocalTypeR.freeVarsOfBranches, List.mem_append]
              exact ⟨Or.inr hpair.1, hpair.2⟩
termination_by sizeOf branches
end

/-- Free variables after substitution come from the replacement or the original (minus varName). -/
theorem freeVars_substitute_subset (lt : LocalTypeR) (varName : String) (repl : LocalTypeR) :
    ∀ x, x ∈ (lt.substitute varName repl).freeVars →
         x ∈ repl.freeVars ∨ (x ∈ lt.freeVars ∧ x ≠ varName) :=
  fun x hx => freeVars_substitute_subset_aux lt varName repl x hx

/-- If all free variables of lt are equal to varName, and repl is closed,
    then lt.substitute varName repl is closed.

    Proven using freeVars_substitute_subset. -/
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

/-- For closed mu types, the body's only free variable is possibly the bound variable.

If (.mu t body).freeVars = [], then body.freeVars.filter (· != t) = [],
meaning any free variable in body must equal t. -/
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

/-- Helper: if all vars in list equal t, then filtering out t gives empty list. -/
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

-- Helper: allVarsBound implies freeVars are contained in bound list
-- Uses mutual well-founded recursion on global type/branches size.
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
    (h : GlobalType.allVarsBoundBranches branches bound = true) (x : String)
    (hx : x ∈ GlobalType.freeVarsOfBranches branches) : x ∈ bound :=
  match branches with
  | [] => by simp only [GlobalType.freeVarsOfBranches, List.not_mem_nil] at hx
  | (_, cont) :: rest => by
      simp only [GlobalType.freeVarsOfBranches, List.mem_append] at hx
      simp only [GlobalType.allVarsBoundBranches, Bool.and_eq_true] at h
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

/-- Muve types remain muve after substitution with muve replacements.

    Proven by well-founded recursion on the local type size. -/
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

/-! ### Structural Well-Formedness

Following the Coq development, we separate structural properties (allCommsNonEmpty, noSelfComm)
from variable binding (allVarsBound). The structural properties compose well with mu bodies,
while allVarsBound does not (body.allVarsBound [t] doesn't imply body.allVarsBound []).

This avoids the semantic gap that arises from using full wellFormed. -/

-- Helper: wellFormed preservation for mu body (structural parts only)
private theorem wellFormed_mu_body (t : String) (body : GlobalType)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    body.allCommsNonEmpty = true ∧ body.noSelfComm = true := by
  unfold GlobalType.wellFormed at hwf
  simp only [GlobalType.allCommsNonEmpty, GlobalType.noSelfComm, Bool.and_eq_true] at hwf
  simp_all only [and_self]

-- Helper: sizeOf pair.2 < sizeOf (comm sender receiver (pair :: rest))
-- This is needed for termination proof of trans_muve_of_not_part_of2
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

-- Helper: wellFormed preservation for comm first branch
private theorem wellFormed_comm_cont (sender receiver : String) (pair : Label × GlobalType)
    (rest : List (Label × GlobalType))
    (hwf : (GlobalType.comm sender receiver (pair :: rest)).wellFormed = true) :
    pair.2.wellFormed = true := by
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf ⊢
  simp only [GlobalType.allVarsBound, GlobalType.allVarsBoundBranches,
             GlobalType.allCommsNonEmpty, GlobalType.allCommsNonEmptyBranches,
             GlobalType.noSelfComm, GlobalType.noSelfCommBranches,
             GlobalType.isProductive, GlobalType.isProductiveBranches,
             Bool.and_eq_true] at hwf ⊢
  tauto

/-- Auxiliary version using structural properties that compose with mu.
    This avoids the semantic gap where body.allVarsBound [] cannot be proven
    from (mu t body).wellFormed. -/
private theorem trans_muve_of_not_part_of2_aux_base (g : GlobalType) (role : String) :
    g = .end ∨ (∃ t, g = .var t) → isMuve (Trans.trans g role) = true := by
  -- Base cases follow directly from trans and isMuve definitions.
  intro h
  cases h with
  | inl hEnd => cases hEnd; simp [Trans.trans, isMuve]
  | inr hVar => rcases hVar with ⟨t, rfl⟩; simp [Trans.trans, isMuve]

private theorem trans_muve_of_not_part_of2_aux_mu (t : String) (body : GlobalType) (role : String)
    (_hnotpart : ¬ part_of2 role (.mu t body))
    (_hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (_hnsc : (GlobalType.mu t body).noSelfComm = true)
    (hbody : isMuve (Trans.trans body role) = true) :
    isMuve (Trans.trans (.mu t body) role) = true := by
  -- The mu case reduces to the body when the projection is guarded.
  rw [Trans.trans.eq_3]
  by_cases hguard : (Trans.trans body role).isGuarded t
  · simp only [hguard, ↓reduceIte, isMuve]
    exact hbody
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, isMuve]

private theorem trans_muve_of_not_part_of2_aux (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g)
    (hne : g.allCommsNonEmpty = true) (hnsc : g.noSelfComm = true) :
    isMuve (Trans.trans g role) = true := by
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
      have hbody : isMuve (Trans.trans body role) = true :=
        trans_muve_of_not_part_of2_aux body role hnotpart_body hne_body hnsc_body
      exact trans_muve_of_not_part_of2_aux_mu t body role hnotpart hne hnsc hbody
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
                  simp [Trans.trans, hrole_sender, hrole_receiver, isMuve]
              | cons first rest =>
                  rw [Trans.trans.eq_5]
                  simp only [hrole_sender, Bool.false_eq_true, ↓reduceIte, hrole_receiver]
                  have hnotpart_cont : ¬ part_of2 role first.2 := by
                    intro hcont
                    have hmem : (first.1, first.2) ∈ first :: rest := by simp
                    exact hnotpart (part_of2.intro _ (part_ofF.comm_branch sender receiver
                      first.1 first.2 (first :: rest) hmem hcont))
                  have hne_cont : first.2.allCommsNonEmpty = true := by
                    simp only [GlobalType.allCommsNonEmpty, GlobalType.allCommsNonEmptyBranches,
                      Bool.and_eq_true] at hne
                    exact hne.2.1
                  have hnsc_cont : first.2.noSelfComm = true := by
                    simp only [GlobalType.noSelfComm, GlobalType.noSelfCommBranches,
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

/-- Non-participant projection yields a muve local type under well-formedness. -/
theorem trans_muve_of_not_part_of2 (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g) (hwf : g.wellFormed = true) :
    isMuve (Trans.trans g role) = true := by
  -- Extract structural properties from wellFormed
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact trans_muve_of_not_part_of2_aux g role hnotpart hwf.1.1.2 hwf.1.2

/-- Relation for proving EQ2 .end X for closed muve types.
    ClosedMuveRel a b holds when a = .end and b is a closed muve type. -/
def ClosedMuveRel : LocalTypeR → LocalTypeR → Prop := fun a b =>
  a = .end ∧ isMuve b = true ∧ isClosed b = true

/-- Convert isClosed = true to freeVars = []. -/
theorem isClosed_eq_true_iff (lt : LocalTypeR) :
    isClosed lt = true ↔ lt.freeVars = [] := by
  simp only [isClosed, beq_iff_eq]

/-- For closed muve types, substituting into the body keeps it closed muve.
    This is key for the mu case of the coinduction proof. -/
theorem closed_muve_substitute_mu (t : String) (body : LocalTypeR)
    (hmuve : isMuve (.mu t body) = true)
    (hclosed : isClosed (.mu t body) = true) :
    isMuve (body.substitute t (.mu t body)) = true ∧
    isClosed (body.substitute t (.mu t body)) = true := by
  -- Convert isClosed hypothesis to freeVars = []
  have hclosed_eq : (.mu t body : LocalTypeR).freeVars = [] :=
    (isClosed_eq_true_iff _).mp hclosed
  constructor
  · -- muve preservation
    simp only [isMuve] at hmuve
    apply isMuve_substitute
    · exact hmuve
    · -- isMuve (.mu t body) requires isMuve body
      simp only [isMuve, hmuve]
  · -- closed preservation: use substitute_closed_when_only_var
    rw [isClosed_eq_true_iff]
    -- (.mu t body).freeVars = [] means body.freeVars.filter (· != t) = []
    -- This means all free vars in body are equal to t
    have hbody_fv : ∀ x, x ∈ body.freeVars → x = t := mu_closed_body_freeVars t body hclosed_eq
    -- (.mu t body).freeVars = [] since isClosed
    exact substitute_closed_when_only_var body t (.mu t body) hbody_fv hclosed_eq

/-- ClosedMuveRel is a post-fixpoint of EQ2F.
    This proves: if b is a closed muve type, then EQ2 .end b. -/
theorem ClosedMuveRel_postfix :
    ∀ a b, ClosedMuveRel a b → EQ2F ClosedMuveRel a b := by
  intro a b ⟨ha, hmuve, hclosed⟩
  subst ha  -- a = .end
  cases b with
  | «end» => simp only [EQ2F]  -- EQ2F _ .end .end = True
  | var t =>
      -- var has free vars, contradicts hclosed
      -- hclosed : isClosed (.var t) = true means ([t] == []) = true
      -- But [t] ≠ [], so this is false = true
      simp only [isClosed, LocalTypeR.freeVars, beq_iff_eq] at hclosed
      exact nomatch hclosed
  | mu t body =>
      -- EQ2F ClosedMuveRel .end (.mu t body) = ClosedMuveRel .end (body.substitute t (.mu t body))
      simp only [EQ2F]
      constructor
      · rfl
      · have ⟨hmuve', hclosed'⟩ := closed_muve_substitute_mu t body hmuve hclosed
        exact ⟨hmuve', hclosed'⟩
  | send _ _ => simp [isMuve] at hmuve
  | recv _ _ => simp [isMuve] at hmuve


end RumpsteakV2.Protocol.Projection.Project
