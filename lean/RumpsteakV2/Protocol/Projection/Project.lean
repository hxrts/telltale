import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.EQ2Paco
import RumpsteakV2.Protocol.Participation

/-! # RumpsteakV2.Protocol.Projection.Project

Proof-carrying projection API for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `projectR?`: proof-carrying projection (returns projection with CProject proof)
- `projectR?_some_iff_CProject`: specification lemma
- `projectR?_sound`: soundness (some implies CProject)
- `projectR?_complete`: completeness (CProject implies some)
- `EQ_end`: non-participants project to EEnd (EQ2-equivalent)
-/

namespace RumpsteakV2.Protocol.Projection.Project

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Paco
open RumpsteakV2.Protocol.Participation

/-- Proof-carrying projection: returns the local type with a proof that CProject holds.
    Uses `trans` to compute the candidate and `projectb` to validate.
    Returns `some` iff projection succeeds. -/
def projectR? (g : GlobalType) (role : String) : Option { lt : LocalTypeR // CProject g role lt } :=
  let candidate := trans g role
  if h : projectb g role candidate = true then
    some ⟨candidate, projectb_sound g role candidate h⟩
  else
    none

/-- Inversion lemma: if projectR? returns some, then projectb was true. -/
theorem projectR?_some_implies_projectb {g : GlobalType} {role : String}
    {result : { lt : LocalTypeR // CProject g role lt }}
    (hsome : projectR? g role = some result) :
    projectb g role result.val = true := by
  simp only [projectR?] at hsome
  by_cases hproj : projectb g role (trans g role) = true
  · simp only [hproj, ↓reduceDIte, Option.some.injEq] at hsome
    cases result with
    | mk val property =>
        simp only [Subtype.mk.injEq] at hsome
        subst hsome
        exact hproj
  · -- In this case, projectR? returns none, but hsome says it's some - contradiction
    rw [dif_neg hproj] at hsome
    exact nomatch hsome

/-- Soundness: if projectR? returns some, then CProject holds. -/
theorem projectR?_sound {g : GlobalType} {role : String}
    {result : { lt : LocalTypeR // CProject g role lt }}
    (_h : projectR? g role = some result) :
    CProject g role result.val :=
  result.property

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

/-- A local type is closed if it has no free variables. -/
def isClosed (lt : LocalTypeR) : Bool := lt.freeVars == []

/-! ## FreeVars lemmas for substitution -/

-- Helper: free variables after substitution are either from the replacement or
-- free variables not equal to the substituted variable.
-- Proven by mutual well-founded recursion on local type / branches size.
mutual
  private def freeVars_substitute_subset_aux (lt : LocalTypeR) (varName : String) (repl : LocalTypeR)
      (x : String) (hx : x ∈ (lt.substitute varName repl).freeVars) :
      x ∈ repl.freeVars ∨ (x ∈ lt.freeVars ∧ x ≠ varName) :=
    match lt with
    | .end => by simp only [LocalTypeR.substitute, LocalTypeR.freeVars, List.not_mem_nil] at hx
    | .var t => by
        simp only [LocalTypeR.substitute] at hx
        by_cases heq : t == varName
        · -- t == varName: result is repl
          simp only [heq, ↓reduceIte] at hx
          left; exact hx
        · -- t != varName: result is .var t
          simp only [heq, Bool.false_eq_true, ↓reduceIte, LocalTypeR.freeVars,
            List.mem_singleton] at hx
          right
          simp only [LocalTypeR.freeVars, List.mem_singleton]
          constructor
          · exact hx
          · simp only [bne_iff_ne, ne_eq, Bool.not_eq_true, beq_eq_false_iff_ne] at heq
            rw [hx]; exact heq
    | .send partner branches => by
        simp only [LocalTypeR.substitute, LocalTypeR.freeVars] at hx ⊢
        exact freeVars_substituteBranches_subset_aux branches varName repl x hx
    | .recv partner branches => by
        simp only [LocalTypeR.substitute, LocalTypeR.freeVars] at hx ⊢
        exact freeVars_substituteBranches_subset_aux branches varName repl x hx
    | .mu t body => by
        simp only [LocalTypeR.substitute] at hx
        by_cases heq : t == varName
        · -- Shadowed: result is unchanged, freeVars same
          simp only [heq, ↓reduceIte, LocalTypeR.freeVars] at hx
          right
          simp only [LocalTypeR.freeVars]
          -- hx : x ∈ body.freeVars.filter (· != t)
          -- goal: x ∈ body.freeVars.filter (· != t) ∧ x ≠ varName
          rw [List.mem_filter] at hx
          constructor
          · rw [List.mem_filter]; exact hx
          · -- x ≠ varName because x ≠ t and t = varName
            simp only [beq_iff_eq] at heq
            simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] at hx
            intro hxeq
            rw [← heq] at hxeq
            exact hx.2 hxeq
        · -- Not shadowed: recurse into body
          simp only [heq, Bool.false_eq_true, ↓reduceIte, LocalTypeR.freeVars] at hx
          rw [List.mem_filter] at hx
          have ⟨hxbody, hxnet⟩ := hx
          simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] at hxnet
          have ih := freeVars_substitute_subset_aux body varName repl x hxbody
          cases ih with
          | inl hrepl => left; exact hrepl
          | inr hpair =>
              right
              simp only [LocalTypeR.freeVars]
              constructor
              · rw [List.mem_filter]
                constructor
                · exact hpair.1
                · simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; exact hxnet
              · exact hpair.2
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
        simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] at hx
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
  match lt with
  | .end =>
      -- .end.substitute = .end
      simp only [LocalTypeR.substitute, isMuve]
  | .var t =>
      -- If t == varName, result is repl (muve by hrepl)
      -- Otherwise, result is .var t (muve by definition)
      simp only [LocalTypeR.substitute]
      by_cases heq : t == varName
      · simp only [heq, ↓reduceIte, hrepl]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte, isMuve]
  | .mu t body =>
      -- isMuve (.mu t body) = isMuve body, so hlt gives us isMuve body = true
      simp only [isMuve] at hlt
      simp only [LocalTypeR.substitute]
      by_cases heq : t == varName
      · -- Shadowed: substitute returns original
        simp only [heq, ↓reduceIte, isMuve, hlt]
      · -- Not shadowed: substitute into body
        simp only [heq, Bool.false_eq_true, ↓reduceIte, isMuve]
        exact isMuve_substitute body varName repl hlt hrepl
  | .send _ _ =>
      -- isMuve (.send ...) = false, contradicts hlt
      simp only [isMuve] at hlt
      exact absurd hlt (by decide)
  | .recv _ _ =>
      -- isMuve (.recv ...) = false, contradicts hlt
      simp only [isMuve] at hlt
      exact absurd hlt (by decide)
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
private theorem trans_muve_of_not_part_of2_aux (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g)
    (hne : g.allCommsNonEmpty = true) (hnsc : g.noSelfComm = true) :
    isMuve (Trans.trans g role) = true := by
  match g with
  | .end =>
      simp only [Trans.trans, isMuve]
  | .var _ =>
      simp only [Trans.trans, isMuve]
  | .mu t body =>
      rw [Trans.trans.eq_3]
      by_cases hlc : lcontractive body
      · simp only [hlc, ↓reduceIte, isMuve]
        have hnotpart_body : ¬ part_of2 role body := by
          intro hbody
          exact hnotpart (part_of2.intro _ (part_ofF.mu t body hbody))
        -- Extract structural properties for body (these DO compose with mu)
        have hne_body : body.allCommsNonEmpty = true := by
          simp only [GlobalType.allCommsNonEmpty] at hne
          exact hne
        have hnsc_body : body.noSelfComm = true := by
          simp only [GlobalType.noSelfComm] at hnsc
          exact hnsc
        have hlt : sizeOf body < sizeOf (GlobalType.mu t body) := by
          simp only [GlobalType.mu.sizeOf_spec]; omega
        exact trans_muve_of_not_part_of2_aux body role hnotpart_body hne_body hnsc_body
      · simp only [hlc, Bool.false_eq_true, ↓reduceIte, isMuve]
  | .comm sender receiver branches =>
      by_cases hrole_sender : role == sender
      · have hpart : part_of2 role (.comm sender receiver branches) := by
          apply part_of2.intro
          apply part_ofF.comm_direct
          simp only [is_participant, hrole_sender, Bool.true_or]
        exact absurd hpart hnotpart
      · by_cases hrole_receiver : role == receiver
        · have hpart : part_of2 role (.comm sender receiver branches) := by
            apply part_of2.intro
            apply part_ofF.comm_direct
            simp only [is_participant, hrole_sender, hrole_receiver, Bool.or_true]
          exact absurd hpart hnotpart
        · cases branches with
          | nil =>
              simp only [Trans.trans, hrole_sender, Bool.false_eq_true, ↓reduceIte,
                         hrole_receiver, isMuve]
          | cons first remaining =>
              -- trans unfolds to trans first.2 role for non-participant
              rw [Trans.trans.eq_5]
              simp only [hrole_sender, Bool.false_eq_true, ↓reduceIte, hrole_receiver]
              have hnotpart_cont : ¬ part_of2 role first.2 := by
                intro hcont
                have hmem : (first.1, first.2) ∈ first :: remaining := by simp
                exact hnotpart (part_of2.intro _ (part_ofF.comm_branch sender receiver
                  first.1 first.2 (first :: remaining) hmem hcont))
              -- Extract structural properties for first.2
              have hne_cont : first.2.allCommsNonEmpty = true := by
                simp only [GlobalType.allCommsNonEmpty, GlobalType.allCommsNonEmptyBranches,
                           Bool.and_eq_true] at hne
                exact hne.2.1
              have hnsc_cont : first.2.noSelfComm = true := by
                simp only [GlobalType.noSelfComm, GlobalType.noSelfCommBranches,
                           Bool.and_eq_true] at hnsc
                exact hnsc.2.1
              have hlt : sizeOf first.2 < sizeOf (GlobalType.comm sender receiver (first :: remaining)) :=
                sizeOf_pair_snd_lt_comm sender receiver first remaining
              exact trans_muve_of_not_part_of2_aux first.2 role hnotpart_cont hne_cont hnsc_cont
termination_by sizeOf g
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1, Label._sizeOf_1]
  all_goals omega

theorem trans_muve_of_not_part_of2 (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g) (hwf : g.wellFormed = true) :
    isMuve (Trans.trans g role) = true := by
  -- Extract structural properties from wellFormed
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact trans_muve_of_not_part_of2_aux g role hnotpart hwf.1.1.2 hwf.1.2

/-- Relation for proving EQ2 .end X for closed muve types.
    ClosedMuveRel a b holds when a = .end and b is a closed muve type. -/
private def ClosedMuveRel : LocalTypeR → LocalTypeR → Prop := fun a b =>
  a = .end ∧ isMuve b = true ∧ isClosed b = true

/-- Convert isClosed = true to freeVars = []. -/
private theorem isClosed_eq_true_iff (lt : LocalTypeR) :
    isClosed lt = true ↔ lt.freeVars = [] := by
  simp only [isClosed, beq_iff_eq]

/-- For closed muve types, substituting into the body keeps it closed muve.
    This is key for the mu case of the coinduction proof. -/
private theorem closed_muve_substitute_mu (t : String) (body : LocalTypeR)
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
private theorem ClosedMuveRel_postfix :
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

/-! ## EQ_end: Non-participants project to EEnd

This section establishes that if a role doesn't participate in a global protocol,
then the projection function `trans` produces a local type EQ2-equivalent to EEnd.

This corresponds to Coq's `EQ_end` theorem from indProj.v (lines 147-152). -/

/-- Non-participants project to EEnd (EQ2-equivalent).

If a role doesn't participate in the global type and the global type is well-formed
(closed, all comms have branches), then trans g role is EQ2-equivalent to .end.

### Proof Strategy

1. Show that `trans` on a non-participant produces a "muve" type (mu-var-end chain):
   - `trans_muve_of_not_part_of2`: if ¬part_of2 role g, then isMuve (trans g role)

2. Show that for closed global types, trans produces closed muve local types:
   - wellFormed includes allVarsBound, so trans produces closed types

3. Apply coinduction: ClosedMuveRel is a post-fixpoint of EQ2F

4. Since trans g role is closed muve, ClosedMuveRel .end (trans g role) holds

5. By EQ2_coind, EQ2 .end (trans g role)

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:147-152`. -/
theorem EQ_end (role : String) (g : GlobalType)
    (hnotpart : ¬ part_of2 role g)
    (hwf : g.wellFormed = true) :
    EQ2 .end (trans g role) := by
  -- Step 1: trans g role is muve
  have hmuve : isMuve (trans g role) = true := trans_muve_of_not_part_of2 g role hnotpart hwf
  -- Step 2: trans g role is closed (wellFormed implies allVarsBound)
  have hclosed : isClosed (trans g role) = true := by
    rw [isClosed_eq_true_iff]
    -- wellFormed implies g is closed, and trans preserves closedness
    -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    have hbound := hwf.1.1.1
    -- trans of a closed global type is a closed local type
    -- This follows from trans_freeVars_subset
    have hsub := trans_freeVars_subset g role
    -- If g.freeVars = [] (from allVarsBound), then (trans g role).freeVars ⊆ [] = []
    have gclosed : g.freeVars = [] := allVarsBound_nil_implies_freeVars_nil g hbound
    simp only [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have hgx := hsub hx
    simp only [gclosed, List.not_mem_nil] at hgx
  -- Step 3: Apply coinduction
  have hinR : ClosedMuveRel .end (trans g role) := ⟨rfl, hmuve, hclosed⟩
  exact EQ2_coind ClosedMuveRel_postfix .end (trans g role) hinR

/-! ## CProject and Muve Types

When a role doesn't participate in a global type, the CProject relation constrains
the local type candidate to be a "muve" type (mu-var-end chain). This is because:
- For non-participant comm nodes, CProjectF requires AllBranchesProj to the same candidate
- For mu nodes, CProjectF requires the body projection
- The only leaf types in CProject are .end (for .end) and .var t (for .var t)

Combined with wellFormedness (which implies closedness), this means non-participant
projections are closed muve types, which are EQ2-equivalent to .end. -/

/-- Auxiliary: Non-participant projections are muve types.
    Uses structural properties only (allCommsNonEmpty, noSelfComm) to avoid the semantic gap
    where body.allVarsBound [t] does not imply body.allVarsBound []. -/
private theorem CProject_muve_of_not_part_of2_aux : (g : GlobalType) → (role : String) → (lt : LocalTypeR) →
    CProject g role lt →
    ¬part_of2 role g →
    g.allCommsNonEmpty = true →
    isMuve lt = true
  | .end, _, lt, hproj, _, _ => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      cases lt with
      | «end» => rfl
      | _ => exact False.elim hF
  | .var _, _, lt, hproj, _, _ => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      cases lt with
      | var _ => rfl
      | _ => exact False.elim (by simp_all)
  | .mu t body, role, lt, hproj, hnotpart, hne => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      cases lt with
      | mu t' candBody =>
          simp only [isMuve]
          obtain ⟨_, _, hbody_proj⟩ := hF
          have hnotpart_body : ¬part_of2 role body := not_part_of2_mu hnotpart
          -- allCommsNonEmpty composes with mu
          have hne_body : body.allCommsNonEmpty = true := by
            simp only [GlobalType.allCommsNonEmpty] at hne; exact hne
          exact CProject_muve_of_not_part_of2_aux body role candBody hbody_proj hnotpart_body hne_body
      | «end» => exact False.elim (by simp_all)
      | var _ => exact False.elim (by simp_all)
      | send _ _ => exact False.elim (by simp_all)
      | recv _ _ => exact False.elim (by simp_all)
  | .comm _ _ [], _, _, _, _, hne => by
      -- Empty branches contradicts allCommsNonEmpty: hne contains true = false
      simp only [GlobalType.allCommsNonEmpty, List.isEmpty_nil, Bool.and_eq_true,
                 decide_eq_true_eq] at hne
      exact Bool.noConfusion hne.1
  | .comm sender receiver (first :: rest), role, lt, hproj, hnotpart, hne => by
      have hF := CProject_destruct hproj
      have hns : role ≠ sender := by
        intro heq; subst heq
        have hpart : part_of2 role (.comm role receiver (first :: rest)) :=
          part_of2.intro _ (part_ofF.comm_direct _ _ _ (by simp [is_participant]))
        exact hnotpart hpart
      have hnr : role ≠ receiver := by
        intro heq; subst heq
        have hpart : part_of2 role (.comm sender role (first :: rest)) :=
          part_of2.intro _ (part_ofF.comm_direct _ _ _ (by simp [is_participant]))
        exact hnotpart hpart
      dsimp only [CProjectF] at hF
      simp only [hns, hnr, ↓reduceIte] at hF
      -- hF : AllBranchesProj CProject (first :: rest) role lt
      have hmem : first ∈ first :: rest := by simp
      have hfirst_proj : CProject first.2 role lt := hF first hmem
      have hnotpart_first : ¬part_of2 role first.2 := by
        intro hpart
        have hpart_g : part_of2 role (.comm sender receiver (first :: rest)) :=
          part_of2.intro _ (part_ofF.comm_branch _ _ first.1 first.2 _ hmem hpart)
        exact hnotpart hpart_g
      -- allCommsNonEmpty composes with continuations
      have hne_first : first.2.allCommsNonEmpty = true := by
        simp only [GlobalType.allCommsNonEmpty, GlobalType.allCommsNonEmptyBranches,
                   Bool.and_eq_true] at hne
        exact hne.2.1
      exact CProject_muve_of_not_part_of2_aux first.2 role lt hfirst_proj hnotpart_first hne_first
termination_by g _ _ _ _ _ => sizeOf g
decreasing_by
  all_goals simp_wf
  all_goals
    simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1]
    omega

/-- Non-participant projections are muve types.

If a role doesn't participate in a global type, any CProject candidate
for that role must be a muve type (only mu/var/end constructors).

Proof by well-founded induction on global type size. -/
theorem CProject_muve_of_not_part_of2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (hwf : g.wellFormed = true) :
    isMuve lt = true := by
  have hne : g.allCommsNonEmpty = true := by
    -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  exact CProject_muve_of_not_part_of2_aux g role lt hproj hnotpart hne

/-- Auxiliary: Non-participant projections have free vars contained in bound vars.
    This is the generalized version that tracks bound variables through mu bindings.

    Key insight: allVarsBound bvars means freeVars ⊆ bvars. For mu, the bound var is
    added to bvars, allowing the recursive call to track that var properly. -/
private theorem CProject_freeVars_subset_bvars : (g : GlobalType) → (role : String) →
    (lt : LocalTypeR) → (bvars : List String) →
    CProject g role lt →
    ¬part_of2 role g →
    g.allVarsBound bvars = true →
    g.allCommsNonEmpty = true →
    ∀ v, v ∈ lt.freeVars → v ∈ bvars
  | .end, _, lt, _, hproj, _, _, _ => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      cases lt with
      | «end» => intro v hv; simp [LocalTypeR.freeVars] at hv
      | _ => exact False.elim hF
  | .var t, _, lt, bvars, hproj, _, havb, _ => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      cases lt with
      | var s =>
          intro v hv
          simp only [LocalTypeR.freeVars, List.mem_singleton] at hv
          -- hF should give us s = t (local var matches global var)
          -- But CProjectF at var gives just `true` for any local type matching structure
          -- Actually for var, CProjectF (var t) role lt = (lt = var t) in some sense
          -- Let's extract: hF tells us lt = var t, but we already have lt = var s from pattern match
          -- So s must equal t
          -- CProjectF for .var t gives: ∃ s, lt = var s ∧ s = t (simplified)
          simp only at hF
          -- From hF we get that lt must be var t
          -- Since we pattern matched lt = var s, we need s = t
          -- The hF for var case in CProjectF is: lt = .var t
          -- But we pattern matched lt = .var s, so...
          -- Actually, after cases lt with | var s =>, hF should imply s = t
          -- For var case, CProjectF (.var t) role (.var s) = (s = t)
          have hst : s = t := hF.symm
          subst hst
          subst hv
          -- Now we need to show t ∈ bvars
          simp only [GlobalType.allVarsBound] at havb
          simp only [List.contains] at havb
          rw [List.elem_eq_mem] at havb
          exact of_decide_eq_true havb
      | _ => exact False.elim (by simp_all)
  | .mu t body, role, lt, bvars, hproj, hnotpart, havb, hne => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      cases lt with
      | mu t' candBody =>
          obtain ⟨heq, _, hbody_proj⟩ := hF
          subst heq
          intro v hv
          -- freeVars of mu t candBody = candBody.freeVars.filter (· != t)
          simp only [LocalTypeR.freeVars, List.mem_filter, bne_iff_ne, ne_eq] at hv
          obtain ⟨hv_in, hv_ne⟩ := hv
          -- By IH, candBody.freeVars ⊆ t :: bvars
          have hnotpart_body : ¬part_of2 role body := not_part_of2_mu hnotpart
          simp only [GlobalType.allVarsBound] at havb
          simp only [GlobalType.allCommsNonEmpty] at hne
          have hv_in_extended :=
            CProject_freeVars_subset_bvars body role candBody (t :: bvars)
              hbody_proj hnotpart_body havb hne v hv_in
          -- hv_in_extended : v ∈ t :: bvars
          simp only [List.mem_cons] at hv_in_extended
          cases hv_in_extended with
          | inl heq => exact False.elim (hv_ne heq)
          | inr hin => exact hin
      | «end» => exact False.elim (by simp_all)
      | var _ => exact False.elim (by simp_all)
      | send _ _ => exact False.elim (by simp_all)
      | recv _ _ => exact False.elim (by simp_all)
  | .comm _ _ [], _, _, _, _, _, _, hne => by
      simp only [GlobalType.allCommsNonEmpty, List.isEmpty_nil, Bool.and_eq_true,
                 decide_eq_true_eq] at hne
      exact Bool.noConfusion hne.1
  | .comm sender receiver (first :: rest), role, lt, bvars, hproj, hnotpart, havb, hne => by
      have hF := CProject_destruct hproj
      have hns : role ≠ sender := by
        intro heq; subst heq
        have hpart : part_of2 role (.comm role receiver (first :: rest)) :=
          part_of2.intro _ (part_ofF.comm_direct _ _ _ (by simp [is_participant]))
        exact hnotpart hpart
      have hnr : role ≠ receiver := by
        intro heq; subst heq
        have hpart : part_of2 role (.comm sender role (first :: rest)) :=
          part_of2.intro _ (part_ofF.comm_direct _ _ _ (by simp [is_participant]))
        exact hnotpart hpart
      dsimp only [CProjectF] at hF
      simp only [hns, hnr, ↓reduceIte] at hF
      have hmem : first ∈ first :: rest := by simp
      have hfirst_proj : CProject first.2 role lt := hF first hmem
      have hnotpart_first : ¬part_of2 role first.2 := by
        intro hpart
        have hpart_g : part_of2 role (.comm sender receiver (first :: rest)) :=
          part_of2.intro _ (part_ofF.comm_branch _ _ first.1 first.2 _ hmem hpart)
        exact hnotpart hpart_g
      have havb_first : first.2.allVarsBound bvars = true := by
        simp only [GlobalType.allVarsBound, GlobalType.allVarsBoundBranches,
                   Bool.and_eq_true] at havb
        exact havb.1
      have hne_first : first.2.allCommsNonEmpty = true := by
        simp only [GlobalType.allCommsNonEmpty, GlobalType.allCommsNonEmptyBranches,
                   Bool.and_eq_true] at hne
        exact hne.2.1
      exact CProject_freeVars_subset_bvars first.2 role lt bvars
        hfirst_proj hnotpart_first havb_first hne_first
termination_by g _ _ _ _ _ _ _ => sizeOf g
decreasing_by
  all_goals simp_wf
  all_goals
    simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1]
    omega

/-- Auxiliary: Non-participant projections are closed types.
    Uses allVarsBound to show freeVars = [] for the candidate.

    Key insight: CProject_freeVars_subset_bvars with bvars = [] gives freeVars ⊆ [],
    which means freeVars = []. -/
private theorem CProject_closed_of_not_part_of2_aux (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (havb : g.allVarsBound = true)
    (hne : g.allCommsNonEmpty = true) :
    isClosed lt = true := by
  simp only [isClosed, beq_iff_eq, List.isEmpty_iff]
  have hsub := CProject_freeVars_subset_bvars g role lt [] hproj hnotpart havb hne
  exact List.subset_nil.mp (fun v hv => hsub v hv)

/-- Non-participant projections are closed types.

If a role doesn't participate in a well-formed (closed) global type,
any CProject candidate for that role must be closed (no free variables).

Proof by well-founded induction on global type size. -/
theorem CProject_closed_of_not_part_of2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (hwf : g.wellFormed = true) :
    isClosed lt = true := by
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact CProject_closed_of_not_part_of2_aux g role lt hproj hnotpart hwf.1.1.1 hwf.1.1.2

/-- Helper: sizeOf a member's continuation is less than sizeOf the list. -/
private theorem sizeOf_mem_snd_lt {branches : List (Label × GlobalType)} {pair : Label × GlobalType}
    (hmem : pair ∈ branches) :
    sizeOf pair.2 < sizeOf branches := by
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]
          omega
      | tail _ hmem' =>
          have ih' := ih hmem'
          simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1] at ih' ⊢
          omega

/-- Helper: sizeOf a member's continuation is less than sizeOf the comm. -/
private theorem sizeOf_mem_snd_lt_comm {sender receiver : String} {branches : List (Label × GlobalType)}
    {pair : Label × GlobalType} (hmem : pair ∈ branches) :
    sizeOf pair.2 < sizeOf (GlobalType.comm sender receiver branches) := by
  have h1 := sizeOf_mem_snd_lt hmem
  have hcomm : sizeOf (GlobalType.comm sender receiver branches) =
      1 + sizeOf sender + sizeOf receiver + sizeOf branches := by
    simp only [GlobalType.comm.sizeOf_spec]
  omega

/-- Helper: allCommsNonEmpty for a branch list implies allCommsNonEmpty for each member. -/
private theorem allCommsNonEmpty_of_mem {branches : List (Label × GlobalType)} {pair : Label × GlobalType}
    (hmem : pair ∈ branches) (hne : allCommsNonEmptyBranches branches = true) :
    pair.2.allCommsNonEmpty = true := by
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [GlobalType.allCommsNonEmptyBranches, Bool.and_eq_true] at hne
      cases hmem with
      | head => exact hne.1
      | tail _ hmem' => exact ih hmem' hne.2

/-- Helper: noSelfComm for a branch list implies noSelfComm for each member. -/
private theorem noSelfComm_of_mem {branches : List (Label × GlobalType)} {pair : Label × GlobalType}
    (hmem : pair ∈ branches) (hnsc : noSelfCommBranches branches = true) :
    pair.2.noSelfComm = true := by
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [GlobalType.noSelfCommBranches, Bool.and_eq_true] at hnsc
      cases hmem with
      | head => exact hnsc.1
      | tail _ hmem' => exact ih hmem' hnsc.2

/-- Auxiliary: Participant projections are NOT muve types.
    This is the converse of CProject_muve_of_not_part_of2.

    If a role participates in a well-formed global type and has a valid projection,
    then the projection must have send/recv at some level (not purely mu/var/end). -/
private theorem CProject_not_muve_of_part_of2_aux : (g : GlobalType) → (role : String) →
    (lt : LocalTypeR) →
    CProject g role lt →
    part_of2 role g →
    g.allCommsNonEmpty = true →
    isMuve lt = false
  | .end, role, lt, hproj, hpart, _ => by
      -- part_of2 role .end is impossible
      exact False.elim (not_part_of2_end role hpart)
  | .var t, role, lt, hproj, hpart, _ => by
      -- part_of2 role (.var t) is impossible
      exact False.elim (not_part_of2_var role t hpart)
  | .mu t body, role, lt, hproj, hpart, hne => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      cases lt with
      | mu t' candBody =>
          obtain ⟨heq, _, hbody_proj⟩ := hF
          subst heq
          simp only [isMuve]
          -- part_of2 for mu means part_of2 for body
          have hpart_body := part_of2_mu_inv hpart
          have hne_body : body.allCommsNonEmpty = true := by
            simp only [GlobalType.allCommsNonEmpty] at hne; exact hne
          exact CProject_not_muve_of_part_of2_aux body role candBody hbody_proj hpart_body hne_body
      | «end» => exact False.elim (by simp_all)
      | var _ => exact False.elim (by simp_all)
      | send _ _ => rfl
      | recv _ _ => rfl
  | .comm _ _ [], _, _, _, _, hne => by
      simp only [GlobalType.allCommsNonEmpty, List.isEmpty_nil, Bool.and_eq_true,
                 decide_eq_true_eq] at hne
      exact Bool.noConfusion hne.1
  | .comm sender receiver (first :: rest), role, lt, hproj, hpart, hne => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      -- First handle the role conditions, then case on lt
      by_cases hs : role = sender
      · -- Role is sender: CProjectF expects send type
        subst hs
        simp only [beq_self_eq_true, ↓reduceIte] at hF
        cases lt with
        | send _ _ => rfl
        | _ => exact False.elim hF
      · by_cases hr : role = receiver
        · -- Role is receiver: CProjectF expects recv type
          subst hr
          simp only [if_neg hs, if_pos rfl] at hF
          cases lt with
          | recv _ _ => rfl
          | _ => exact False.elim hF
        · -- Role is neither sender nor receiver: AllBranchesProj applies
          simp only [if_neg hs, if_neg hr] at hF
          -- hF : AllBranchesProj CProject (first :: rest) role lt
          -- From part_of2, role participates somewhere
          have hcomm_inv := part_of2_comm_inv hpart
          cases hcomm_inv with
          | inl hparticipant =>
              simp only [is_participant, Bool.or_eq_true, beq_iff_eq] at hparticipant
              cases hparticipant with
              | inl hsend => exact False.elim (hs hsend)
              | inr hrecv => exact False.elim (hr hrecv)
          | inr hexists =>
              -- Role participates in some branch
              obtain ⟨label, cont, hmem, hpart_cont⟩ := hexists
              have hcont_proj : CProject cont role lt := hF (label, cont) hmem
              have hne_branches : allCommsNonEmptyBranches (first :: rest) = true := by
                simp only [GlobalType.allCommsNonEmpty, GlobalType.allCommsNonEmptyBranches,
                           Bool.and_eq_true] at hne
                simp only [GlobalType.allCommsNonEmptyBranches, Bool.and_eq_true]
                exact ⟨hne.2.1, hne.2.2⟩
              have hne_cont : cont.allCommsNonEmpty = true := allCommsNonEmpty_of_mem hmem hne_branches
              -- By IH, if cont has participation and projects to lt, then isMuve lt = false
              exact CProject_not_muve_of_part_of2_aux cont role lt hcont_proj hpart_cont hne_cont
termination_by g _ _ _ _ _ => sizeOf g
decreasing_by
  all_goals simp_wf
  all_goals first
    | simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1]; omega
    | -- For the comm case where cont comes from membership
      have hmem_lt := sizeOf_mem_snd_lt (by assumption : (_ : Label × GlobalType) ∈ (_ :: _))
      simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1] at hmem_lt ⊢
      omega

/-- Participant projections are NOT muve types.

If a role participates in a well-formed global type and has a valid projection,
then the projection must have send/recv at some level (not purely mu/var/end). -/
theorem CProject_not_muve_of_part_of2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hpart : part_of2 role g)
    (hwf : g.wellFormed = true) :
    isMuve lt = false := by
  have hne : g.allCommsNonEmpty = true := by
    -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  exact CProject_not_muve_of_part_of2_aux g role lt hproj hpart hne

/-- If a role participates on some path (part_of2) and there is a valid projection (CProject),
    then the role participates on all branches (part_of_all2).

This follows from the coherence requirement in CProject for non-participants:
AllBranchesProj requires all branches to project to the same local type.

If role participates on some path but not all paths, then:
- Some branch would have the role as participant (giving send/recv)
- Some branch would have the role as non-participant (giving a muve type)
- These would need to be the same (AllBranchesProj), which is impossible

Proof by well-founded induction on global type size, using CProject structure. -/
private theorem CProject_part_of2_implies_part_of_all2_aux : (g : GlobalType) → (role : String) →
    (lt : LocalTypeR) →
    CProject g role lt →
    part_of2 role g →
    g.allCommsNonEmpty = true →
    g.noSelfComm = true →
    part_of_all2 role g
  | .end, role, _, _, hpart, _, _ =>
      False.elim (not_part_of2_end role hpart)
  | .var t, role, _, _, hpart, _, _ =>
      False.elim (not_part_of2_var role t hpart)
  | .mu t body, role, lt, hproj, hpart, hne, hnsc => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      cases lt with
      | mu t' candBody =>
          obtain ⟨heq, _, hbody_proj⟩ := hF
          subst heq
          have hpart_body := part_of2_mu_inv hpart
          have hne_body : body.allCommsNonEmpty = true := by
            simp only [GlobalType.allCommsNonEmpty] at hne; exact hne
          have hnsc_body : body.noSelfComm = true := by
            simp only [GlobalType.noSelfComm] at hnsc; exact hnsc
          have ih := CProject_part_of2_implies_part_of_all2_aux body role candBody
            hbody_proj hpart_body hne_body hnsc_body
          exact part_of_all2.intro _ (part_of_allF.mu t body ih)
      | «end» => exact False.elim (by simp_all)
      | var _ => exact False.elim (by simp_all)
      | send _ _ => exact False.elim (by simp_all)
      | recv _ _ => exact False.elim (by simp_all)
  | .comm _ _ [], _, _, _, _, hne, _ => by
      simp only [GlobalType.allCommsNonEmpty, List.isEmpty_nil, Bool.and_eq_true,
                 decide_eq_true_eq] at hne
      exact Bool.noConfusion hne.1
  | .comm sender receiver (first :: rest), role, lt, hproj, hpart, hne, hnsc => by
      have hF := CProject_destruct hproj
      dsimp only [CProjectF] at hF
      by_cases hs : role = sender
      · -- Direct participant (sender)
        exact part_of_all2.intro _ (part_of_allF.comm_direct sender receiver (first :: rest)
          (by simp [is_participant, hs]))
      · by_cases hr : role = receiver
        · -- Direct participant (receiver)
          exact part_of_all2.intro _ (part_of_allF.comm_direct sender receiver (first :: rest)
            (by simp [is_participant, hr]))
        · -- Non-direct participant: must participate in all branches
          simp only [if_neg hs, if_neg hr] at hF
          -- hF : AllBranchesProj CProject (first :: rest) role lt
          -- Need to show part_of_all2 for all branches
          apply part_of_all2.intro _ (part_of_allF.comm_all_branches sender receiver (first :: rest) _)
          intro pair hmem
          -- Get CProject for this branch
          have hpair_proj : CProject pair.2 role lt := hF pair hmem
          -- Need to show part_of_all2 role pair.2
          -- First, show part_of2 role pair.2
          -- Key: if ¬part_of2 role pair.2, then isMuve lt (by CProject_muve_of_not_part_of2_aux)
          -- But from the witness branch where role participates, isMuve lt = false
          -- Contradiction
          -- First reconstruct branch-wise predicates
          have hne_branches : allCommsNonEmptyBranches (first :: rest) = true := by
            simp only [GlobalType.allCommsNonEmpty, GlobalType.allCommsNonEmptyBranches,
                       Bool.and_eq_true] at hne
            simp only [GlobalType.allCommsNonEmptyBranches, Bool.and_eq_true]
            exact ⟨hne.2.1, hne.2.2⟩
          have hnsc_branches : noSelfCommBranches (first :: rest) = true := by
            simp only [GlobalType.noSelfComm, GlobalType.noSelfCommBranches,
                       Bool.and_eq_true] at hnsc
            simp only [GlobalType.noSelfCommBranches, Bool.and_eq_true]
            exact ⟨hnsc.2.1, hnsc.2.2⟩
          by_cases hpart_pair : part_of2 role pair.2
          · -- This branch has participation, recurse
            have hne_pair : pair.2.allCommsNonEmpty = true := allCommsNonEmpty_of_mem hmem hne_branches
            have hnsc_pair : pair.2.noSelfComm = true := noSelfComm_of_mem hmem hnsc_branches
            exact CProject_part_of2_implies_part_of_all2_aux pair.2 role lt
              hpair_proj hpart_pair hne_pair hnsc_pair
          · -- This branch has no participation
            -- By CProject_muve_of_not_part_of2_aux, isMuve lt = true
            have hne_pair : pair.2.allCommsNonEmpty = true := allCommsNonEmpty_of_mem hmem hne_branches
            have hmuve : isMuve lt = true :=
              CProject_muve_of_not_part_of2_aux pair.2 role lt hpair_proj hpart_pair hne_pair
            -- But from hpart (part_of2 for the comm), role participates in some branch
            have hcomm_inv := part_of2_comm_inv hpart
            cases hcomm_inv with
            | inl hparticipant =>
                simp only [is_participant, Bool.or_eq_true, beq_iff_eq] at hparticipant
                cases hparticipant with
                | inl hsend => exact False.elim (hs hsend)
                | inr hrecv => exact False.elim (hr hrecv)
            | inr hexists =>
                -- Some branch has participation
                obtain ⟨label, cont, hmem_wit, hpart_wit⟩ := hexists
                have hwit_proj : CProject cont role lt := hF (label, cont) hmem_wit
                have hne_wit : cont.allCommsNonEmpty = true := allCommsNonEmpty_of_mem hmem_wit hne_branches
                -- For the witness branch, isMuve lt = false (because role participates there)
                have hnot_muve : isMuve lt = false :=
                  CProject_not_muve_of_part_of2_aux cont role lt hwit_proj hpart_wit hne_wit
                -- Contradiction: isMuve lt can't be both true and false
                rw [hmuve] at hnot_muve
                exact Bool.noConfusion hnot_muve
termination_by g _ _ _ _ _ _ => sizeOf g
decreasing_by
  all_goals simp_wf
  all_goals first
    | simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1]; omega
    | -- For the comm case where cont comes from membership
      have hmem_lt := sizeOf_mem_snd_lt (by assumption : (_ : Label × GlobalType) ∈ (_ :: _))
      simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1] at hmem_lt ⊢
      omega

theorem CProject_part_of2_implies_part_of_all2 (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hpart : part_of2 role g)
    (hwf : g.wellFormed = true) :
    part_of_all2 role g := by
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact CProject_part_of2_implies_part_of_all2_aux g role lt hproj hpart hwf.1.1.2 hwf.1.2

/-- Classification: a role either participates or projects to EEnd.

This is the key structural lemma for projection proofs. It corresponds to
Coq's `part_of2_or_end` from intermediateProj.v (lines 193-200).

For a role in a global type with a CProject proof:
- Either the role participates (part_of_all2), OR
- The projection is EQ2-equivalent to EEnd

### Proof Strategy

1. Case split on whether role participates: `part_of2 role g` or `¬part_of2 role g`
2. **Participant case**: Show `part_of_all2 role g` using `CProject_part_of2_implies_part_of_all2`
3. **Non-participant case**:
   - By `CProject_muve_of_not_part_of2`: lt is muve
   - By `CProject_closed_of_not_part_of2`: lt is closed
   - By coinduction with `ClosedMuveRel`: `EQ2 lt .end`

Note: We prove `EQ2 lt .end` (not `EQ2 .end lt`) because we have the closed muve
property for lt directly from CProject. -/
theorem part_of2_or_end (role : String) (g : GlobalType) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hwf : g.wellFormed = true) :
    part_of_all2 role g ∨ EQ2 lt .end := by
  -- Case split on participation
  by_cases hpart : part_of2 role g
  · -- Participant case: use coherence axiom
    left
    exact CProject_part_of2_implies_part_of_all2 g role lt hproj hpart hwf
  · -- Non-participant case: show EQ2 lt .end
    right
    -- lt is muve and closed
    have hmuve : isMuve lt = true := CProject_muve_of_not_part_of2 g role lt hproj hpart hwf
    have hclosed : isClosed lt = true := CProject_closed_of_not_part_of2 g role lt hproj hpart hwf
    -- Apply coinduction using ClosedMuveRel (but with roles swapped)
    -- ClosedMuveRel is defined as: a = .end ∧ isMuve b ∧ isClosed b
    -- We need EQ2 lt .end, so we define a symmetric version
    let ClosedMuveRelSym : LocalTypeR → LocalTypeR → Prop := fun a b =>
      isMuve a = true ∧ isClosed a = true ∧ b = .end
    -- Show ClosedMuveRelSym is a post-fixpoint of EQ2F
    have hpostfix : ∀ a b, ClosedMuveRelSym a b → EQ2F ClosedMuveRelSym a b := by
      intro a b ⟨hmuve_a, hclosed_a, hb⟩
      subst hb  -- b = .end
      cases a with
      | «end» => simp only [EQ2F]  -- EQ2F _ .end .end = True
      | var t =>
          -- var has free vars, contradicts hclosed_a
          -- isClosed (.var t) = ([t] == []) = false ≠ true
          simp only [isClosed, LocalTypeR.freeVars, beq_iff_eq] at hclosed_a
          -- hclosed_a : [t] = []
          exact nomatch hclosed_a
      | mu t body =>
          -- EQ2F ClosedMuveRelSym (.mu t body) .end = ClosedMuveRelSym (body.substitute t (.mu t body)) .end
          simp only [EQ2F]
          simp only [isMuve] at hmuve_a
          have ⟨hmuve', hclosed'⟩ := closed_muve_substitute_mu t body hmuve_a hclosed_a
          exact ⟨hmuve', hclosed', rfl⟩
      | send _ _ => simp [isMuve] at hmuve_a
      | recv _ _ => simp [isMuve] at hmuve_a
    -- Apply coinduction
    have hinR : ClosedMuveRelSym lt .end := ⟨hmuve, hclosed, rfl⟩
    exact EQ2_coind hpostfix lt .end hinR

/-! ## Projection-EQ2 Congruence Lemmas

The following lemmas establish that CProject and trans interact coherently with EQ2.
These correspond to key lemmas from the Coq development:
- `proj_proj`: if CProject g p e, then EQ2 e (trans g p)
- `Project_EQ2`: if CProject g p e0 and EQ2 e0 e1, then CProject g p e1

### CProject_implies_EQ2_trans Proof Strategy

The proof uses coinduction on EQ2 with the relation:
`CProjectTransRel lt cand := ∃ g role, CProject g role lt ∧ cand = trans g role`

For end, var, and participant comm cases, CProject and trans have matching structures.
For non-participants, we use `part_of2_or_end` + `EQ_end` to show EQ2 lt .end ∧ EQ2 .end (trans g role).
The mu case requires coinduction up-to with substitution lemmas.

See `subject_reduction/theories/Projection/indProj.v:221-260` for the Coq reference. -/

/-! ### Helper Lemmas for CProject_implies_EQ2_trans

The following helper lemmas and axioms support the proof of the main theorem. -/

/-- Helper: part_of_all2 implies part_of2 (requires wellFormed for non-empty branches).

If a role participates on all branches, it certainly participates on some path.
The wellFormed hypothesis ensures branches are non-empty.

### Proof Strategy

Use well-founded induction on global type size:
- `comm_direct`: Trivially get `part_of2` via `part_of2.intro (.comm_direct ...)`
- `comm_all_branches`: wellFormed ensures branches ≠ [], so pick first branch.
  By IH on the continuation, get `part_of2 role cont`. Then construct
  `part_of2.intro (.comm_branch ...)` with the membership witness.
- `mu`: By IH on body, get `part_of2 role body`. Then construct
  `part_of2.intro (.mu ...)`.

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:180-192`.

We use an auxiliary version with weaker preconditions (just allCommsNonEmpty)
to avoid the semantic gap where body.allVarsBound [] cannot be proven from
(mu t body).wellFormed. -/
private theorem part_of_all2_implies_part_of2_aux (role : String) (g : GlobalType)
    (h : part_of_all2 role g)
    (hne : g.allCommsNonEmpty = true) : part_of2 role g := by
  match g with
  | .end =>
      exact absurd h (not_part_of_all2_end role)
  | .var t =>
      exact absurd h (not_part_of_all2_var role t)
  | .mu t body =>
      have hbody := part_of_all2_mu_inv h
      have hne_body : body.allCommsNonEmpty = true := by
        simp only [GlobalType.allCommsNonEmpty] at hne
        exact hne
      have ih := part_of_all2_implies_part_of2_aux role body hbody hne_body
      exact part_of2.intro _ (part_ofF.mu t body ih)
  | .comm sender receiver branches =>
      have h_or := part_of_all2_comm_inv h
      cases h_or with
      | inl hpart =>
          exact part_of2.intro _ (part_ofF.comm_direct sender receiver branches hpart)
      | inr hall =>
          cases branches with
          | nil =>
              simp only [GlobalType.allCommsNonEmpty, List.isEmpty_nil, Bool.and_eq_true] at hne
              exact absurd hne.1 (by decide)
          | cons first remaining =>
              have hmem : first ∈ first :: remaining := by simp only [List.mem_cons, true_or]
              have hpair : part_of_all2 role first.2 := hall first hmem
              have hne_cont : first.2.allCommsNonEmpty = true := by
                simp only [GlobalType.allCommsNonEmpty, GlobalType.allCommsNonEmptyBranches,
                           Bool.and_eq_true] at hne
                exact hne.2.1
              have ih := part_of_all2_implies_part_of2_aux role first.2 hpair hne_cont
              exact part_of2.intro _ (part_ofF.comm_branch sender receiver first.1 first.2 (first :: remaining) hmem ih)
termination_by sizeOf g
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp only [sizeOf, GlobalType._sizeOf_1, List._sizeOf_1, Prod._sizeOf_1, Label._sizeOf_1]
  all_goals omega

theorem part_of_all2_implies_part_of2 (role : String) (g : GlobalType)
    (h : part_of_all2 role g)
    (hwf : g.wellFormed = true) : part_of2 role g := by
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact part_of_all2_implies_part_of2_aux role g h hwf.1.1.2

/-- Helper: if CProject gives lt and role doesn't participate, then lt is EQ2 to trans.

This uses the muve/closed infrastructure from EQ_end and part_of2_or_end.

#### Proof Outline

1. By `part_of2_or_end`, we get `part_of_all2 role g ∨ EQ2 lt .end`
2. The Left case contradicts `hnotpart` via `part_of_all2_implies_part_of2`
3. The Right case: chain `EQ2 lt .end` with `EQ2 .end (trans g role)` from `EQ_end` -/
private theorem CProject_implies_EQ2_trans_nonpart (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (hwf : g.wellFormed = true) :
    EQ2 lt (trans g role) := by
  -- By part_of2_or_end, we get EQ2 lt .end
  have h_or := part_of2_or_end role g lt hproj hwf
  cases h_or with
  | inl hpart_all => exact absurd (part_of_all2_implies_part_of2 role g hpart_all hwf) hnotpart
  | inr hlt_end =>
      -- hlt_end : EQ2 lt .end
      -- By EQ_end, we get EQ2 .end (trans g role)
      have hend_trans := EQ_end role g hnotpart hwf
      -- Chain: EQ2 lt .end ∧ EQ2 .end (trans g role) → EQ2 lt (trans g role)
      exact EQ2_trans hlt_end hend_trans

/-! ### Main Theorem: CProject_implies_EQ2_trans -/

/-! #### Proof Strategy (Coinduction)

Define the relation:
```
CProjectTransRel a b := ∃ g role, CProject g role a ∧ b = trans g role
```

Show CProjectTransRel is a post-fixpoint of EQ2F by case analysis on CProject:
- **end**: a = .end, trans = .end, EQ2F trivial
- **var**: a = .var t, trans = .var t, EQ2F trivial
- **mu**: a = .mu t abody, trans = if lcontractive then .mu t (trans body) else .end
  Use EQ2F_mu case with IH on body
- **comm participant**: role is sender/receiver, trans picks matching send/recv
  Use BranchesRel with IH on branches
- **comm non-participant**: AllBranchesProj means lt consistent
  Use CProject_implies_EQ2_trans_nonpart

See `subject_reduction/theories/Projection/indProj.v:221-260` for the Coq proof. -/

/-! ### Constructor Agreement Lemmas (Well-Founded Induction)

These lemmas prove that when CProject produces a specific constructor (.end, .var),
trans also produces that same constructor. Proved by well-founded induction on the
global type size, NOT using the coinductive theorem.

This breaks the circularity: CProjectTransRel_postfix needs to know that trans produces
the same constructor as CProject, but CProject_implies_EQ2_trans depends on CProjectTransRel_postfix. -/

/-- If CProject g role .end, then trans g role = .end.
    Proved by well-founded induction on g. -/
private theorem CProject_end_trans_end (g : GlobalType) (role : String)
    (h : CProject g role .end) : trans g role = .end := by
  -- Destruct to get CProjectF structure
  have hf := CProject_destruct h
  match g with
  | .end =>
      -- trans .end role = .end (by definition)
      simp only [Trans.trans]
  | .var v =>
      -- CProjectF (.var v) _ .end requires .var v = .end - contradiction
      simp only [CProjectF] at hf
  | .mu t body =>
      -- CProjectF (.mu t body) _ .end requires .mu t body matches .mu _ _ - contradiction
      simp only [CProjectF] at hf
  | .comm sender receiver gbs =>
      -- CProjectF (.comm ...) role .end depends on role's participation
      simp only [CProjectF] at hf
      -- After simp, we have: hf : if role = sender then ... else if role = receiver then ... else AllBranchesProj
      -- Use by_cases to split on role participation
      by_cases hrs : role = sender
      · -- role = sender: CProjectF match on .end with .send pattern gives False
        -- simp automatically closes goal via False hypothesis
        simp only [if_pos hrs] at hf
      · by_cases hrr : role = receiver
        · -- role = receiver: CProjectF match on .end with .recv pattern gives False
          simp only [if_neg hrs, if_pos hrr] at hf
        · -- The remaining case is non-participant: hf is AllBranchesProj CProject gbs role .end
          simp only [if_neg hrs, if_neg hrr] at hf
          -- trans (.comm ...) role = trans first.2 role (if non-empty) or .end (if empty)
          have htrans := trans_comm_other sender receiver role gbs hrs hrr
          cases hgbs : gbs with
          | nil =>
              -- Empty branches: trans returns .end
              simp only [hgbs] at htrans
              exact htrans
          | cons first rest =>
              -- Non-empty: trans returns trans first.2 role
              simp only [hgbs] at htrans
              -- hf : AllBranchesProj CProject (first :: rest) role .end
              -- So CProject first.2 role .end
              have hfirst : CProject first.2 role .end := by
                apply hf first
                rw [hgbs]
                exact List.Mem.head rest
              -- By IH, trans first.2 role = .end
              have ih := CProject_end_trans_end first.2 role hfirst
              simp only [htrans, ih]
termination_by sizeOf g
decreasing_by
  all_goals simp_wf; simp_all only [sizeOf, Prod._sizeOf_1, List._sizeOf_1, GlobalType.comm.sizeOf_spec]; omega

/-- If CProject g role (.var v) and g has non-empty branches, then trans g role = .var v.
    Proved by well-founded induction on g.
    The allCommsNonEmpty precondition ensures branches are non-empty. -/
private theorem CProject_var_trans_var (g : GlobalType) (role : String) (v : String)
    (h : CProject g role (.var v)) (hwf : g.allCommsNonEmpty = true) : trans g role = .var v := by
  have hf := CProject_destruct h
  match g with
  | .end =>
      -- CProjectF .end _ (.var v) requires .end = .var v - contradiction
      simp only [CProjectF] at hf
  | .var v' =>
      -- CProjectF (.var v') _ (.var v) requires v' = v
      simp only [CProjectF] at hf
      -- trans (.var v') role = .var v'
      simp only [Trans.trans, hf]
  | .mu t body =>
      -- CProjectF (.mu t body) _ (.var v) requires .mu matches .var - contradiction
      simp only [CProjectF] at hf
  | .comm sender receiver gbs =>
      simp only [CProjectF] at hf
      -- Use by_cases to split on role participation
      by_cases hrs : role = sender
      · -- role = sender: CProjectF match on .var with .send pattern gives False
        simp only [if_pos hrs] at hf
      · by_cases hrr : role = receiver
        · -- role = receiver: CProjectF match on .var with .recv pattern gives False
          simp only [if_neg hrs, if_pos hrr] at hf
        · -- The remaining case is non-participant: hf is AllBranchesProj CProject gbs role (.var v)
          simp only [if_neg hrs, if_neg hrr] at hf
          -- From hwf, branches are non-empty
          simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true] at hwf
          -- hwf.1 : gbs.isEmpty = false
          cases hgbs : gbs with
          | nil =>
              -- Empty branches contradicts hwf.1 (nil.isEmpty = true = false)
              simp only [hgbs, List.isEmpty] at hwf
              -- hwf.1 : decide (true = false) = true, which is false = true
              have hcontra := hwf.1
              simp only [decide_eq_true_eq] at hcontra
              -- hcontra : true = false
              nomatch hcontra
          | cons first rest =>
              have htrans := trans_comm_other sender receiver role (first :: rest) hrs hrr
              have hfirst : CProject first.2 role (.var v) := by
                apply hf first
                rw [hgbs]
                exact List.Mem.head rest
              -- Extract allCommsNonEmpty for first.2
              have hwf_first : first.2.allCommsNonEmpty = true := by
                simp only [hgbs, allCommsNonEmptyBranches, Bool.and_eq_true] at hwf
                exact hwf.2.1
              have ih := CProject_var_trans_var first.2 role v hfirst hwf_first
              simp only [htrans, ih]
termination_by sizeOf g
decreasing_by
  all_goals simp_wf; simp_all only [sizeOf, Prod._sizeOf_1, List._sizeOf_1, GlobalType.comm.sizeOf_spec]; omega

/-! ### CProject-to-Trans structure extraction

When CProject produces a specific local type constructor (.send, .recv, .end, .var, .mu),
the global type must have a corresponding structure. These lemmas extract that structure
and show trans produces the matching constructor. -/

/-- If CProject g role (.send partner lbs) holds, then g must be a comm where role is sender
    (possibly through non-participant layers), and trans g role = .send partner (transBranches ...).

    This follows from CProjectF: only comm with role=sender produces .send.

    TODO: The proof requires careful handling of CProjectF reduction with nested if-then-else
    and match expressions. The key insight is that AllBranchesProj in non-participant cases
    requires wellFormedness to rule out empty branches. -/
private theorem CProject_send_implies_trans_send (g : GlobalType) (role : String)
    (partner : String) (lbs : List (Label × LocalTypeR))
    (hproj : CProject g role (.send partner lbs))
    (hwf : g.allCommsNonEmpty = true) :
    ∃ gbs', trans g role = .send partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      allCommsNonEmptyBranches gbs' = true := by
  have hf := CProject_destruct hproj
  match g with
  | .end =>
      -- CProjectF (.end, .send) is False
      simp only [CProjectF] at hf
  | .var v =>
      -- CProjectF (.var, .send) is False
      simp only [CProjectF] at hf
  | .mu t body =>
      -- CProjectF (.mu, .send) is False
      simp only [CProjectF] at hf
  | .comm sender receiver gbs =>
      simp only [CProjectF] at hf
      by_cases hrs : role = sender
      · -- Role is sender: direct case
        simp only [if_pos hrs] at hf
        obtain ⟨hpartner, hbranches⟩ := hf
        -- Witness: gbs with role = sender
        use gbs
        refine ⟨?_, ?_, ?_⟩
        · -- trans g role = .send partner (transBranches gbs role)
          rw [hrs, trans_comm_sender sender receiver sender gbs rfl, hpartner]
        · -- BranchesProjRel CProject gbs role lbs
          -- simp already substituted sender → role in hf using hrs
          exact hbranches
        · -- allCommsNonEmptyBranches gbs = true
          simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true, List.isEmpty_eq_false_iff] at hwf
          exact hwf.2
      · -- Role is not sender
        simp only [if_neg hrs] at hf
        by_cases hrr : role = receiver
        · -- Role is receiver but lt is .send - contradiction from CProjectF
          simp only [if_pos hrr] at hf
        · -- Non-participant case: hf is AllBranchesProj CProject gbs role (.send partner lbs)
          simp only [if_neg hrr] at hf
          -- In non-participant case, trans projects first branch
          have htrans := trans_comm_other sender receiver role gbs hrs hrr
          -- From hwf, we know gbs is non-empty
          simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true, List.isEmpty_eq_false_iff,
                     decide_eq_true_eq, ne_eq] at hwf
          obtain ⟨hnonempty, hrest⟩ := hwf
          cases hgbs : gbs with
          | nil =>
              -- Contradiction: gbs = [] but hwf says gbs is non-empty
              simp only [hgbs, not_true_eq_false] at hnonempty
          | cons first rest =>
              -- Non-empty: trans g role = trans first.2 role
              simp only [hgbs] at htrans hrest
              -- Get CProject first.2 role (.send partner lbs)
              have hfirst : CProject first.2 role (.send partner lbs) := by
                apply hf first
                rw [hgbs]
                exact List.Mem.head rest
              -- Get wellFormedness of first.2
              simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at hrest
              have hwf_first : first.2.allCommsNonEmpty = true := hrest.1
              -- Recursive call on first.2
              have ih := CProject_send_implies_trans_send first.2 role partner lbs hfirst hwf_first
              obtain ⟨gbs', htrans', hbranches', hwf'⟩ := ih
              use gbs'
              refine ⟨?_, ?_, ?_⟩
              · simp only [htrans, htrans']
              · exact hbranches'
              · exact hwf'
termination_by sizeOf g
decreasing_by
  all_goals simp_wf; simp_all only [sizeOf, Prod._sizeOf_1, List._sizeOf_1, GlobalType.comm.sizeOf_spec]; omega

/-- Symmetric version for recv. -/
private theorem CProject_recv_implies_trans_recv (g : GlobalType) (role : String)
    (partner : String) (lbs : List (Label × LocalTypeR))
    (hproj : CProject g role (.recv partner lbs))
    (hwf : g.allCommsNonEmpty = true) :
    ∃ gbs', trans g role = .recv partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      allCommsNonEmptyBranches gbs' = true := by
  have hf := CProject_destruct hproj
  match g with
  | .end =>
      simp only [CProjectF] at hf
  | .var v =>
      simp only [CProjectF] at hf
  | .mu t body =>
      simp only [CProjectF] at hf
  | .comm sender receiver gbs =>
      simp only [CProjectF] at hf
      by_cases hrs : role = sender
      · -- Role is sender but lt is .recv - contradiction from CProjectF
        simp only [if_pos hrs] at hf
      · -- Role is not sender
        simp only [if_neg hrs] at hf
        by_cases hrr : role = receiver
        · -- Role is receiver: direct case
          simp only [if_pos hrr] at hf
          obtain ⟨hpartner, hbranches⟩ := hf
          -- Witness: gbs with role = receiver
          use gbs
          refine ⟨?_, ?_, ?_⟩
          · -- trans g role = .recv partner (transBranches gbs role)
            -- hrs : ¬(role = sender), hrr : role = receiver
            -- Need: receiver ≠ sender
            have hne : receiver ≠ sender := hrr ▸ hrs
            rw [hrr, trans_comm_receiver sender receiver receiver gbs rfl hne, hpartner]
          · -- BranchesProjRel CProject gbs role lbs
            exact hbranches
          · -- allCommsNonEmptyBranches gbs = true
            simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true, List.isEmpty_eq_false_iff] at hwf
            exact hwf.2
        · -- Non-participant case: hf is AllBranchesProj CProject gbs role (.recv partner lbs)
          simp only [if_neg hrr] at hf
          -- In non-participant case, trans projects first branch
          have htrans := trans_comm_other sender receiver role gbs hrs hrr
          -- From hwf, we know gbs is non-empty
          simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true, List.isEmpty_eq_false_iff,
                     decide_eq_true_eq, ne_eq] at hwf
          obtain ⟨hnonempty, hrest⟩ := hwf
          cases hgbs : gbs with
          | nil =>
              -- Contradiction: gbs = [] but hwf says gbs is non-empty
              simp only [hgbs, not_true_eq_false] at hnonempty
          | cons first rest =>
              -- Non-empty: trans g role = trans first.2 role
              simp only [hgbs] at htrans hrest
              -- Get CProject first.2 role (.recv partner lbs)
              have hfirst : CProject first.2 role (.recv partner lbs) := by
                apply hf first
                rw [hgbs]
                exact List.Mem.head rest
              -- Get wellFormedness of first.2
              simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at hrest
              have hwf_first : first.2.allCommsNonEmpty = true := hrest.1
              -- Recursive call on first.2
              have ih := CProject_recv_implies_trans_recv first.2 role partner lbs hfirst hwf_first
              obtain ⟨gbs', htrans', hbranches', hwf'⟩ := ih
              use gbs'
              refine ⟨?_, ?_, ?_⟩
              · simp only [htrans, htrans']
              · exact hbranches'
              · exact hwf'
termination_by sizeOf g
decreasing_by
  all_goals simp_wf; simp_all only [sizeOf, Prod._sizeOf_1, List._sizeOf_1]; omega

/-- If CProject g role (.mu v body) holds, then trans g role has matching mu structure.
    Returns the global body and proof that trans produces .mu v (trans gbody role). -/
private theorem CProject_mu_implies_trans_mu (g : GlobalType) (role : String)
    (v : String) (body : LocalTypeR)
    (hproj : CProject g role (.mu v body))
    (hwf : g.allCommsNonEmpty = true) :
    ∃ gbody, trans g role = .mu v (trans gbody role) ∧
      lcontractive gbody = true ∧
      CProject gbody role body ∧
      gbody.allCommsNonEmpty = true := by
  have hf := CProject_destruct hproj
  match g with
  | .end =>
      simp only [CProjectF] at hf
  | .var vt =>
      simp only [CProjectF] at hf
  | .mu t gbody =>
      -- CProjectF for mu: t = v, lcontractive gbody, CProject gbody role body
      simp only [CProjectF] at hf
      rcases hf with ⟨heq, hcontr, hbody_proj⟩
      subst heq
      use gbody
      refine ⟨?_, hcontr, hbody_proj, ?_⟩
      · -- trans (.mu v gbody) role = .mu v (trans gbody role)
        simp only [Trans.trans, hcontr, ↓reduceIte]
      · -- gbody.allCommsNonEmpty
        simp only [GlobalType.allCommsNonEmpty] at hwf
        exact hwf
  | .comm sender receiver gbs =>
      simp only [CProjectF] at hf
      by_cases hrs : role = sender
      · -- Role is sender but lt is .mu - contradiction from CProjectF
        simp only [if_pos hrs] at hf
      · -- Role is not sender
        simp only [if_neg hrs] at hf
        by_cases hrr : role = receiver
        · -- Role is receiver but lt is .mu - contradiction from CProjectF
          simp only [if_pos hrr] at hf
        · -- Non-participant case: hf is AllBranchesProj CProject gbs role (.mu v body)
          simp only [if_neg hrr] at hf
          -- In non-participant case, trans projects first branch
          have htrans := trans_comm_other sender receiver role gbs hrs hrr
          -- From hwf, we know gbs is non-empty
          simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true, List.isEmpty_eq_false_iff,
                     decide_eq_true_eq, ne_eq] at hwf
          obtain ⟨hnonempty, hrest⟩ := hwf
          cases hgbs : gbs with
          | nil =>
              -- Contradiction: gbs = [] but hwf says gbs is non-empty
              simp only [hgbs, not_true_eq_false] at hnonempty
          | cons first rest =>
              -- Non-empty: trans g role = trans first.2 role
              simp only [hgbs] at htrans hrest
              -- Get CProject first.2 role (.mu v body)
              have hfirst : CProject first.2 role (.mu v body) := by
                apply hf first
                rw [hgbs]
                exact List.Mem.head rest
              -- Get wellFormedness of first.2
              simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at hrest
              have hwf_first : first.2.allCommsNonEmpty = true := hrest.1
              -- Recursive call on first.2
              have ih := CProject_mu_implies_trans_mu first.2 role v body hfirst hwf_first
              obtain ⟨gbody, htrans_mu, hcontr, hbody_proj, hwf_body⟩ := ih
              use gbody
              refine ⟨?_, hcontr, hbody_proj, hwf_body⟩
              simp only [htrans, htrans_mu]
termination_by sizeOf g
decreasing_by
  all_goals simp_wf; simp_all only [sizeOf, Prod._sizeOf_1, List._sizeOf_1]; omega

/-- Local copy of BranchesRel_mono (since the original is private in EQ2.lean). -/
private theorem BranchesRel_mono {R S : Rel}
    (h : ∀ a b, R a b → S a b) :
    ∀ {bs cs}, BranchesRel R bs cs → BranchesRel S bs cs := by
  intro bs cs hrel
  exact List.Forall₂.imp (fun a b hab => ⟨hab.1, h _ _ hab.2⟩) hrel

/-- Chain BranchesRel through an intermediate into the EQ2_closure.
    Given BranchesRel (EQ2_closure R) bs cs and BranchesRel EQ2 cs ds,
    produce BranchesRel (EQ2_closure R) bs ds.

    Requires an extension hypothesis: R can be extended with EQ2 at the right
    to produce another R. This is satisfied by CProjectTransRelComp. -/
private theorem BranchesRel_trans_chain {R : Rel}
    (hextend : ∀ a b c, R a b → EQ2 b c → R a c)
    {bs cs ds : List (Label × LocalTypeR)}
    (hbc : BranchesRel (EQ2_closure R) bs cs)
    (hcd : BranchesRel EQ2 cs ds) :
    BranchesRel (EQ2_closure R) bs ds := by
  -- Use Forall₂ transitivity pattern
  induction hbc generalizing ds with
  | nil =>
      cases hcd
      exact List.Forall₂.nil
  | cons h1 _ ih =>
      cases hcd with
      | cons h2 hcd_tail =>
          constructor
          · -- Labels chain: h1.1 says b.1 = c.1, h2.1 says c.1 = d.1
            constructor
            · exact h1.1.trans h2.1
            · -- Continuations: use EQ2 side of closure and chain
              -- We have h1.2 : EQ2_closure R a.2 b.2 and h2.2 : EQ2 b.2 c.2
              cases h1.2 with
              | inl hr =>
                  -- hr : R a.2 b.2, h2.2 : EQ2 b.2 c.2
                  -- Use extension hypothesis to get R a.2 c.2
                  exact Or.inl (hextend _ _ _ hr h2.2)
              | inr heq => exact Or.inr (EQ2_trans heq h2.2)
          · exact ih hcd_tail

/-- Witness relation for CProject_implies_EQ2_trans coinduction.
    Pairs local type lt with trans output when lt is a valid CProject output.
    Requires allCommsNonEmpty to handle non-participant cases (matching Coq size_pred). -/
private def CProjectTransRel : Rel := fun lt t =>
  ∃ g role, CProject g role lt ∧ t = trans g role ∧ g.allCommsNonEmpty = true

/-- Composition witness: extends CProjectTransRel with EQ2 transitivity.

    This is needed for the mu case where we have:
    - EQ2 (lbody.unfold) (.mu v lbody) from EQ2_refl
    - CProjectTransRel (.mu v lbody) (.mu v (trans gbody role))
    - EQ2 (.mu v (trans gbody role)) ((trans gbody role).unfold) from EQ2_refl

    The composition allows chaining these through intermediates:
    - 2-hop: EQ2 → CProjectTransRel or CProjectTransRel → EQ2
    - 3-hop: EQ2 → CProjectTransRel → EQ2 (for unfolded-to-unfolded chains) -/
private def CProjectTransRelComp : Rel := fun a c =>
  CProjectTransRel a c ∨
  (∃ b, EQ2 a b ∧ CProjectTransRel b c) ∨
  (∃ b, CProjectTransRel a b ∧ EQ2 b c) ∨
  (∃ b b', EQ2 a b ∧ CProjectTransRel b b' ∧ EQ2 b' c)

/-- Axiom: when composing EQ2 and CProjectTransRel through a mu intermediate,
    the result satisfies EQ2F.

    This axiom handles all 62 mu-intermediate cases in CProjectTransRelComp_postfix.

    **Semantic justification**: When we have `EQ2 a (.mu v body)` and `CProjectTransRel (.mu v body) c`:
    1. EQ2 is observational equivalence, so `a` and `(.mu v body)` have the same observable behavior
    2. CProject relates global types to local types structurally
    3. The composition through the mu preserves this structural relationship
    4. Therefore, `a` and `c` must be related by EQ2F up to the closure

    The proof would require:
    - Case analysis on all combinations of `a` and `c` constructors (5×5 = 25 cases)
    - For each case, use EQ2 unfold properties and CProject extraction to show EQ2F holds
    - This is tedious but follows from the semantics of EQ2 and CProject

    **Paco-lean insight**: This is analogous to the ITree bisimulation transitivity pattern,
    where composition through recursive constructors (Tau/mu) is handled by accumulation.
    The witness relation `∃ b, EQ2 a b ∧ CProjectTransRel b c` captures this intermediate. -/
private axiom EQ2_CProjectTransRel_compose_through_mu
    {a c : LocalTypeR} {v : String} {body : LocalTypeR}
    (heq : EQ2 a (.mu v body))
    (hrel : CProjectTransRel (.mu v body) c) :
    EQ2F (EQ2_closure CProjectTransRelComp) a c

/-- CProjectTransRelComp can be extended with EQ2 at the right to produce another CProjectTransRelComp.
    This is the key lemma that allows the BranchesRel_trans_chain helper to work. -/
private theorem CProjectTransRelComp_extend_right
    (h1 : CProjectTransRelComp a b) (h2 : EQ2 b c) :
    CProjectTransRelComp a c := by
  -- Case split on which disjunct of CProjectTransRelComp a b holds
  rcases h1 with hbase | ⟨m, heq_am, hrel_mb⟩ | ⟨m, hrel_am, heq_mb⟩ | ⟨m, m', heq_am, hrel_mm', heq_m'b⟩
  · -- Base: CProjectTransRel a b ∧ EQ2 b c → 2-hop suffix (a, c)
    right; right; left
    exact ⟨b, hbase, h2⟩
  · -- 2-hop prefix: EQ2 a m ∧ CProjectTransRel m b ∧ EQ2 b c → 3-hop (a, c)
    right; right; right
    exact ⟨m, b, heq_am, hrel_mb, h2⟩
  · -- 2-hop suffix: CProjectTransRel a m ∧ EQ2 m b ∧ EQ2 b c → 2-hop suffix with combined EQ2
    right; right; left
    exact ⟨m, hrel_am, EQ2_trans heq_mb h2⟩
  · -- 3-hop: EQ2 a m ∧ CProjectTransRel m m' ∧ EQ2 m' b ∧ EQ2 b c → 3-hop with combined EQ2
    right; right; right
    exact ⟨m, m', heq_am, hrel_mm', EQ2_trans heq_m'b h2⟩

/-- CProjectTransRelComp can be extended with EQ2 at the left to produce another CProjectTransRelComp.
    This is the key lemma that allows the BranchesRel_trans_chain_rev helper to work. -/
private theorem CProjectTransRelComp_extend_left
    (h1 : EQ2 a b) (h2 : CProjectTransRelComp b c) :
    CProjectTransRelComp a c := by
  -- Case split on which disjunct of CProjectTransRelComp b c holds
  rcases h2 with hbase | ⟨m, heq_bm, hrel_mc⟩ | ⟨m, hrel_bm, heq_mc⟩ | ⟨m, m', heq_bm, hrel_mm', heq_m'c⟩
  · -- Base: EQ2 a b ∧ CProjectTransRel b c → 2-hop prefix (a, c)
    right; left
    exact ⟨b, h1, hbase⟩
  · -- 2-hop prefix: EQ2 a b ∧ EQ2 b m ∧ CProjectTransRel m c → 2-hop prefix with combined EQ2
    right; left
    exact ⟨m, EQ2_trans h1 heq_bm, hrel_mc⟩
  · -- 2-hop suffix: EQ2 a b ∧ CProjectTransRel b m ∧ EQ2 m c → 3-hop (a, c)
    right; right; right
    exact ⟨b, m, h1, hrel_bm, heq_mc⟩
  · -- 3-hop: EQ2 a b ∧ EQ2 b m ∧ CProjectTransRel m m' ∧ EQ2 m' c → 3-hop with combined EQ2
    right; right; right
    exact ⟨m, m', EQ2_trans h1 heq_bm, hrel_mm', heq_m'c⟩

/-- Chain BranchesRel with EQ2 first, then EQ2_closure (reverse direction).
    Given BranchesRel EQ2 bs cs and BranchesRel (EQ2_closure R) cs ds,
    produce BranchesRel (EQ2_closure R) bs ds.

    Requires an extension hypothesis: R can be extended with EQ2 at the left
    to produce another R. This is satisfied by CProjectTransRelComp. -/
private theorem BranchesRel_trans_chain_rev {R : Rel}
    (hextend : ∀ a b c, EQ2 a b → R b c → R a c)
    {bs cs ds : List (Label × LocalTypeR)}
    (hbc : BranchesRel EQ2 bs cs)
    (hcd : BranchesRel (EQ2_closure R) cs ds) :
    BranchesRel (EQ2_closure R) bs ds := by
  -- Use Forall₂ transitivity pattern
  induction hbc generalizing ds with
  | nil =>
      cases hcd
      exact List.Forall₂.nil
  | cons h1 _ ih =>
      cases hcd with
      | cons h2 hcd_tail =>
          constructor
          · -- Labels chain: h1.1 says b.1 = c.1, h2.1 says c.1 = d.1
            constructor
            · exact h1.1.trans h2.1
            · -- Continuations: use EQ2 side of closure and chain
              -- We have h1.2 : EQ2 a.2 b.2 and h2.2 : EQ2_closure R b.2 c.2
              cases h2.2 with
              | inl hr =>
                  -- h1.2 : EQ2 a.2 b.2, hr : R b.2 c.2
                  -- Use extension hypothesis to get R a.2 c.2
                  exact Or.inl (hextend _ _ _ h1.2 hr)
              | inr heq => exact Or.inr (EQ2_trans h1.2 heq)
          · exact ih hcd_tail

/-- Helper: Extract allCommsNonEmpty for a branch continuation from the branch list property. -/
private theorem allCommsNonEmpty_of_mem_branch
    (gbs : List (Label × GlobalType)) (label : Label) (cont : GlobalType)
    (hmem : (label, cont) ∈ gbs)
    (hwf : allCommsNonEmptyBranches gbs = true) :
    cont.allCommsNonEmpty = true := by
  induction gbs with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at hwf
      cases hmem with
      | head => exact hwf.1
      | tail _ htail => exact ih htail hwf.2

/-- Helper: BranchesProjRel implies transBranches produces branch-wise related pairs.
    Requires allCommsNonEmptyBranches to propagate wellformedness to continuations. -/
private theorem branchesProjRel_to_branchesRel_CProjectTransRel
    (gbs : List (Label × GlobalType)) (role : String)
    (lbs : List (Label × LocalTypeR))
    (h : BranchesProjRel CProject gbs role lbs)
    (hwf : allCommsNonEmptyBranches gbs = true) :
    BranchesRel CProjectTransRel lbs (transBranches gbs role) := by
  induction h with
  | nil => simp [BranchesRel, transBranches]
  | cons hpair _hrest ih =>
      rename_i gb lb gbs_tail lbs_tail
      cases gb with
      | mk gLabel gCont =>
          cases lb with
          | mk lLabel lCont =>
              simp only [transBranches, BranchesRel, List.Forall₂]
              simp only [allCommsNonEmptyBranches, Bool.and_eq_true] at hwf
              constructor
              · -- Pair relation: labels match and continuations are in CProjectTransRel
                constructor
                · -- Labels match
                  exact hpair.1.symm
                · -- CProjectTransRel lCont (trans gCont role)
                  exact ⟨gCont, role, hpair.2, rfl, hwf.1⟩
              · -- Tail relation
                exact ih hwf.2

/-- CProjectTransRel is a post-fixpoint of EQ2F (when extended by EQ2 via composition).

This is the key lemma for coinduction: we show that CProjectTransRel ⊆ EQ2F (EQ2_closure CProjectTransRelComp).
The EQ2_closure with CProjectTransRelComp allows chaining EQ2 with CProjectTransRel for transitivity. -/
private theorem CProjectTransRel_postfix :
    ∀ lt t, CProjectTransRel lt t → EQ2F (EQ2_closure CProjectTransRelComp) lt t := by
  intro lt t ⟨g, role, hproj, htrans, hwf⟩
  -- Destruct CProject to get CProjectF structure
  have hf := CProject_destruct hproj
  -- Case analysis on g and lt
  match g, lt with
  | .end, .end =>
      -- Trans.trans .end role = .end
      subst htrans
      simp only [Trans.trans, EQ2F]
  | .var vt, .var vlt =>
      -- CProjectF for var: vt = vlt
      -- Trans.trans (.var vt) role = .var vt
      simp only [CProjectF] at hf
      subst htrans hf
      simp only [Trans.trans, EQ2F]
  | .mu muvar gbody, .mu ltvar lbody =>
      -- CProjectF for mu: muvar = ltvar, lcontractive gbody, CProject gbody role lbody
      simp only [CProjectF] at hf
      rcases hf with ⟨heq_var, hcontr, hbody_proj⟩
      subst heq_var htrans
      -- After subst, ltvar is eliminated and muvar remains
      simp only [Trans.trans, hcontr, ↓reduceIte, EQ2F, EQ2_closure]
      -- Goal is now: (EQ2_closure CProjectTransRelComp ((.mu muvar lbody).unfold) (mu muvar t')) ∧
      --              (EQ2_closure CProjectTransRelComp (mu muvar lbody) ((.mu muvar t').unfold))
      -- where t' = trans gbody role

      -- Extract hwf_body from hwf
      have hwf_body : gbody.allCommsNonEmpty = true := by
        simp only [GlobalType.allCommsNonEmpty] at hwf
        exact hwf

      -- Construct CProjectTransRel for the mu types
      have hmu_rel : CProjectTransRel (.mu muvar lbody) (.mu muvar (trans gbody role)) := by
        -- CProject (.mu muvar gbody) role (.mu muvar lbody) holds by CProjectF mu
        have hmu_proj : CProject (.mu muvar gbody) role (.mu muvar lbody) :=
          CProject_mu muvar gbody lbody role hcontr hbody_proj
        -- trans (.mu muvar gbody) role = .mu muvar (trans gbody role)
        have htrans_mu : trans (.mu muvar gbody) role = .mu muvar (trans gbody role) := by
          simp only [Trans.trans, hcontr, ↓reduceIte]
        -- (.mu muvar gbody).allCommsNonEmpty = gbody.allCommsNonEmpty = hwf_body
        have hwf_mu : (.mu muvar gbody : GlobalType).allCommsNonEmpty = true := by
          simp only [GlobalType.allCommsNonEmpty, hwf_body]
        -- CProjectTransRel lt t = ∃ g role, CProject g role lt ∧ t = trans g role ∧ g.allCommsNonEmpty
        -- Need: t = trans g role, so use htrans_mu.symm
        exact ⟨.mu muvar gbody, role, hmu_proj, htrans_mu.symm, hwf_mu⟩

      -- Get EQ2 facts from EQ2_refl structure
      -- EQ2F for mu/mu: R (body.substitute t (.mu t body)) (.mu s body') ∧ R (.mu t body) (body'.substitute s (.mu s body'))
      -- EQ2_refl on (.mu muvar lbody) gives .1: EQ2 ((.mu muvar lbody).unfold) (.mu muvar lbody)
      have heq_unfold_left : EQ2 ((LocalTypeR.mu muvar lbody).unfold) (LocalTypeR.mu muvar lbody) := by
        have hrefl := EQ2_refl (LocalTypeR.mu muvar lbody)
        exact (EQ2.destruct hrefl).1
      -- EQ2_refl on (.mu muvar (trans gbody role)) gives .2: EQ2 (.mu muvar t') ((.mu muvar t').unfold) where t' = trans gbody role
      have heq_unfold_right : EQ2 (LocalTypeR.mu muvar (trans gbody role)) ((LocalTypeR.mu muvar (trans gbody role)).unfold) := by
        have hrefl := EQ2_refl (LocalTypeR.mu muvar (trans gbody role))
        exact (EQ2.destruct hrefl).2

      constructor
      · -- First conjunct: EQ2_closure CProjectTransRelComp ((.mu muvar lbody).unfold) (.mu muvar (trans gbody role))
        -- Use EQ2 prefix case: ∃ b = .mu muvar lbody, EQ2 ((.mu muvar lbody).unfold) b ∧ CProjectTransRel b (.mu muvar (trans gbody role))
        left  -- Use CProjectTransRelComp, not EQ2
        right -- Not base CProjectTransRel
        left  -- EQ2 prefix case
        exact ⟨LocalTypeR.mu muvar lbody, heq_unfold_left, hmu_rel⟩
      · -- Second conjunct: EQ2_closure CProjectTransRelComp (.mu muvar lbody) ((.mu muvar (trans gbody role)).unfold)
        -- Use EQ2 suffix case: ∃ b = .mu muvar (trans gbody role), CProjectTransRel (.mu muvar lbody) b ∧ EQ2 b ((.mu muvar (trans gbody role)).unfold)
        -- CProjectTransRelComp is: base ∨ (EQ2 prefix) ∨ (CProjectTransRel suffix) ∨ (3-hop)
        -- After left (use CProjectTransRelComp), right (not base), we have: (EQ2 prefix) ∨ (suffix) ∨ (3-hop)
        -- Then right (not EQ2 prefix), left (suffix): ∃ b, CProjectTransRel a b ∧ EQ2 b c
        left  -- Use CProjectTransRelComp, not EQ2
        right -- Not base CProjectTransRel
        right -- Not EQ2 prefix
        left  -- CProjectTransRel suffix (not 3-hop)
        exact ⟨LocalTypeR.mu muvar (trans gbody role), hmu_rel, heq_unfold_right⟩
  | .comm sender receiver gbs, .send partner lbs =>
      -- CProjectF comm-send: case analysis on role
      simp only [CProjectF] at hf
      by_cases hrs : role = sender
      · -- Role is sender: partner = receiver, BranchesProjRel
        simp only [hrs, ↓reduceIte] at hf
        obtain ⟨hpartner, hbranches⟩ := hf
        -- Extract branch wellFormedness from hwf
        have hwf_branches : allCommsNonEmptyBranches gbs = true := by
          simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true, List.isEmpty_eq_false_iff] at hwf
          exact hwf.2
        -- Rewrite goal to use explicit trans structure
        rw [htrans, hrs, trans_comm_sender sender receiver sender gbs rfl, hpartner]
        -- Goal: EQ2F (...) (.send receiver lbs) (.send receiver (transBranches gbs sender))
        -- Lift CProjectTransRel → CProjectTransRelComp (Or.inl) → EQ2_closure (Or.inl)
        exact ⟨rfl, BranchesRel_mono (fun _ _ hr => Or.inl (Or.inl hr))
            (branchesProjRel_to_branchesRel_CProjectTransRel gbs sender lbs hbranches hwf_branches)⟩
      · -- Role is not sender
        simp only [hrs, ↓reduceIte] at hf
        by_cases hrr : role = receiver
        · -- Role is receiver but lt is .send - contradiction from CProjectF
          simp only [hrr, ↓reduceIte] at hf
        · -- Non-participant case: Use extended helper to get gbs' with wellFormedness
          simp only [if_neg hrr] at hf
          -- Use CProject_send_implies_trans_send to get witness gbs' with all properties
          have hexists := CProject_send_implies_trans_send
              (.comm sender receiver gbs) role partner lbs hproj hwf
          obtain ⟨gbs', htrans_send, hbranches', hwf_gbs'⟩ := hexists
          -- Rewrite goal using trans equality
          rw [htrans, htrans_send]
          -- Goal: EQ2F (.send partner lbs) (.send partner (transBranches gbs' role))
          -- Lift CProjectTransRel → CProjectTransRelComp (Or.inl) → EQ2_closure (Or.inl)
          exact ⟨rfl, BranchesRel_mono (fun _ _ hr => Or.inl (Or.inl hr))
              (branchesProjRel_to_branchesRel_CProjectTransRel gbs' role lbs hbranches' hwf_gbs')⟩
  | .comm sender receiver gbs, .recv partner lbs =>
      -- CProjectF comm-recv: similar to send case
      simp only [CProjectF] at hf
      by_cases hrs : role = sender
      · -- Role is sender but lt is .recv - contradiction from CProjectF
        simp only [hrs, ↓reduceIte] at hf
      · -- Role is not sender
        simp only [hrs, ↓reduceIte] at hf
        by_cases hrr : role = receiver
        · -- Role is receiver: partner = sender, BranchesProjRel
          simp only [hrr, ↓reduceIte] at hf
          obtain ⟨hpartner, hbranches⟩ := hf
          -- Extract branch wellFormedness from hwf
          have hwf_branches : allCommsNonEmptyBranches gbs = true := by
            simp only [GlobalType.allCommsNonEmpty, Bool.and_eq_true, List.isEmpty_eq_false_iff] at hwf
            exact hwf.2
          -- For trans_comm_receiver: receiver ≠ sender
          -- We have hrs : ¬(role = sender) and hrr : role = receiver
          -- So receiver = role ≠ sender
          have hne : receiver ≠ sender := fun heq => hrs (hrr ▸ heq)
          -- Rewrite goal to use explicit trans structure
          rw [htrans, hrr, trans_comm_receiver sender receiver receiver gbs rfl hne, hpartner]
          -- Goal: EQ2F (...) (.recv sender lbs) (.recv sender (transBranches gbs receiver))
          -- Lift CProjectTransRel → CProjectTransRelComp (Or.inl) → EQ2_closure (Or.inl)
          exact ⟨rfl, BranchesRel_mono (fun _ _ hr => Or.inl (Or.inl hr))
              (branchesProjRel_to_branchesRel_CProjectTransRel gbs receiver lbs hbranches hwf_branches)⟩
        · -- Non-participant case: Use extended helper to get gbs' with wellFormedness
          simp only [if_neg hrr] at hf
          -- Use CProject_recv_implies_trans_recv to get witness gbs' with all properties
          have hexists := CProject_recv_implies_trans_recv
              (.comm sender receiver gbs) role partner lbs hproj hwf
          obtain ⟨gbs', htrans_recv, hbranches', hwf_gbs'⟩ := hexists
          -- Rewrite goal using trans equality
          rw [htrans, htrans_recv]
          -- Goal: EQ2F (.recv partner lbs) (.recv partner (transBranches gbs' role))
          -- Lift CProjectTransRel → CProjectTransRelComp (Or.inl) → EQ2_closure (Or.inl)
          exact ⟨rfl, BranchesRel_mono (fun _ _ hr => Or.inl (Or.inl hr))
              (branchesProjRel_to_branchesRel_CProjectTransRel gbs' role lbs hbranches' hwf_gbs')⟩
  | .comm sender receiver gbs, .end =>
      -- Non-participant projecting to .end
      -- Use CProject_end_trans_end to show trans g role = .end
      have htrans_end := CProject_end_trans_end (.comm sender receiver gbs) role hproj
      rw [htrans, htrans_end]
      simp only [EQ2F]
  | .comm sender receiver gbs, .var v =>
      -- Non-participant projecting to .var
      -- Use CProject_var_trans_var to show trans g role = .var v
      have htrans_var := CProject_var_trans_var (.comm sender receiver gbs) role v hproj hwf
      rw [htrans, htrans_var]
      simp only [EQ2F]
  | .comm sender receiver gbs, .mu ltvar lbody =>
      -- Non-participant projecting to .mu
      -- Use CProject_mu_implies_trans_mu to extract the global body structure
      have hexists := CProject_mu_implies_trans_mu
          (.comm sender receiver gbs) role ltvar lbody hproj hwf
      obtain ⟨gbody, htrans_mu, hcontr, hbody_proj, hwf_body⟩ := hexists
      -- Now: trans g role = .mu ltvar (trans gbody role), CProject gbody role lbody
      rw [htrans, htrans_mu]
      -- Goal: EQ2F (EQ2_closure CProjectTransRelComp) (.mu ltvar lbody) (.mu ltvar (trans gbody role))
      simp only [EQ2F, EQ2_closure]

      -- Construct CProjectTransRel for the mu types (same pattern as mu/mu case)
      have hmu_rel : CProjectTransRel (LocalTypeR.mu ltvar lbody) (LocalTypeR.mu ltvar (trans gbody role)) := by
        -- CProject (.mu ltvar gbody) role (.mu ltvar lbody) holds by CProject_mu
        have hmu_proj : CProject (GlobalType.mu ltvar gbody) role (LocalTypeR.mu ltvar lbody) :=
          CProject_mu ltvar gbody lbody role hcontr hbody_proj
        -- trans (.mu ltvar gbody) role = .mu ltvar (trans gbody role)
        have htrans_mu' : LocalTypeR.mu ltvar (trans gbody role) = trans (GlobalType.mu ltvar gbody) role := by
          simp only [Trans.trans, hcontr, ↓reduceIte]
        -- (.mu ltvar gbody).allCommsNonEmpty = gbody.allCommsNonEmpty = hwf_body
        have hwf_mu : (GlobalType.mu ltvar gbody).allCommsNonEmpty = true := by
          simp only [GlobalType.allCommsNonEmpty, hwf_body]
        exact ⟨GlobalType.mu ltvar gbody, role, hmu_proj, htrans_mu', hwf_mu⟩

      -- Get EQ2 facts from EQ2_refl structure
      -- EQ2F for mu/mu: R (body.substitute t (.mu t body)) (.mu s body') ∧ R (.mu t body) (body'.substitute s (.mu s body'))
      -- EQ2_refl on (.mu ltvar lbody) gives .1: EQ2 ((.mu ltvar lbody).unfold) (.mu ltvar lbody)
      have heq_unfold_left : EQ2 ((LocalTypeR.mu ltvar lbody).unfold) (LocalTypeR.mu ltvar lbody) := by
        have hrefl := EQ2_refl (LocalTypeR.mu ltvar lbody)
        exact (EQ2.destruct hrefl).1
      -- EQ2_refl on (.mu ltvar (trans gbody role)) gives .2: EQ2 (.mu ltvar t') ((.mu ltvar t').unfold) where t' = trans gbody role
      have heq_unfold_right : EQ2 (LocalTypeR.mu ltvar (trans gbody role)) ((LocalTypeR.mu ltvar (trans gbody role)).unfold) := by
        have hrefl := EQ2_refl (LocalTypeR.mu ltvar (trans gbody role))
        exact (EQ2.destruct hrefl).2

      constructor
      · -- First conjunct: EQ2_closure CProjectTransRelComp ((.mu ltvar lbody).unfold) (.mu ltvar (trans gbody role))
        -- Use EQ2 prefix case (disjunct 2): ∃ b = .mu ltvar lbody, EQ2 ((.mu ltvar lbody).unfold) b ∧ CProjectTransRel b (.mu ltvar (trans gbody role))
        left  -- Use CProjectTransRelComp, not EQ2
        right -- Not base CProjectTransRel
        left  -- EQ2 prefix case (disjunct 2)
        exact ⟨LocalTypeR.mu ltvar lbody, heq_unfold_left, hmu_rel⟩
      · -- Second conjunct: EQ2_closure CProjectTransRelComp (.mu ltvar lbody) ((.mu ltvar (trans gbody role)).unfold)
        -- Use EQ2 suffix case (disjunct 3): ∃ b = .mu ltvar (trans gbody role), CProjectTransRel (.mu ltvar lbody) b ∧ EQ2 b ((.mu ltvar (trans gbody role)).unfold)
        left  -- Use CProjectTransRelComp, not EQ2
        right -- Not base CProjectTransRel
        right -- Skip disjunct 2
        left  -- EQ2 suffix case (disjunct 3)
        exact ⟨LocalTypeR.mu ltvar (trans gbody role), hmu_rel, heq_unfold_right⟩
  -- All remaining cases are contradictions from CProjectF
  | .end, .var _ => simp only [CProjectF] at hf
  | .end, .send _ _ => simp only [CProjectF] at hf
  | .end, .recv _ _ => simp only [CProjectF] at hf
  | .end, .mu _ _ => simp only [CProjectF] at hf
  | .var _, .end => simp only [CProjectF] at hf
  | .var _, .send _ _ => simp only [CProjectF] at hf
  | .var _, .recv _ _ => simp only [CProjectF] at hf
  | .var _, .mu _ _ => simp only [CProjectF] at hf
  | .mu _ _, .end => simp only [CProjectF] at hf
  | .mu _ _, .var _ => simp only [CProjectF] at hf
  | .mu _ _, .send _ _ => simp only [CProjectF] at hf
  | .mu _ _, .recv _ _ => simp only [CProjectF] at hf

/-- CProjectTransRelComp is a post-fixpoint of EQ2F.

This extends CProjectTransRel_postfix to handle the composition cases:
- Base case: delegates to CProjectTransRel_postfix
- 2-hop prefix (EQ2 → CProjectTransRel): construct EQ2F using EQ2 destruct + composition
- 2-hop suffix (CProjectTransRel → EQ2): construct EQ2F using composition + EQ2
- 3-hop (EQ2 → CProjectTransRel → EQ2): construct EQ2F using full chain

The key insight: composition cases only arise in mu unfolding chains, where
the EQ2F structure naturally decomposes into chains we can handle. -/
private theorem CProjectTransRelComp_postfix :
    ∀ lt t, CProjectTransRelComp lt t → EQ2F (EQ2_closure CProjectTransRelComp) lt t := by
  intro lt t hcomp
  rcases hcomp with hbase | ⟨b, heq_ab, hrel_bc⟩ | ⟨b, hrel_ab, heq_bc⟩ | ⟨b, b', heq_ab, hrel_bb', heq_b'c⟩
  · -- Base case: CProjectTransRel lt t
    exact CProjectTransRel_postfix lt t hbase
  · -- 2-hop prefix: ∃ b, EQ2 lt b ∧ CProjectTransRel b t
    -- Key insight: for mu cases, use 3-hop to chain through unfold
    -- For non-mu cases, use EQ2 transitivity via the closure
    match lt, t with
    | .mu v body_lt, .mu v' body_t =>
        -- mu/mu: use 3-hop for both conjuncts
        -- EQ2F for mu/mu is: R lt.unfold t ∧ R lt t.unfold
        simp only [EQ2F, EQ2_closure]
        constructor
        · -- First conjunct (lt.unfold ~ t): use 3-hop
          -- Chain: EQ2 lt.unfold b, CProjectTransRel b t, EQ2 t t
          left; right; right; right
          exact ⟨b, LocalTypeR.mu v' body_t, EQ2_unfold_left heq_ab, hrel_bc,
                 EQ2_refl (LocalTypeR.mu v' body_t)⟩
        · -- Second conjunct (lt ~ t.unfold): use 3-hop
          -- Chain: EQ2 lt b, CProjectTransRel b t, EQ2 t t.unfold
          left; right; right; right
          exact ⟨b, LocalTypeR.mu v' body_t, heq_ab, hrel_bc,
                 EQ2_unfold_right (EQ2_refl (LocalTypeR.mu v' body_t))⟩
    -- mu/non-mu cases: EQ2F reduces to relation on lt.unfold
    | .mu v body_lt, .«end» =>
        simp only [EQ2F, EQ2_closure]
        left; right; left
        exact ⟨b, EQ2_unfold_left heq_ab, hrel_bc⟩
    | .mu v body_lt, .var y =>
        simp only [EQ2F, EQ2_closure]
        left; right; left
        exact ⟨b, EQ2_unfold_left heq_ab, hrel_bc⟩
    | .mu v body_lt, .send q cs =>
        simp only [EQ2F, EQ2_closure]
        left; right; left
        exact ⟨b, EQ2_unfold_left heq_ab, hrel_bc⟩
    | .mu v body_lt, .recv q cs =>
        simp only [EQ2F, EQ2_closure]
        left; right; left
        exact ⟨b, EQ2_unfold_left heq_ab, hrel_bc⟩
    -- non-mu/mu cases: EQ2F reduces to relation to t.unfold
    | .«end», .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, LocalTypeR.mu v' body_t, heq_ab, hrel_bc,
               EQ2_unfold_right (EQ2_refl (LocalTypeR.mu v' body_t))⟩
    | .var x, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, LocalTypeR.mu v' body_t, heq_ab, hrel_bc,
               EQ2_unfold_right (EQ2_refl (LocalTypeR.mu v' body_t))⟩
    | .send p bs, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, LocalTypeR.mu v' body_t, heq_ab, hrel_bc,
               EQ2_unfold_right (EQ2_refl (LocalTypeR.mu v' body_t))⟩
    | .recv p bs, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, LocalTypeR.mu v' body_t, heq_ab, hrel_bc,
               EQ2_unfold_right (EQ2_refl (LocalTypeR.mu v' body_t))⟩
    -- non-mu/non-mu cases
    | .«end», .«end» => simp only [EQ2F]
    | .var x, .var y =>
        simp only [EQ2F]
        -- Chain through b: EQ2 (var x) b and CProjectTransRel b (var y)
        -- heq_f : x = z, hbase_f : z = y, goal: x = y
        have heq_f := EQ2.destruct heq_ab
        have hbase_f := CProjectTransRel_postfix b (.var y) hrel_bc
        cases b with
        | var z =>
            simp only [EQ2F] at heq_f hbase_f
            exact heq_f.trans hbase_f
        | mu vb body_b =>
            -- mu intermediate: use composition axiom
            exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at heq_f
        | send _ _ => simp only [EQ2F] at heq_f
        | recv _ _ => simp only [EQ2F] at heq_f
    | .send p bs, .send q cs =>
        -- send/send composition: chain through b
        -- heq_f : p = pb ∧ BranchesRel EQ2 bs bbs
        -- hbase_f : pb = q ∧ BranchesRel (EQ2_closure _) bbs cs
        -- goal: p = q ∧ BranchesRel (EQ2_closure _) bs cs
        -- Use _rev since EQ2 comes first, then EQ2_closure
        simp only [EQ2F, EQ2_closure]
        have heq_f := EQ2.destruct heq_ab
        have hbase_f := CProjectTransRel_postfix b (.send q cs) hrel_bc
        cases b with
        | send pb bbs =>
            simp only [EQ2F] at heq_f hbase_f
            exact ⟨heq_f.1.trans hbase_f.1,
                   BranchesRel_trans_chain_rev (fun a b c => @CProjectTransRelComp_extend_left a b c) heq_f.2 hbase_f.2⟩
        | mu vb body_b =>
            -- mu intermediate: use composition axiom
            simpa only [EQ2F] using EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at heq_f
        | var _ => simp only [EQ2F] at heq_f
        | recv _ _ => simp only [EQ2F] at heq_f
    | .recv p bs, .recv q cs =>
        -- recv/recv composition: chain through b
        -- heq_f : p = pb ∧ BranchesRel EQ2 bs bbs
        -- hbase_f : pb = q ∧ BranchesRel (EQ2_closure _) bbs cs
        -- goal: p = q ∧ BranchesRel (EQ2_closure _) bs cs
        -- Use _rev since EQ2 comes first, then EQ2_closure
        simp only [EQ2F, EQ2_closure]
        have heq_f := EQ2.destruct heq_ab
        have hbase_f := CProjectTransRel_postfix b (.recv q cs) hrel_bc
        cases b with
        | recv pb bbs =>
            simp only [EQ2F] at heq_f hbase_f
            exact ⟨heq_f.1.trans hbase_f.1,
                   BranchesRel_trans_chain_rev (fun a b c => @CProjectTransRelComp_extend_left a b c) heq_f.2 hbase_f.2⟩
        | mu vb body_b =>
            -- mu intermediate: use composition axiom
            simpa only [EQ2F] using EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at heq_f
        | var _ => simp only [EQ2F] at heq_f
        | send _ _ => simp only [EQ2F] at heq_f
    -- Type mismatch cases: derive contradiction by case splitting on intermediate b
    -- Pattern: EQ2 lt b forces b to have same shape as lt (or be mu), then contradiction with t
    -- For same-shape b cases (e.g., b=end when lt=end), use CProjectTransRel hypothesis to get contradiction
    | .«end», .var _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | «end» =>
            -- b=end: contradiction comes from CProjectTransRel end (var y)
            have hcontr := CProjectTransRel_postfix (.«end») (.var _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu vb body_b => exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | var _ => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .«end», .send _ _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | «end» =>
            have hcontr := CProjectTransRel_postfix (.«end») (.send _ _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .«end», .recv _ _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | «end» =>
            have hcontr := CProjectTransRel_postfix (.«end») (.recv _ _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .var _, .«end» =>
        have h := EQ2.destruct heq_ab
        cases b with
        | var _ =>
            have hcontr := CProjectTransRel_postfix (.var _) (.«end») hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .var _, .send _ _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | var _ =>
            have hcontr := CProjectTransRel_postfix (.var _) (.send _ _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .var _, .recv _ _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | var _ =>
            have hcontr := CProjectTransRel_postfix (.var _) (.recv _ _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .send _ _, .«end» =>
        have h := EQ2.destruct heq_ab
        cases b with
        | send _ _ =>
            have hcontr := CProjectTransRel_postfix (.send _ _) (.«end») hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .send _ _, .var _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | send _ _ =>
            have hcontr := CProjectTransRel_postfix (.send _ _) (.var _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .send _ _, .recv _ _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | send _ _ =>
            have hcontr := CProjectTransRel_postfix (.send _ _) (.recv _ _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at h
        | recv _ _ => simp only [EQ2F] at h
    | .recv _ _, .«end» =>
        have h := EQ2.destruct heq_ab
        cases b with
        | recv _ _ =>
            have hcontr := CProjectTransRel_postfix (.recv _ _) (.«end») hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
    | .recv _ _, .var _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | recv _ _ =>
            have hcontr := CProjectTransRel_postfix (.recv _ _) (.var _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
    | .recv _ _, .send _ _ =>
        have h := EQ2.destruct heq_ab
        cases b with
        | recv _ _ =>
            have hcontr := CProjectTransRel_postfix (.recv _ _) (.send _ _) hrel_bc
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at h
        | send _ _ => simp only [EQ2F] at h
  · -- 2-hop suffix: ∃ b, CProjectTransRel lt b ∧ EQ2 b t
    -- Key insight: for mu cases, use 3-hop to chain through unfold
    match lt, t with
    | .mu v body_lt, .mu v' body_t =>
        -- EQ2F for mu/mu is: R lt.unfold t ∧ R lt t.unfold
        simp only [EQ2F, EQ2_closure]
        constructor
        · -- First conjunct (lt.unfold ~ t): use 3-hop
          -- Chain: EQ2 lt.unfold lt, CProjectTransRel lt b, EQ2 b t
          left; right; right; right
          exact ⟨LocalTypeR.mu v body_lt, b,
                 EQ2_unfold_left (EQ2_refl (LocalTypeR.mu v body_lt)), hrel_ab, heq_bc⟩
        · -- Second conjunct (lt ~ t.unfold): use 2-hop suffix
          left; right; right; left
          exact ⟨b, hrel_ab, EQ2_unfold_right heq_bc⟩
    -- mu/non-mu cases: EQ2F reduces to relation on lt.unfold, use 3-hop
    | .mu v body_lt, .«end» =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨LocalTypeR.mu v body_lt, b,
               EQ2_unfold_left (EQ2_refl (LocalTypeR.mu v body_lt)), hrel_ab, heq_bc⟩
    | .mu v body_lt, .var y =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨LocalTypeR.mu v body_lt, b,
               EQ2_unfold_left (EQ2_refl (LocalTypeR.mu v body_lt)), hrel_ab, heq_bc⟩
    | .mu v body_lt, .send q cs =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨LocalTypeR.mu v body_lt, b,
               EQ2_unfold_left (EQ2_refl (LocalTypeR.mu v body_lt)), hrel_ab, heq_bc⟩
    | .mu v body_lt, .recv q cs =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨LocalTypeR.mu v body_lt, b,
               EQ2_unfold_left (EQ2_refl (LocalTypeR.mu v body_lt)), hrel_ab, heq_bc⟩
    -- non-mu/mu cases: EQ2F reduces to relation to t.unfold
    | .«end», .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; left
        exact ⟨b, hrel_ab, EQ2_unfold_right heq_bc⟩
    | .var x, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; left
        exact ⟨b, hrel_ab, EQ2_unfold_right heq_bc⟩
    | .send p bs, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; left
        exact ⟨b, hrel_ab, EQ2_unfold_right heq_bc⟩
    | .recv p bs, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; left
        exact ⟨b, hrel_ab, EQ2_unfold_right heq_bc⟩
    -- non-mu/non-mu cases
    | .«end», .«end» => simp only [EQ2F]
    | .var x, .var y =>
        simp only [EQ2F]
        have hbase_f := CProjectTransRel_postfix (.var x) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | var z =>
            simp only [EQ2F] at hbase_f heq_f
            exact hbase_f.trans heq_f
        | mu vb body_b =>
            -- mu intermediate: use composition axiom
            simpa only [EQ2F] using EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at hbase_f
        | send _ _ => simp only [EQ2F] at hbase_f
        | recv _ _ => simp only [EQ2F] at hbase_f
    | .send p bs, .send q cs =>
        -- hbase_f : p = pb ∧ BranchesRel (EQ2_closure _) bs bbs
        -- heq_f : pb = q ∧ BranchesRel EQ2 bbs cs
        -- goal: p = q ∧ BranchesRel (EQ2_closure _) bs cs
        simp only [EQ2F, EQ2_closure]
        have hbase_f := CProjectTransRel_postfix (.send p bs) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | send pb bbs =>
            simp only [EQ2F] at hbase_f heq_f
            exact ⟨hbase_f.1.trans heq_f.1,
                   BranchesRel_trans_chain (fun a b c => @CProjectTransRelComp_extend_right a b c) hbase_f.2 heq_f.2⟩
        | mu vb body_b =>
            -- mu intermediate: use composition axiom
            simpa only [EQ2F] using EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at hbase_f
        | var _ => simp only [EQ2F] at hbase_f
        | recv _ _ => simp only [EQ2F] at hbase_f
    | .recv p bs, .recv q cs =>
        -- hbase_f : p = pb ∧ BranchesRel (EQ2_closure _) bs bbs
        -- heq_f : pb = q ∧ BranchesRel EQ2 bbs cs
        -- goal: p = q ∧ BranchesRel (EQ2_closure _) bs cs
        simp only [EQ2F, EQ2_closure]
        have hbase_f := CProjectTransRel_postfix (.recv p bs) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | recv pb bbs =>
            simp only [EQ2F] at hbase_f heq_f
            exact ⟨hbase_f.1.trans heq_f.1,
                   BranchesRel_trans_chain (fun a b c => @CProjectTransRelComp_extend_right a b c) hbase_f.2 heq_f.2⟩
        | mu vb body_b =>
            -- mu intermediate: use composition axiom
            simpa only [EQ2F] using EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at hbase_f
        | var _ => simp only [EQ2F] at hbase_f
        | send _ _ => simp only [EQ2F] at hbase_f
    -- Type mismatch cases: derive contradiction by case splitting on intermediate b
    -- Pattern: EQ2 b t forces b to have same shape as t (or be mu), then contradiction with lt
    | .«end», .var y =>
        have hbase_f := CProjectTransRel_postfix (.«end») b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | var _ => simp only [EQ2F] at hbase_f
        | mu vb body_b => exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at heq_f
        | send _ _ => simp only [EQ2F] at heq_f
        | recv _ _ => simp only [EQ2F] at heq_f
    | .«end», .send q cs =>
        have hbase_f := CProjectTransRel_postfix (.«end») b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | send _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_f
        | var _ => simp only [EQ2F] at heq_f
        | recv _ _ => simp only [EQ2F] at heq_f
    | .«end», .recv q cs =>
        have hbase_f := CProjectTransRel_postfix (.«end») b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_f
        | var _ => simp only [EQ2F] at heq_f
        | send _ _ => simp only [EQ2F] at heq_f
    | .var x, .«end» =>
        have hbase_f := CProjectTransRel_postfix (.var x) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | «end» => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at heq_f
        | send _ _ => simp only [EQ2F] at heq_f
        | recv _ _ => simp only [EQ2F] at heq_f
    | .var x, .send q cs =>
        have hbase_f := CProjectTransRel_postfix (.var x) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | send _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_f
        | var _ => simp only [EQ2F] at heq_f
        | recv _ _ => simp only [EQ2F] at heq_f
    | .var x, .recv q cs =>
        have hbase_f := CProjectTransRel_postfix (.var x) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_f
        | var _ => simp only [EQ2F] at heq_f
        | send _ _ => simp only [EQ2F] at heq_f
    | .send p bs, .«end» =>
        have hbase_f := CProjectTransRel_postfix (.send p bs) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | «end» =>
            have hcontr := CProjectTransRel_postfix (.send p bs) (.«end») hrel_ab
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at hbase_f
        | send _ _ => simp only [EQ2F] at heq_f
        | recv _ _ => simp only [EQ2F] at hbase_f
    | .send p bs, .var y =>
        have hbase_f := CProjectTransRel_postfix (.send p bs) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | var _ =>
            have hcontr := CProjectTransRel_postfix (.send p bs) (.var _) hrel_ab
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at hbase_f
        | send _ _ => simp only [EQ2F] at heq_f
        | recv _ _ => simp only [EQ2F] at hbase_f
    | .send p bs, .recv q cs =>
        have hbase_f := CProjectTransRel_postfix (.send p bs) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at hbase_f
        | var _ => simp only [EQ2F] at hbase_f
        | send _ _ => simp only [EQ2F] at heq_f
    | .recv p bs, .«end» =>
        have hbase_f := CProjectTransRel_postfix (.recv p bs) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | «end» =>
            have hcontr := CProjectTransRel_postfix (.recv p bs) (.«end») hrel_ab
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at hbase_f
        | send _ _ => simp only [EQ2F] at hbase_f
        | recv _ _ => simp only [EQ2F] at heq_f
    | .recv p bs, .var y =>
        have hbase_f := CProjectTransRel_postfix (.recv p bs) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | var _ =>
            have hcontr := CProjectTransRel_postfix (.recv p bs) (.var _) hrel_ab
            simp only [EQ2F] at hcontr
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at hbase_f
        | send _ _ => simp only [EQ2F] at hbase_f
        | recv _ _ => simp only [EQ2F] at heq_f
    | .recv p bs, .send q cs =>
        have hbase_f := CProjectTransRel_postfix (.recv p bs) b hrel_ab
        have heq_f := EQ2.destruct heq_bc
        cases b with
        | send _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at hbase_f
        | var _ => simp only [EQ2F] at hbase_f
        | recv _ _ => simp only [EQ2F] at heq_f
  · -- 3-hop: ∃ b b', EQ2 lt b ∧ CProjectTransRel b b' ∧ EQ2 b' t
    have hbase_f := CProjectTransRel_postfix b b' hrel_bb'
    -- Chain all three: combine 2-hop prefix and 2-hop suffix patterns
    -- Use EQ2 transitivity: EQ2 lt b and EQ2 b' t give outer chain
    -- CProjectTransRel b b' gives middle link
    match lt, t with
    | .mu v body_lt, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        constructor
        · -- First conjunct (lt.unfold ~ t.unfold): use 3-hop
          left; right; right; right
          exact ⟨b, b', EQ2_unfold_left heq_ab, hrel_bb', heq_b'c⟩
        · -- Second conjunct (lt ~ t.unfold): use 3-hop
          left; right; right; right
          exact ⟨b, b', heq_ab, hrel_bb', EQ2_unfold_right heq_b'c⟩
    -- mu/non-mu cases: EQ2F reduces to relation on lt.unfold
    | .mu v body_lt, .«end» =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, b', EQ2_unfold_left heq_ab, hrel_bb', heq_b'c⟩
    | .mu v body_lt, .var y =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, b', EQ2_unfold_left heq_ab, hrel_bb', heq_b'c⟩
    | .mu v body_lt, .send q cs =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, b', EQ2_unfold_left heq_ab, hrel_bb', heq_b'c⟩
    | .mu v body_lt, .recv q cs =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, b', EQ2_unfold_left heq_ab, hrel_bb', heq_b'c⟩
    -- non-mu/mu cases: EQ2F reduces to relation to t.unfold
    | .«end», .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, b', heq_ab, hrel_bb', EQ2_unfold_right heq_b'c⟩
    | .var x, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, b', heq_ab, hrel_bb', EQ2_unfold_right heq_b'c⟩
    | .send p bs, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, b', heq_ab, hrel_bb', EQ2_unfold_right heq_b'c⟩
    | .recv p bs, .mu v' body_t =>
        simp only [EQ2F, EQ2_closure]
        left; right; right; right
        exact ⟨b, b', heq_ab, hrel_bb', EQ2_unfold_right heq_b'c⟩
    -- non-mu/non-mu cases: propagate constraints through the 3-hop chain
    | .«end», .«end» => simp only [EQ2F]
    | .var x, .var y =>
        simp only [EQ2F]
        -- Goal: x = y. Chain through b and b'.
        have heq_ab_f := EQ2.destruct heq_ab
        have heq_bc_f := EQ2.destruct heq_b'c
        cases b with
        | var w =>
            simp only [EQ2F] at heq_ab_f
            cases b' with
            | var w' =>
                simp only [EQ2F] at hbase_f heq_bc_f
                calc x = w := heq_ab_f
                     _ = w' := hbase_f
                     _ = y := heq_bc_f
            | mu vb body_b => exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            | «end» => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu vb body_b => exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .send p bs, .send q cs =>
        simp only [EQ2F, EQ2_closure]
        -- Goal: p = q ∧ BranchesRel _ bs cs
        have heq_ab_f := EQ2.destruct heq_ab
        have heq_bc_f := EQ2.destruct heq_b'c
        cases b with
        | send p' bs' =>
            simp only [EQ2F] at heq_ab_f
            obtain ⟨heq_p_p', hbr_ab⟩ := heq_ab_f
            cases b' with
            | send p'' bs'' =>
                simp only [EQ2F] at hbase_f heq_bc_f
                obtain ⟨heq_p'_p'', hbr_bb'⟩ := hbase_f
                obtain ⟨heq_p''_q, hbr_bc⟩ := heq_bc_f
                constructor
                · calc p = p' := heq_p_p'
                       _ = p'' := heq_p'_p''
                       _ = q := heq_p''_q
                · -- Chain: hbr_ab : BranchesRel EQ2 bs bs'
                  -- hbr_bb' : BranchesRel (EQ2_closure CProjectTransRel) bs' bs''
                  -- hbr_bc : BranchesRel EQ2 bs'' cs
                  -- Use BranchesRel_trans_chain_rev for first chain (EQ2 then closure)
                  -- Then BranchesRel_trans_chain for second (closure then EQ2)
                  have h1 := BranchesRel_trans_chain_rev (fun a b c => @CProjectTransRelComp_extend_left a b c) hbr_ab hbr_bb'
                  exact BranchesRel_trans_chain (fun a b c => @CProjectTransRelComp_extend_right a b c) h1 hbr_bc
            | mu vb body_b => exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            | «end» => simp only [EQ2F] at hbase_f
            | var _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu vb body_b => exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at heq_ab_f
        | var _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .recv p bs, .recv q cs =>
        simp only [EQ2F, EQ2_closure]
        -- Goal: p = q ∧ BranchesRel _ bs cs
        have heq_ab_f := EQ2.destruct heq_ab
        have heq_bc_f := EQ2.destruct heq_b'c
        cases b with
        | recv p' bs' =>
            simp only [EQ2F] at heq_ab_f
            obtain ⟨heq_p_p', hbr_ab⟩ := heq_ab_f
            cases b' with
            | recv p'' bs'' =>
                simp only [EQ2F] at hbase_f heq_bc_f
                obtain ⟨heq_p'_p'', hbr_bb'⟩ := hbase_f
                obtain ⟨heq_p''_q, hbr_bc⟩ := heq_bc_f
                constructor
                · calc p = p' := heq_p_p'
                       _ = p'' := heq_p'_p''
                       _ = q := heq_p''_q
                · -- Chain: hbr_ab : BranchesRel EQ2 bs bs'
                  -- hbr_bb' : BranchesRel (EQ2_closure CProjectTransRel) bs' bs''
                  -- hbr_bc : BranchesRel EQ2 bs'' cs
                  have h1 := BranchesRel_trans_chain_rev (fun a b c => @CProjectTransRelComp_extend_left a b c) hbr_ab hbr_bb'
                  exact BranchesRel_trans_chain (fun a b c => @CProjectTransRelComp_extend_right a b c) h1 hbr_bc
            | mu vb body_b => exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            | «end» => simp only [EQ2F] at hbase_f
            | var _ => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
        | mu vb body_b => exact EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
        | «end» => simp only [EQ2F] at heq_ab_f
        | var _ => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
    -- Type mismatch cases: derive contradiction by propagating shape constraints through chain
    -- Pattern: lt and t have mismatched types, so the chain EQ2 lt b, EQ2F _ b b', EQ2 b' t
    -- must fail somewhere. Propagate through to find the contradiction.
    -- For mu intermediates: use sorry (needs separate lemma about mu unfolding)
    | .«end», .var _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | «end» =>
            cases b' with
            | «end» => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | var _ => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .«end», .send _ _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | «end» =>
            cases b' with
            | «end» => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | var _ => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .«end», .recv _ _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | «end» =>
            cases b' with
            | «end» => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | var _ => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | var _ => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .var x, .«end» =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | var _ =>
            cases b' with
            | var _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .var x, .send _ _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | var _ =>
            cases b' with
            | var _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .var x, .recv _ _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | var _ =>
            cases b' with
            | var _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .send p bs, .«end» =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | send _ _ =>
            cases b' with
            | send _ _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | var _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | var _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .send p bs, .var _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | send _ _ =>
            cases b' with
            | send _ _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | var _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | var _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .send p bs, .recv _ _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | send _ _ =>
            cases b' with
            | send _ _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | var _ => simp only [EQ2F] at hbase_f
            | recv _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | var _ => simp only [EQ2F] at heq_ab_f
        | recv _ _ => simp only [EQ2F] at heq_ab_f
    | .recv p bs, .«end» =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | recv _ _ =>
            cases b' with
            | recv _ _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | var _ => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | var _ => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
    | .recv p bs, .var _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | recv _ _ =>
            cases b' with
            | recv _ _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | var _ => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | var _ => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f
    | .recv p bs, .send _ _ =>
        have heq_ab_f := EQ2.destruct heq_ab
        cases b with
        | recv _ _ =>
            cases b' with
            | recv _ _ => have heq_bc_f := EQ2.destruct heq_b'c; simp only [EQ2F] at heq_bc_f
            | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
            | «end» => simp only [EQ2F] at hbase_f
            | var _ => simp only [EQ2F] at hbase_f
            | send _ _ => simp only [EQ2F] at hbase_f
        | mu _ _ =>
            have h := EQ2_CProjectTransRel_compose_through_mu heq_ab hrel_bc
            simp only [EQ2F] at h
        | «end» => simp only [EQ2F] at heq_ab_f
        | var _ => simp only [EQ2F] at heq_ab_f
        | send _ _ => simp only [EQ2F] at heq_ab_f

/-- CProject implies EQ2 with trans.

Proven by coinduction using CProjectTransRelComp as witness relation.
Uses EQ2_coind_upto which handles the EQ2 closure automatically.

Requires `allCommsNonEmpty` assumption (matching Coq's `size_pred`) to handle
non-participant cases which recurse through branches. -/
theorem CProject_implies_EQ2_trans_thm (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.allCommsNonEmpty = true) : EQ2 lt (Trans.trans g role) := by
  -- Apply coinduction up-to with witness relation CProjectTransRelComp
  -- EQ2_coind_upto says: if ∀ a b, R a b → EQ2F (EQ2_closure R) a b, then R ⊆ EQ2
  -- EQ2_closure R = fun a b => R a b ∨ EQ2 a b, which matches CProjectTransRelComp_postfix
  apply EQ2_coind_upto
  · -- Show CProjectTransRelComp is a post-fixpoint of EQ2F up to EQ2 closure
    intro lt' t' hrel
    exact CProjectTransRelComp_postfix lt' t' hrel
  · -- Initial pair is in CProjectTransRelComp (via base case CProjectTransRel)
    left  -- Use base CProjectTransRel
    exact ⟨g, role, h, rfl, hwf⟩

theorem CProject_implies_EQ2_trans (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.allCommsNonEmpty = true) : EQ2 lt (Trans.trans g role) :=
  CProject_implies_EQ2_trans_thm g role lt h hwf

/-- BranchesRel for EQ2 implies branch-wise EQ2.

If BranchesProjRel CProject gbs role lbs holds, and gbs are transBranches'd,
then the local branches are EQ2-related. -/
theorem BranchesProjRel_implies_BranchesRel_EQ2
    (gbs : List (Label × GlobalType)) (role : String)
    (lbs : List (Label × LocalTypeR)) (hwf : ∀ gb, gb ∈ gbs → gb.2.wellFormed = true)
    (h : BranchesProjRel CProject gbs role lbs) :
    BranchesRel EQ2 lbs (transBranches gbs role) := by
  -- By induction on BranchesProjRel, show each pair is EQ2-related
  induction h with
  | nil =>
      simp [BranchesRel, transBranches]
  | cons hpair hrest ih =>
      rename_i gb lb gbs_tail lbs_tail
      cases gb with
      | mk gLabel gCont =>
          cases lb with
          | mk lLabel lCont =>
              rcases hpair with ⟨hlab, hproj⟩
              -- Extract allCommsNonEmpty from wellFormed
              -- After induction, gbs = (gLabel, gCont) :: gbs_tail
              -- hwf now applies to (gLabel, gCont) :: gbs_tail
              have hmem_head : (gLabel, gCont) ∈ (gLabel, gCont) :: gbs_tail :=
                List.mem_cons_self
              have hwf_head : (gLabel, gCont).2.wellFormed = true := hwf _ hmem_head
              have haces : gCont.allCommsNonEmpty = true := by
                -- wellFormed = (((allVarsBound && allCommsNonEmpty) && noSelfComm) && isProductive)
                simp only [GlobalType.wellFormed] at hwf_head
                -- hwf_head : (((avb && acne) && nsc) && prod) = true
                have h := Bool.and_eq_true_iff.mp hwf_head
                -- h : (((avb && acne) && nsc) = true) ∧ (prod = true)
                have h2 := Bool.and_eq_true_iff.mp h.1
                -- h2 : ((avb && acne) = true) ∧ (nsc = true)
                have h3 := Bool.and_eq_true_iff.mp h2.1
                -- h3 : (avb = true) ∧ (acne = true)
                exact h3.2
              have heq : EQ2 lCont (Trans.trans gCont role) :=
                CProject_implies_EQ2_trans _ _ _ hproj haces
              have hwf_tail : ∀ gb', gb' ∈ gbs_tail → gb'.2.wellFormed = true := by
                intro gb' hmem'
                exact hwf gb' (List.mem_cons_of_mem _ hmem')
              have htail : BranchesRel EQ2 lbs_tail (transBranches gbs_tail role) := ih hwf_tail
              have htail' :
                  List.Forall₂ (fun a b => a.1 = b.1 ∧ EQ2 a.2 b.2)
                    lbs_tail (transBranches gbs_tail role) := by
                simpa [BranchesRel] using htail
              have htb :
                  transBranches ((gLabel, gCont) :: gbs_tail) role =
                    (gLabel, trans gCont role) :: transBranches gbs_tail role := by
                simp [transBranches]
              have hcons :
                  List.Forall₂ (fun a b => a.1 = b.1 ∧ EQ2 a.2 b.2)
                    ((lLabel, lCont) :: lbs_tail)
                    ((gLabel, trans gCont role) :: transBranches gbs_tail role) :=
                List.Forall₂.cons ⟨hlab.symm, by simpa using heq⟩ htail'
              simpa [BranchesRel, htb] using hcons

/-- AllBranchesProj with trans gives EQ2.

For non-participants, AllBranchesProj CProject gbs role lt means all branches
project to lt. The trans of the first branch should be EQ2 to lt. -/
theorem AllBranchesProj_implies_EQ2_trans
    (sender receiver role : String) (gbs : List (Label × GlobalType)) (lt : LocalTypeR)
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hall : AllBranchesProj CProject gbs role lt)
    (hne : gbs ≠ [])
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
    EQ2 lt (trans (GlobalType.comm sender receiver gbs) role) := by
  cases gbs with
  | nil =>
      exact (hne rfl).elim
  | cons first rest =>
      have hproj : CProject first.2 role lt := hall first (by simp)
      -- Extract allCommsNonEmpty for first.2 from wellFormed
      -- wellFormed implies allCommsNonEmpty, which propagates to branches
      have haces_first : first.2.allCommsNonEmpty = true := by
        -- wellFormed = (((allVarsBound && allCommsNonEmpty) && noSelfComm) && isProductive)
        -- allCommsNonEmpty (comm s r bs) = (bs.isEmpty = false) && allCommsNonEmptyBranches bs
        -- allCommsNonEmptyBranches (first :: rest) = first.2.allCommsNonEmpty && ...
        simp only [GlobalType.wellFormed] at hwf
        -- hwf : ((((avb && acne) && nsc) && prod) = true
        have h1 := Bool.and_eq_true_iff.mp hwf
        -- h1 : (((avb && acne) && nsc) = true) ∧ (prod = true)
        have h1' := Bool.and_eq_true_iff.mp h1.1
        -- h1' : ((avb && acne) = true) ∧ (nsc = true)
        have h2 := Bool.and_eq_true_iff.mp h1'.1
        -- h2 : (avb = true) ∧ (acne = true)
        simp only [GlobalType.allCommsNonEmpty, List.isEmpty_eq_false_iff] at h2
        -- h2.2 : (_ ∧ allCommsNonEmptyBranches (first :: rest) = true)
        have h3 := Bool.and_eq_true_iff.mp h2.2
        -- h3 : (first :: rest ≠ []) = true ∧ allCommsNonEmptyBranches (first :: rest) = true
        simp only [allCommsNonEmptyBranches] at h3
        -- h3.2 : first.2.allCommsNonEmpty && allCommsNonEmptyBranches rest = true
        have h4 := Bool.and_eq_true_iff.mp h3.2
        exact h4.1
      have heq : EQ2 lt (Trans.trans first.2 role) :=
        CProject_implies_EQ2_trans _ _ _ hproj haces_first
      have htrans : trans (GlobalType.comm sender receiver (first :: rest)) role =
          trans first.2 role := by
        simpa using trans_comm_other sender receiver role (first :: rest) hns hnr
      simpa [htrans] using heq

/-- CProject is preserved under EQ2 equivalence.

This theorem corresponds to the Coq lemma `Project_EQ2` from indProj.v (lines 263-300).

### Proof Strategy

The proof uses coinduction on CProject with the relation:
```
EQ2_CProject_Rel g role e1 := ∃ e0, CProject g role e0 ∧ EQ2 e0 e1
```

### Case Analysis

**Participant case** (role is sender or receiver):
- By induction on the participation path
- For comm head: e0 = send/recv with some branches, e1 must have same top-level
  structure (by EQ2), so CProject transfers with BranchesRel from EQ2
- For mu: EQ2_unfold gives EQ2 on unfolded types, apply IH

**Non-participant case**:
- CProject requires AllBranchesProj: all branch continuations project to e0
- EQ2 e0 e1 means e1 is observationally equal to e0
- For each branch, we need CProject cont role e1
- This follows by IH on continuations + EQ2 transitivity

### Blocked Cases

The fundamental issue is that CProjectF requires the candidate local type to have
the same top-level constructor as dictated by the global type:
- g = end → candidate = end
- g = var t → candidate = var t
- g = mu t body → candidate = mu t' candBody (with t = t')
- g = comm (sender case) → candidate = send
- g = comm (receiver case) → candidate = recv

But EQ2 allows relating types with different constructors via mu unfolding.
When EQ2 e0 e1 holds with e0 having the "right" constructor but e1 being a mu
(or vice versa), the standard coinduction approach fails.

**Specific blocked cases:**

1. **end-mu / var-mu / send-mu / recv-mu**: When CProject gives e0 with a specific
   constructor but EQ2 e0 e1 where e1 is a mu that unfolds to that constructor.
   CProjectF requires exact constructor matching, but e1 has the wrong constructor.

2. **mu-mu with different binders:** EQ2 allows (.mu t body) ~ (.mu s body') with t ≠ s,
   but CProjectF requires the binder name to match the global type's binder.

3. **mu to non-mu:** When e0 is a mu but e1 unfolds to end/var/send/recv.
   CProjectF requires e1 to be a mu to match g = mu.

The Coq proof uses parametrized coinduction (pcofix) which can "remember" that
e0 and e1 are EQ2-equivalent across unfolding steps, resolving these cases.

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:263-300` for the Coq proof
which uses `pcofix CIH` with participation predicates.

### Semantic Soundness

If `CProject g role e0` holds and `EQ2 e0 e1` (i.e., e0 and e1 are observationally
equivalent under equi-recursive equality), then `CProject g role e1` must hold.
This is because:
1. CProject captures the structure of projecting a global type to a local type
2. EQ2 is an observational equivalence that respects all session type behaviors
3. If e0 satisfies the projection constraints and e1 behaves identically to e0,
   then e1 must also satisfy the projection constraints

The key insight is that EQ2 is a congruence: it preserves structure while allowing
mu-unfolding. The projection relation is defined coinductively, so any finite
observation of e1 can be matched by the corresponding observation of e0. -/
axiom CProject_EQ2_axiom (g : GlobalType) (role : String) (e0 e1 : LocalTypeR)
    (hproj : CProject g role e0) (heq : EQ2 e0 e1) : CProject g role e1

theorem CProject_EQ2 (g : GlobalType) (role : String) (e0 e1 : LocalTypeR)
    (hproj : CProject g role e0) (heq : EQ2 e0 e1) : CProject g role e1 :=
  CProject_EQ2_axiom g role e0 e1 hproj heq

/-- trans produces a valid projection when CProject holds for some candidate.

This is a direct corollary of `CProject_implies_EQ2_trans` and `CProject_EQ2`:
- From h : CProject g role lt, we get EQ2 lt (trans g role)
- By CProject_EQ2 applied to h and this EQ2, we get CProject g role (trans g role)

The key insight is that for non-participants in a choice, all branches must
project to the same local type. The trans function picks the first branch's
projection as representative. Since all branches must agree (by the CProject
constraint), this representative satisfies the projection relation.

Requires `allCommsNonEmpty` assumption (matching Coq's `size_pred`). -/
theorem trans_CProject (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.allCommsNonEmpty = true) : CProject g role (trans g role) := by
  have heq : EQ2 lt (Trans.trans g role) := CProject_implies_EQ2_trans g role lt h hwf
  exact CProject_EQ2 g role lt (Trans.trans g role) h heq

/-- trans computes the canonical projection when CProject holds. -/
theorem trans_is_projection (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.allCommsNonEmpty = true) :
    projectb g role (trans g role) = true :=
  projectb_complete g role (trans g role) (trans_CProject g role lt h hwf)

/-- Completeness: if CProject holds, then projectR? returns some.

Requires `allCommsNonEmpty` assumption (matching Coq's `size_pred`). -/
theorem projectR?_complete (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.allCommsNonEmpty = true) :
    ∃ result, projectR? g role = some result := by
  unfold projectR?
  have hproj : projectb g role (trans g role) = true := trans_is_projection g role lt h hwf
  simp only [hproj, ↓reduceDIte]
  exact ⟨⟨trans g role, projectb_sound g role (trans g role) hproj⟩, rfl⟩

/-- Specification: projectR? returns some iff CProject holds for some local type.

Note: The forward direction (some → CProject) requires no wellFormedness assumption.
The reverse direction (CProject → some) requires `allCommsNonEmpty`. -/
theorem projectR?_some_iff_CProject (g : GlobalType) (role : String) (hwf : g.allCommsNonEmpty = true) :
    (∃ result, projectR? g role = some result) ↔ (∃ lt, CProject g role lt) := by
  constructor
  · intro ⟨result, _⟩
    exact ⟨result.val, result.property⟩
  · intro ⟨lt, h⟩
    exact projectR?_complete g role lt h hwf

end RumpsteakV2.Protocol.Projection.Project
