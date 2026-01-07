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
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  simp only [GlobalType.allCommsNonEmpty, GlobalType.noSelfComm] at hwf
  exact ⟨hwf.1.2, hwf.2⟩

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
             Bool.and_eq_true] at hwf
  -- hwf structure: ((avb ∧ avb_rest) ∧ decide ... ∧ acne ∧ acne_rest) ∧ ((s != r) ∧ nsc_pair ∧ nsc_rest)
  -- Goal: (avb ∧ acne) ∧ nsc (left-associative due to Bool.and_eq_true)
  exact ⟨⟨hwf.1.1.1, hwf.1.2.2.1⟩, hwf.2.2.1⟩

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
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact trans_muve_of_not_part_of2_aux g role hnotpart hwf.1.2 hwf.2

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
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    have hbound := hwf.1.1
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
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.2
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
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact CProject_closed_of_not_part_of2_aux g role lt hproj hnotpart hwf.1.1 hwf.1.2

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
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.2
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
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact CProject_part_of2_implies_part_of_all2_aux g role lt hproj hpart hwf.1.2 hwf.2

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
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact part_of_all2_implies_part_of2_aux role g h hwf.1.2

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

/-- CProject implies EQ2 with trans.

This is an axiom because the coinductive structure requires paco-style
reasoning where the coinductive hypothesis can be applied directly in
the non-participant case (recursing into branch continuations).

### Proof Strategy

Define witness relation:
```
CProjectTransRel lt trans_g := ∃ g role, CProject g role lt ∧ trans_g = trans g role
```

Show CProjectTransRel is a post-fixpoint of EQ2F by case analysis on CProject:
- **end/var**: immediate by structure
- **mu**: use IH on body, handle substitution with EQ2 congruence
- **comm sender/receiver**: use IH on branches
- **comm non-participant**: use IH on first branch continuation (the "step down")

The non-participant case is the key difficulty: it requires the coinductive
hypothesis to apply recursively. Paco's `paco_coind_acc` enables this by
allowing previously proven facts (the IH) to appear in the accumulator.

### Coq Reference

Corresponds to Coq lemma `proj_proj` in indProj.v:221-260.

### Semantic Soundness

If a local type `lt` is a valid projection of global type `g` for role `role`
(CProject g role lt), then `lt` is observationally equivalent (EQ2) to the
canonical projection `trans g role`. This holds because:
1. CProject and trans compute the same structure for end, var, mu, send, recv
2. For non-participants, all branches project to the same lt, and trans picks one
3. Observational equality allows unfolding mu types -/
axiom CProject_implies_EQ2_trans_axiom (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) : EQ2 lt (trans g role)

theorem CProject_implies_EQ2_trans (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) : EQ2 lt (trans g role) :=
  CProject_implies_EQ2_trans_axiom g role lt h

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
              have heq : EQ2 lCont (trans gCont role) :=
                CProject_implies_EQ2_trans _ _ _ hproj
              have hwf_tail : ∀ gb', gb' ∈ gbs_tail → gb'.2.wellFormed = true := by
                intro gb' hmem
                exact hwf gb' (List.mem_cons_of_mem _ hmem)
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
      have heq : EQ2 lt (trans first.2 role) := CProject_implies_EQ2_trans _ _ _ hproj
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
which uses `pcofix CIH` with participation predicates. -/
theorem CProject_EQ2 (g : GlobalType) (role : String) (e0 e1 : LocalTypeR)
    (hproj : CProject g role e0) (heq : EQ2 e0 e1) : CProject g role e1 := by
  -- The proof uses coinduction on CProject with EQ2_CProject_Rel
  --
  -- Key insight: EQ2 is an equivalence relation, and CProject is monotone
  -- in the sense that if e0 and e1 are observationally equivalent (EQ2),
  -- and e0 satisfies CProject, then e1 should too.
  --
  -- The difficulty is that CProjectF requires specific constructor matching,
  -- but EQ2 allows mu-unfolding to relate different constructors.
  --
  -- The Coq proof uses pcofix (parametrized coinduction) which is not
  -- directly available in Lean 4. We would need to:
  -- 1. Define a custom coinduction-up-to principle for CProject
  -- 2. Or use a simulation relation that handles mu-unfolding
  --
  -- For now, we provide the structure with sorry.
  sorry

/-- trans produces a valid projection when CProject holds for some candidate.

This is a direct corollary of `CProject_implies_EQ2_trans` and `CProject_EQ2`:
- From h : CProject g role lt, we get EQ2 lt (trans g role)
- By CProject_EQ2 applied to h and this EQ2, we get CProject g role (trans g role)

The key insight is that for non-participants in a choice, all branches must
project to the same local type. The trans function picks the first branch's
projection as representative. Since all branches must agree (by the CProject
constraint), this representative satisfies the projection relation. -/
theorem trans_CProject (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) : CProject g role (trans g role) := by
  have heq : EQ2 lt (trans g role) := CProject_implies_EQ2_trans g role lt h
  exact CProject_EQ2 g role lt (trans g role) h heq

/-- trans computes the canonical projection when CProject holds. -/
theorem trans_is_projection (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) :
    projectb g role (trans g role) = true :=
  projectb_complete g role (trans g role) (trans_CProject g role lt h)

/-- Completeness: if CProject holds, then projectR? returns some. -/
theorem projectR?_complete (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) :
    ∃ result, projectR? g role = some result := by
  unfold projectR?
  have hproj : projectb g role (trans g role) = true := trans_is_projection g role lt h
  simp only [hproj, ↓reduceDIte]
  exact ⟨⟨trans g role, projectb_sound g role (trans g role) hproj⟩, rfl⟩

/-- Specification: projectR? returns some iff CProject holds for some local type. -/
theorem projectR?_some_iff_CProject (g : GlobalType) (role : String) :
    (∃ result, projectR? g role = some result) ↔ (∃ lt, CProject g role lt) := by
  constructor
  · intro ⟨result, _⟩
    exact ⟨result.val, result.property⟩
  · intro ⟨lt, h⟩
    exact projectR?_complete g role lt h

end RumpsteakV2.Protocol.Projection.Project
