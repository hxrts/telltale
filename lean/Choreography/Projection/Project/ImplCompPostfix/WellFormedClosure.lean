import Choreography.Projection.Project.ImplHeadPreservation
import Choreography.Projection.Project.ImplObservables

/-! # Choreography.Projection.Project.ImplCompPostfix.WellFormedClosure

Well-formed closure lifting and base/chain/prefix postfix cases.
-/

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
-/

set_option linter.unnecessarySimpa false

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Projectb
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
open SessionCoTypes.EQ2Paco
open Paco
open SessionTypes.Participation

/-! ## Helper Lemmas for Well-Formed Closure Lifting -/

private theorem lift_eq2_closure_compWF {a b : LocalTypeR}
    (h : EQ2_closure CProjectTransRelComp a b)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) :
    EQ2_closure CProjectTransRelCompWF a b := by
  -- Upgrade a closure witness by pairing with well-formedness at the endpoints.
  cases h with
  | inl hcomp => exact Or.inl ⟨hcomp, hWFa, hWFb⟩
  | inr heq => exact Or.inr heq

theorem BranchesRel_lift_compWF
    {bs cs : List BranchR}
    (h : BranchesRel (EQ2_closure CProjectTransRelComp) bs cs)
    (hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2)
    (hWFcs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2) :
    BranchesRel (EQ2_closure CProjectTransRelCompWF) bs cs := by
  -- Lift each branch pair using the endpoint well-formedness.
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      rename_i b c bs' cs'
      constructor
      · refine ⟨hhead.1, ?_⟩
        exact lift_eq2_closure_compWF hhead.2
          (hWFbs b (List.Mem.head _)) (hWFcs c (List.Mem.head _))
      · exact ih
          (fun lb hm => hWFbs lb (List.Mem.tail _ hm))
          (fun lb hm => hWFcs lb (List.Mem.tail _ hm))

theorem CProjectTransRelCompWF_extend_right {a b c : LocalTypeR}
    (h1 : CProjectTransRelCompWF a b) (h2 : EQ2 b c)
    (hWFa : LocalTypeR.WellFormed a)
    (hWFb : LocalTypeR.WellFormed b)
    (hWFc : LocalTypeR.WellFormed c) : CProjectTransRelCompWF a c := by
  -- Extend the underlying composition and reattach well-formedness.
  exact ⟨CProjectTransRelComp_extend_right h1.1 h2 hWFa hWFb hWFc, hWFa, hWFc⟩

theorem CProjectTransRelCompWF_extend_left {a b c : LocalTypeR}
    (h1 : EQ2 a b) (h2 : CProjectTransRelCompWF b c)
    (hWFa : LocalTypeR.WellFormed a)
    (hWFb : LocalTypeR.WellFormed b)
    (hWFc : LocalTypeR.WellFormed c) : CProjectTransRelCompWF a c := by
  -- Extend the underlying composition and reattach well-formedness.
  exact ⟨CProjectTransRelComp_extend_left h1 h2.1 hWFa hWFb hWFc, hWFa, hWFc⟩

/-! ### EQ2F Lifting Helpers -/

private theorem EQ2F_lift_compWF_send
    {p q : String} {bs cs : List BranchR}
    {h : BranchesRel (EQ2_closure CProjectTransRelComp) bs cs}
    (hWFa : LocalTypeR.WellFormed (.send p bs))
    (hWFc : LocalTypeR.WellFormed (.send q cs)) :
    BranchesRel (EQ2_closure CProjectTransRelCompWF) bs cs := by
  -- Lift branch relations using well-formedness for send branches.
  have hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2 :=
    LocalTypeR.WellFormed.branches_of_send (p := p) (bs := bs) hWFa
  have hWFcs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2 :=
    LocalTypeR.WellFormed.branches_of_send (p := q) (bs := cs) hWFc
  exact BranchesRel_lift_compWF h hWFbs hWFcs

private theorem EQ2F_lift_compWF_recv
    {p q : String} {bs cs : List BranchR}
    {h : BranchesRel (EQ2_closure CProjectTransRelComp) bs cs}
    (hWFa : LocalTypeR.WellFormed (.recv p bs))
    (hWFc : LocalTypeR.WellFormed (.recv q cs)) :
    BranchesRel (EQ2_closure CProjectTransRelCompWF) bs cs := by
  -- Lift branch relations using well-formedness for recv branches.
  have hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2 :=
    LocalTypeR.WellFormed.branches_of_recv (p := p) (bs := bs) hWFa
  have hWFcs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2 :=
    LocalTypeR.WellFormed.branches_of_recv (p := q) (bs := cs) hWFc
  exact BranchesRel_lift_compWF h hWFbs hWFcs

private theorem EQ2F_lift_compWF_mu_left
    {v : String} {body_lt t : LocalTypeR}
    (h : EQ2_closure CProjectTransRelComp (body_lt.substitute v (.mu v body_lt)) t)
    (hWFa : LocalTypeR.WellFormed (.mu v body_lt))
    (hWFc : LocalTypeR.WellFormed t) :
    EQ2_closure CProjectTransRelCompWF (body_lt.substitute v (.mu v body_lt)) t := by
  -- Lift the left-unfold closure using the mu well-formedness.
  have hWF_unfold_lt : LocalTypeR.WellFormed (body_lt.substitute v (.mu v body_lt)) :=
    LocalTypeR.WellFormed.unfold hWFa
  exact lift_eq2_closure_compWF h hWF_unfold_lt hWFc

private theorem EQ2F_lift_compWF_mu_right
    {v : String} {body_t t : LocalTypeR}
    (h : EQ2_closure CProjectTransRelComp t (body_t.substitute v (.mu v body_t)))
    (hWFa : LocalTypeR.WellFormed t)
    (hWFc : LocalTypeR.WellFormed (.mu v body_t)) :
    EQ2_closure CProjectTransRelCompWF t (body_t.substitute v (.mu v body_t)) := by
  -- Lift the right-unfold closure using the mu well-formedness.
  have hWF_unfold_t : LocalTypeR.WellFormed (body_t.substitute v (.mu v body_t)) :=
    LocalTypeR.WellFormed.unfold hWFc
  exact lift_eq2_closure_compWF h hWFa hWF_unfold_t

/- Helper: mu-mu case for EQ2F_lift_compWF. -/
private theorem EQ2F_lift_compWF_mu_mu
    {v v' : String} {body_lt body_t : LocalTypeR}
    (h : EQ2F (EQ2_closure CProjectTransRelComp) (.mu v body_lt) (.mu v' body_t))
    (hWFa : LocalTypeR.WellFormed (.mu v body_lt))
    (hWFc : LocalTypeR.WellFormed (.mu v' body_t)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.mu v body_lt) (.mu v' body_t) := by
  -- Lift both sides of the mu-mu EQ2F payload.
  simp [EQ2F] at h ⊢
  have hWF_unfold_lt : LocalTypeR.WellFormed (body_lt.substitute v (.mu v body_lt)) :=
    LocalTypeR.WellFormed.unfold hWFa
  have hWF_unfold_t : LocalTypeR.WellFormed (body_t.substitute v' (.mu v' body_t)) :=
    LocalTypeR.WellFormed.unfold hWFc
  exact ⟨
    lift_eq2_closure_compWF h.1 hWF_unfold_lt hWFc,
    lift_eq2_closure_compWF h.2 hWFa hWF_unfold_t
  ⟩

private theorem EQ2F_lift_compWF {lt t : LocalTypeR}
    (h : EQ2F (EQ2_closure CProjectTransRelComp) lt t)
    (hWFa : LocalTypeR.WellFormed lt) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) lt t := by
  -- Lift EQ2F across the closure by attaching well-formedness at each endpoint.
  cases lt <;> cases t <;> try (simpa [EQ2F] using h)
  case mu.mu =>
    exact EQ2F_lift_compWF_mu_mu h hWFa hWFc
  all_goals
    simp [EQ2F] at h ⊢
    first
    | exact EQ2F_lift_compWF_mu_right h hWFa hWFc
    | exact EQ2F_lift_compWF_mu_left h hWFa hWFc
    | exact ⟨h.1, EQ2F_lift_compWF_send (h := h.2) hWFa hWFc⟩
    | exact ⟨h.1, EQ2F_lift_compWF_recv (h := h.2) hWFa hWFc⟩
theorem EQ2_CProjectTransRel_compose_through_mu_WF
    {a c : LocalTypeR} {v : String} {body : LocalTypeR}
    (heq : EQ2 a (.mu v body))
    (hrel : CProjectTransRel (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed a) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) a c := by
  -- The target of a mu-projection must be a mu.
  rcases CProjectTransRel_source_mu (v := v) (body := body) (b := c) hrel with ⟨body_c, hc⟩
  subst hc
  have hcomp : EQ2F (EQ2_closure CProjectTransRelComp) a (.mu v body_c) := by
    cases a with
    | mu av abody =>
        -- mu/mu: use the two-step EQ2F decomposition.
        have heq_f : EQ2F EQ2 (.mu av abody) (.mu v body) := EQ2.destruct heq
        simp [EQ2F] at heq_f
        obtain ⟨heq_unfold_left, heq_unfold_right⟩ := heq_f
        simp [EQ2F]
        constructor
        · exact Or.inl (Or.inr (Or.inl ⟨.mu v body, heq_unfold_left, hrel⟩))
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨.mu v body, .mu v body_c, heq, hrel,
            EQ2_unfold_right (EQ2_refl (.mu v body_c))⟩)))
    | «end» | var _ | send _ _ | recv _ _ =>
        -- Non-mu on the left: use the 3-hop chain to the unfolded target.
        simp [EQ2F]
        exact Or.inl (Or.inr (Or.inr (Or.inr ⟨.mu v body, .mu v body_c, heq, hrel,
          EQ2_unfold_right (EQ2_refl (.mu v body_c))⟩)))
  exact EQ2F_lift_compWF hcomp hWFa hWFc

theorem CProjectTransRel_EQ2_compose_through_mu_WF
    {a c : LocalTypeR} {v : String} {body : LocalTypeR}
    (hrel : CProjectTransRel a (.mu v body))
    (heq : EQ2 (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed a) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) a c := by
  -- Lift the existing compose-through-mu lemma into the WF closure.
  have h := CProjectTransRel_EQ2_compose_through_mu hrel heq hWFa hWFc
  exact EQ2F_lift_compWF h hWFa hWFc

private theorem EQ2_CProjectTransRel_EQ2_compose_WF
    {a c : LocalTypeR} {b b' : LocalTypeR}
    (heq1 : EQ2 a b) (hrel : CProjectTransRel b b') (heq2 : EQ2 b' c)
    (hWFa : LocalTypeR.WellFormed a) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) a c := by
  -- Lift the 3-hop composition lemma into the WF closure.
  have h := EQ2_CProjectTransRel_EQ2_compose heq1 hrel heq2 hWFa hWFc
  exact EQ2F_lift_compWF h hWFa hWFc

/-- CProjectTransRelComp is a post-fixpoint of EQ2F.

This extends CProjectTransRel_postfix to handle the composition cases:
- Base case: delegates to CProjectTransRel_postfix
- 2-hop prefix (EQ2 → CProjectTransRel): construct EQ2F using EQ2 destruct + composition
- 2-hop suffix (CProjectTransRel → EQ2): construct EQ2F using composition + EQ2
- 3-hop (EQ2 → CProjectTransRel → EQ2): construct EQ2F using full chain

The key insight: composition cases only arise in mu unfolding chains, where
the EQ2F structure naturally decomposes into chains we can handle. -/
theorem CProjectTransRelComp_postfix_base
    {lt t : LocalTypeR}
    (hbase : CProjectTransRel lt t)
    (hWFa : LocalTypeR.WellFormed lt) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) lt t := by
  -- Base case: lift CProjectTransRel_postfix into the WF closure.
  have hbase_f := CProjectTransRel_postfix lt t hbase
  exact EQ2F_lift_compWF hbase_f hWFa hWFc

theorem CProjectTransRelComp_postfix_chain
    {a c b b' : LocalTypeR}
    (heq_ab : EQ2 a b) (hrel_bb' : CProjectTransRel b b') (heq_b'c : EQ2 b' c)
    (hWFa : LocalTypeR.WellFormed a) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) a c := by
  -- 3-hop chain: lift via the compose lemma into the WF closure.
  exact EQ2_CProjectTransRel_EQ2_compose_WF heq_ab hrel_bb' heq_b'c hWFa hWFc

theorem CProjectTransRelComp_postfix_prefix_mu_mu
    {v v' : String} {body_lt body_t b : LocalTypeR}
    (heq_ab : EQ2 (.mu v body_lt) b) (hrel_bb' : CProjectTransRel b (.mu v' body_t))
    (hWFa : LocalTypeR.WellFormed (.mu v body_lt))
    (hWFc : LocalTypeR.WellFormed (.mu v' body_t)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.mu v body_lt) (.mu v' body_t) := by
  -- Unfold both sides to build the EQ2F conjunction for mu/mu.
  simp only [EQ2F]
  have hWF_unfold_lt : LocalTypeR.WellFormed (body_lt.substitute v (.mu v body_lt)) :=
    LocalTypeR.WellFormed.unfold hWFa
  have hWF_unfold_t : LocalTypeR.WellFormed (body_t.substitute v' (.mu v' body_t)) :=
    LocalTypeR.WellFormed.unfold hWFc
  have hWFb : LocalTypeR.WellFormed b := CProjectTransRel_wf_left hrel_bb'
  have hcomp_b : CProjectTransRelCompWF b (.mu v' body_t) :=
    CProjectTransRelCompWF_of_CProjectTransRel hrel_bb'
  have hcomp_lt_t : CProjectTransRelCompWF (.mu v body_lt) (.mu v' body_t) :=
    CProjectTransRelCompWF_extend_left heq_ab hcomp_b hWFa hWFb hWFc
  constructor
  · have hcomp_left : CProjectTransRelCompWF
        (body_lt.substitute v (.mu v body_lt)) (.mu v' body_t) :=
      CProjectTransRelCompWF_extend_left (EQ2_unfold_left heq_ab) hcomp_b
        hWF_unfold_lt hWFb hWFc
    exact Or.inl hcomp_left
  · have hcomp_right : CProjectTransRelCompWF
        (.mu v body_lt) (body_t.substitute v' (.mu v' body_t)) :=
      CProjectTransRelCompWF_extend_right hcomp_lt_t
        (EQ2_unfold_right (EQ2_refl (.mu v' body_t))) hWFa hWFc hWF_unfold_t
    exact Or.inl hcomp_right

theorem CProjectTransRelComp_postfix_prefix_mu_nonmu
    {v : String} {body_lt t b : LocalTypeR}
    (heq_ab : EQ2 (.mu v body_lt) b) (hrel_bb' : CProjectTransRel b t)
    (hWFa : LocalTypeR.WellFormed (.mu v body_lt)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.mu v body_lt) t := by
  -- Build the left-unfolded composition and split on whether t is mu.
  have hWF_unfold_lt : LocalTypeR.WellFormed (body_lt.substitute v (.mu v body_lt)) :=
    LocalTypeR.WellFormed.unfold hWFa
  have hWFb : LocalTypeR.WellFormed b := CProjectTransRel_wf_left hrel_bb'
  have hcomp_b : CProjectTransRelCompWF b t :=
    CProjectTransRelCompWF_of_CProjectTransRel hrel_bb'
  have hcomp_left : CProjectTransRelCompWF (body_lt.substitute v (.mu v body_lt)) t :=
    CProjectTransRelCompWF_extend_left (EQ2_unfold_left heq_ab) hcomp_b
      hWF_unfold_lt hWFb hWFc
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_prefix_mu_mu
        (v := v) (v' := v') (body_lt := body_lt) (body_t := body_t)
        heq_ab hrel_bb' hWFa hWFc
  | _ =>
      simpa [EQ2F] using (Or.inl hcomp_left)

theorem CProjectTransRelComp_postfix_prefix_nonmu_mu
    {lt b : LocalTypeR} {v' : String} {body_t : LocalTypeR}
    (heq_ab : EQ2 lt b) (hrel_bb' : CProjectTransRel b (.mu v' body_t))
    (hWFa : LocalTypeR.WellFormed lt)
    (hWFc : LocalTypeR.WellFormed (.mu v' body_t)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) lt (.mu v' body_t) := by
  -- Build the right-unfolded composition and split on whether lt is mu.
  have hWF_unfold_t : LocalTypeR.WellFormed (body_t.substitute v' (.mu v' body_t)) :=
    LocalTypeR.WellFormed.unfold hWFc
  have hWFb : LocalTypeR.WellFormed b := CProjectTransRel_wf_left hrel_bb'
  have hcomp_b : CProjectTransRelCompWF b (.mu v' body_t) :=
    CProjectTransRelCompWF_of_CProjectTransRel hrel_bb'
  have hcomp_lt_t : CProjectTransRelCompWF lt (.mu v' body_t) :=
    CProjectTransRelCompWF_extend_left heq_ab hcomp_b hWFa hWFb hWFc
  have hcomp_right : CProjectTransRelCompWF lt (body_t.substitute v' (.mu v' body_t)) :=
    CProjectTransRelCompWF_extend_right hcomp_lt_t
      (EQ2_unfold_right (EQ2_refl (.mu v' body_t))) hWFa hWFc hWF_unfold_t
  cases lt with
  | mu v body_lt =>
      exact CProjectTransRelComp_postfix_prefix_mu_mu
        (v := v) (v' := v') (body_lt := body_lt) (body_t := body_t)
        heq_ab hrel_bb' hWFa hWFc
  | _ =>
      simpa [EQ2F] using (Or.inl hcomp_right)

theorem CProjectTransRelComp_postfix_prefix_var_var
    {x y : String} {b : LocalTypeR}
    (heq_ab : EQ2 (.var x) b) (hrel_bb' : CProjectTransRel b (.var y))
    (hWFa : LocalTypeR.WellFormed (.var x)) (hWFc : LocalTypeR.WellFormed (.var y)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.var x) (.var y) := by
  -- Combine EQ2 destruct with the base postfix relation.
  simp only [EQ2F]
  have heq_f := EQ2.destruct heq_ab
  have hbase_f := CProjectTransRel_postfix b (.var y) hrel_bb'
  cases b with
  | var z =>
      simp only [EQ2F] at heq_f hbase_f
      exact heq_f.trans hbase_f
  | mu _ _ =>
      exact EQ2_CProjectTransRel_compose_through_mu_WF heq_ab hrel_bb' hWFa hWFc
  | «end» => simp only [EQ2F] at heq_f
  | send _ _ => simp only [EQ2F] at heq_f
  | recv _ _ => simp only [EQ2F] at heq_f

end Choreography.Projection.Project
