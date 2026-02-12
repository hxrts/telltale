import Choreography.Projection.Project.ImplExtraction.ObservableExtraction

/-! # Choreography.Projection.Project.ImplExtraction.RecvExtraction

Recv extraction and mu-intermediate composition for observable structure.
-/

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
-/

set_option linter.unnecessarySimpa false

/-! ## Core Development -/

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

/-! ## Recv Extraction Base Case -/

private theorem CProjectTransRelComp_recv_extract_base
    {p1 p2 : String} {bs1 bs2 : List BranchR}
    (hbase : CProjectTransRel (.recv p1 bs1) (.recv p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
	  -- Base CProjectTransRel implies postfix EQ2F on recv.
	  have hbase_f := CProjectTransRel_postfix (.recv p1 bs1) (.recv p2 bs2) hbase
	  simpa [EQ2F] using hbase_f

/-! ## Recv Extraction Left Case -/

/- Helper: left case for CProjectTransRelComp_recv_extract. -/
private theorem CProjectTransRelComp_recv_extract_left
    {p1 p2 : String} {bs1 bs2 : List BranchR} {b : LocalTypeR}
    (heq : EQ2 (.recv p1 bs1) b) (hrel : CProjectTransRel b (.recv p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.recv p1 bs1))
    (hWFc : LocalTypeR.WellFormed (.recv p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  cases b with -- Split the intermediate b and lift branch relations when possible.
  | recv pb bbs =>
      have hWFb : LocalTypeR.WellFormed (.recv pb bbs) := CProjectTransRel_wf_left hrel
      have heq_f : EQ2F EQ2 (.recv p1 bs1) (.recv pb bbs) := EQ2.destruct heq
      have hrel_f := CProjectTransRel_postfix (.recv pb bbs) (.recv p2 bs2) hrel
      simp [EQ2F] at heq_f hrel_f
      obtain ⟨hp1, hbs1⟩ := heq_f
      obtain ⟨hp2, hbs2⟩ := hrel_f
      refine ⟨hp1.trans hp2, ?_⟩
      have hWFbs1 : ∀ lb ∈ bs1, LocalTypeR.WellFormed lb.2.2 := recv_branches_wf p1 bs1 hWFa;
        have hWFbbs : ∀ lb ∈ bbs, LocalTypeR.WellFormed lb.2.2 := recv_branches_wf pb bbs hWFb
      have hWFbs2 : ∀ lb ∈ bs2, LocalTypeR.WellFormed lb.2.2 := recv_branches_wf p2 bs2 hWFc
      exact BranchesRel_trans_chain_rev_noWF
        (fun a b c => CProjectTransRelComp_extend_left_noWF (a := a) (b := b) (c := c))
        hbs1 hbs2 hWFbs1 hWFbbs hWFbs2
  | mu t body =>
      rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .recv p2 bs2) hrel
        with ⟨body', hEq⟩
      cases hEq
	  | «end» | var _ | send _ _ =>
	      simpa [EQ2F] using (EQ2.destruct heq)

/-! ## Recv Extraction Right Case -/

/- Helper: right case for CProjectTransRelComp_recv_extract. -/
private theorem CProjectTransRelComp_recv_extract_right
    {p1 p2 : String} {bs1 bs2 : List BranchR} {b : LocalTypeR}
    (hrel : CProjectTransRel (.recv p1 bs1) b) (heq : EQ2 b (.recv p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.recv p1 bs1))
    (hWFc : LocalTypeR.WellFormed (.recv p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  -- Split the intermediate b and lift branch relations when possible.
  cases b with
  | recv pb bbs =>
      have hWFb : LocalTypeR.WellFormed (.recv pb bbs) := CProjectTransRel_wf_right hrel;
        have hrel_f := CProjectTransRel_postfix (.recv p1 bs1) (.recv pb bbs) hrel;
        have heq_f : EQ2F EQ2 (.recv pb bbs) (.recv p2 bs2) := EQ2.destruct heq
      simp [EQ2F] at hrel_f heq_f
      obtain ⟨hp1, hbs1⟩ := hrel_f; obtain ⟨hp2, hbs2⟩ := heq_f
      refine ⟨hp1.trans hp2, ?_⟩
      have hWFbs1 : ∀ lb ∈ bs1, LocalTypeR.WellFormed lb.2.2 := recv_branches_wf p1 bs1 hWFa
      have hWFbbs : ∀ lb ∈ bbs, LocalTypeR.WellFormed lb.2.2 := recv_branches_wf pb bbs hWFb
      have hWFbs2 : ∀ lb ∈ bs2, LocalTypeR.WellFormed lb.2.2 := recv_branches_wf p2 bs2 hWFc
      exact BranchesRel_trans_chain_noWF
        (fun a b c => CProjectTransRelComp_extend_right_noWF (a := a) (b := b) (c := c))
        hbs1 hbs2 hWFbs1 hWFbbs hWFbs2
  | mu t body =>
      rcases CProjectTransRel_source_recv (p := p1) (bs := bs1) (b := .mu t body) hrel with
        ⟨cs, hEq⟩
      cases hEq
  | «end» =>
      have hrel_f := CProjectTransRel_postfix (.recv p1 bs1) .end (by simpa using hrel)
      simpa [EQ2F] using hrel_f
  | var v =>
      have hrel_f := CProjectTransRel_postfix (.recv p1 bs1) (.var v) (by simpa using hrel)
      simpa [EQ2F] using hrel_f
	  | send q cs =>
	      have hrel_f := CProjectTransRel_postfix (.recv p1 bs1) (.send q cs) (by simpa using hrel)
	      simpa [EQ2F] using hrel_f

/-! ## Recv Extraction Both Case -/

/- Helper: both case for CProjectTransRelComp_recv_extract. -/
private theorem CProjectTransRelComp_recv_extract_both
    {p1 p2 : String} {bs1 bs2 : List BranchR} {b b' : LocalTypeR}
    (heq : EQ2 (.recv p1 bs1) b) (hrel : CProjectTransRel b b') (heq' : EQ2 b' (.recv p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.recv p1 bs1))
    (hWFc : LocalTypeR.WellFormed (.recv p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  -- Compose EQ2 ∘ CProjectTransRel ∘ EQ2, then destruct the recv case.
  have hcomp :=
    EQ2_CProjectTransRel_EQ2_compose (a := .recv p1 bs1) (c := .recv p2 bs2) heq hrel heq'
      hWFa hWFc
	  simpa [EQ2F] using hcomp

/-! ## Recv Extraction Dispatcher -/

private theorem CProjectTransRelComp_recv_extract
    {p1 p2 : String} {bs1 bs2 : List BranchR}
    (h : CProjectTransRelComp (.recv p1 bs1) (.recv p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.recv p1 bs1))
    (hWFc : LocalTypeR.WellFormed (.recv p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  rcases h with hbase | hleft | hright | hboth -- Split the composed relation into base/left/right/both cases.
  · exact CProjectTransRelComp_recv_extract_base hbase
  · rcases hleft with ⟨b, heq, hrel⟩; exact CProjectTransRelComp_recv_extract_left heq hrel hWFa hWFc
	  · rcases hright with ⟨b, hrel, heq⟩; exact CProjectTransRelComp_recv_extract_right hrel heq hWFa hWFc
	  · rcases hboth with ⟨b, b', heq, hrel, heq'⟩; exact CProjectTransRelComp_recv_extract_both heq hrel heq' hWFa hWFc

/-! ## Mu Intermediate Helpers -/

/-- Composing EQ2 and CProjectTransRel through a mu intermediate satisfies EQ2F.

    **Proof strategy**:
    1. Use CProjectTransRel_postfix to get: EQ2F (EQ2_closure CProjectTransRelComp) (.mu v body) c
    2. Use monotonicity to lift: EQ2_closure CProjectTransRel ⊆ EQ2_closure CProjectTransRelComp
       (since CProjectTransRel is the base case of CProjectTransRelComp)
    3. Apply EQ2F.mono to get the result

    This proof doesn't require paco_coind because we're proving a single-step property (EQ2F),
    not a coinductive relation. We leverage:
    - The existing CProjectTransRel_postfix theorem (which already handles the mu unfolding)
    - Monotonicity of EQ2F
    - The fact that CProjectTransRel ⊆ CProjectTransRelComp

    All 62 mu-intermediate cases are resolved uniformly by this theorem. -/
private theorem EQ2_unfold_mu (t : String) (body : LocalTypeR) :
    EQ2 (.mu t body) (body.substitute t (.mu t body)) := by
  -- Use reflexivity then destruct to expose the unfold equation.
	  have hrefl := EQ2_refl (.mu t body)
	  exact (EQ2.destruct hrefl).2

/-! ## Mu Intermediate Relation Wrapper -/

private theorem CProjectTransRelComp_of_mu {a c : LocalTypeR} {v : String} {body : LocalTypeR}
    (heq : EQ2 a (.mu v body)) (hrel : CProjectTransRel (.mu v body) c) :
    CProjectTransRelComp a c := by
	  -- Wrap EQ2 ∘ CProjectTransRel into the composed relation.
	  exact Or.inr (Or.inl ⟨.mu v body, heq, hrel⟩)

/-! ## Through-Mu: Mu/End Target -/

private theorem EQ2_CProjectTransRel_compose_through_mu_mu_end
    {av v : String} {abody body : LocalTypeR}
    (heq_unfold_left : EQ2 (abody.substitute av (.mu av abody)) (.mu v body))
    (hrel : CProjectTransRel (.mu v body) .end) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.mu av abody) .end := by
  -- Mu on the left, end on the right: use the EQ2 prefix.
  simp only [EQ2F]
	  left; right; left
	  exact ⟨.mu v body, heq_unfold_left, hrel⟩

/-! ## Through-Mu: Mu/Var Target -/

private theorem EQ2_CProjectTransRel_compose_through_mu_mu_var
    {av v : String} {abody body : LocalTypeR} {cv : String}
    (heq_unfold_left : EQ2 (abody.substitute av (.mu av abody)) (.mu v body))
    (hrel : CProjectTransRel (.mu v body) (.var cv)) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.mu av abody) (.var cv) := by
  -- Mu on the left, var on the right: use the EQ2 prefix.
  simp only [EQ2F]
	  left; right; left
	  exact ⟨.mu v body, heq_unfold_left, hrel⟩

/-! ## Through-Mu: Mu/Send Target -/

private theorem EQ2_CProjectTransRel_compose_through_mu_mu_send
    {av v : String} {abody body : LocalTypeR} {cp : String}
    {cbs : List BranchR}
    (heq_unfold_left : EQ2 (abody.substitute av (.mu av abody)) (.mu v body))
    (hrel : CProjectTransRel (.mu v body) (.send cp cbs)) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.mu av abody) (.send cp cbs) := by
  -- Mu on the left, send on the right: use the EQ2 prefix.
  simp only [EQ2F]
	  left; right; left
	  exact ⟨.mu v body, heq_unfold_left, hrel⟩

/-! ## Through-Mu: Mu/Recv Target -/

private theorem EQ2_CProjectTransRel_compose_through_mu_mu_recv
    {av v : String} {abody body : LocalTypeR} {cp : String}
    {cbs : List BranchR}
    (heq_unfold_left : EQ2 (abody.substitute av (.mu av abody)) (.mu v body))
    (hrel : CProjectTransRel (.mu v body) (.recv cp cbs)) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.mu av abody) (.recv cp cbs) := by
  -- Mu on the left, recv on the right: use the EQ2 prefix.
  simp only [EQ2F]
	  left; right; left
	  exact ⟨.mu v body, heq_unfold_left, hrel⟩

/-! ## Through-Mu: Mu Source Dispatcher -/

private theorem EQ2_CProjectTransRel_compose_through_mu_mu
    {av v : String} {abody body c : LocalTypeR}
    (heq : EQ2 (.mu av abody) (.mu v body))
    (hrel : CProjectTransRel (.mu v body) c) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.mu av abody) c := by
  -- Unfold EQ2F for the left mu, then dispatch on c.
  have heq_f : EQ2F EQ2 (.mu av abody) (.mu v body) := EQ2.destruct heq
  simp only [EQ2F] at heq_f
  obtain ⟨heq_unfold_left, _heq_unfold_right⟩ := heq_f
  cases c with
  | mu cv cbody =>
      simp only [EQ2F]
      constructor
      · left; right; left
        exact ⟨.mu v body, heq_unfold_left, hrel⟩
      · left; right; right; right
        exact ⟨.mu v body, .mu cv cbody, heq, hrel, EQ2_unfold_mu cv cbody⟩
  | «end» =>
      exact EQ2_CProjectTransRel_compose_through_mu_mu_end heq_unfold_left hrel
  | var cv =>
      exact EQ2_CProjectTransRel_compose_through_mu_mu_var heq_unfold_left hrel
  | send cp cbs =>
      exact EQ2_CProjectTransRel_compose_through_mu_mu_send heq_unfold_left hrel
	  | recv cp cbs =>
	      exact EQ2_CProjectTransRel_compose_through_mu_mu_recv heq_unfold_left hrel

/-! ## Through-Mu: End Source -/

private theorem EQ2_CProjectTransRel_compose_through_mu_end
    {v : String} {body c : LocalTypeR}
    (heq : EQ2 .end (.mu v body)) (hrel : CProjectTransRel (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed .end) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) .end c := by
  -- End can only relate via the composed mu witness.
  cases c with
  | mu cv cbody =>
      simp only [EQ2F]
      left; right; right; right
      exact ⟨.mu v body, .mu cv cbody, heq, hrel, EQ2_unfold_mu cv cbody⟩
  | «end» =>
      simp only [EQ2F]
  | var _ =>
      simp only [EQ2F]
      exact CProjectTransRelComp_end_not_var (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
  | send _ _ =>
      simp only [EQ2F]
      exact CProjectTransRelComp_end_not_send (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
	  | recv _ _ =>
	      simp only [EQ2F]
	      exact CProjectTransRelComp_end_not_recv (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc

/-! ## Through-Mu: Var Source -/

private theorem EQ2_CProjectTransRel_compose_through_mu_var
    {av v : String} {body c : LocalTypeR}
    (heq : EQ2 (.var av) (.mu v body)) (hrel : CProjectTransRel (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed (.var av)) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.var av) c := by
  -- Var case follows by extraction or contradiction.
  cases c with
  | mu cv cbody =>
      simp only [EQ2F]
      left; right; right; right
      exact ⟨.mu v body, .mu cv cbody, heq, hrel, EQ2_unfold_mu cv cbody⟩
  | var _ =>
      simp only [EQ2F]
      exact CProjectTransRelComp_var_extract (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
  | «end» =>
      simp only [EQ2F]
      exact CProjectTransRelComp_var_not_end (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
  | send _ _ =>
      simp only [EQ2F]
      exact CProjectTransRelComp_var_not_send (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
	  | recv _ _ =>
	      simp only [EQ2F]
	      exact CProjectTransRelComp_var_not_recv (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc

/-! ## Through-Mu: Send Source -/

private theorem EQ2_CProjectTransRel_compose_through_mu_send
    {ap v : String} {abs : List BranchR} {body c : LocalTypeR}
    (heq : EQ2 (.send ap abs) (.mu v body)) (hrel : CProjectTransRel (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed (.send ap abs)) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.send ap abs) c := by
  -- Send case follows by extraction or contradiction.
  cases c with
  | mu cv cbody =>
      simp only [EQ2F]
      left; right; right; right
      exact ⟨.mu v body, .mu cv cbody, heq, hrel, EQ2_unfold_mu cv cbody⟩
  | send _ _ =>
      simp only [EQ2F]
      exact CProjectTransRelComp_send_extract (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
  | «end» =>
      simp only [EQ2F]
      exact CProjectTransRelComp_send_not_end (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
  | var _ =>
      simp only [EQ2F]
      exact CProjectTransRelComp_send_not_var (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
	  | recv _ _ =>
	      simp only [EQ2F]
	      exact CProjectTransRelComp_send_not_recv (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc

/-! ## Through-Mu: Recv Source -/

private theorem EQ2_CProjectTransRel_compose_through_mu_recv
    {ap v : String} {abs : List BranchR} {body c : LocalTypeR}
    (heq : EQ2 (.recv ap abs) (.mu v body)) (hrel : CProjectTransRel (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed (.recv ap abs)) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.recv ap abs) c := by
  -- Recv case follows by extraction or contradiction.
  cases c with
  | mu cv cbody =>
      simp only [EQ2F]
      left; right; right; right
      exact ⟨.mu v body, .mu cv cbody, heq, hrel, EQ2_unfold_mu cv cbody⟩
  | recv _ _ =>
      simp only [EQ2F]
      exact CProjectTransRelComp_recv_extract (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
  | «end» =>
      simp only [EQ2F]
      exact CProjectTransRelComp_recv_not_end (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
  | var _ =>
      simp only [EQ2F]
      exact CProjectTransRelComp_recv_not_var (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc
	  | send _ _ =>
	      simp only [EQ2F]
	      exact CProjectTransRelComp_recv_not_send (CProjectTransRelComp_of_mu heq hrel) hWFa hWFc

/-! ## Through-Mu Final Theorem -/

/-- Compose EQ2 on the left with CProjectTransRel through a mu head. -/
theorem EQ2_CProjectTransRel_compose_through_mu
    {a c : LocalTypeR} {v : String} {body : LocalTypeR}
    (heq : EQ2 a (.mu v body))
    (hrel : CProjectTransRel (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed a) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) a c := by
  -- Case analysis on a
  cases a with
  | mu av abody =>
      exact EQ2_CProjectTransRel_compose_through_mu_mu heq hrel
  | «end» =>
      exact EQ2_CProjectTransRel_compose_through_mu_end heq hrel LocalTypeR.WellFormed_end hWFc
  | var av =>
      exact EQ2_CProjectTransRel_compose_through_mu_var heq hrel hWFa hWFc
  | send ap abs =>
      exact EQ2_CProjectTransRel_compose_through_mu_send heq hrel hWFa hWFc
  | recv ap abs =>
      exact EQ2_CProjectTransRel_compose_through_mu_recv heq hrel hWFa hWFc


end Choreography.Projection.Project
