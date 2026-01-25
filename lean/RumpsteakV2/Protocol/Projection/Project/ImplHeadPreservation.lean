import RumpsteakV2.Protocol.Projection.Project.ImplTransRelComp

set_option linter.unnecessarySimpa false

namespace RumpsteakV2.Protocol.Projection.Project

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Props
open RumpsteakV2.Protocol.CoTypes.EQ2Paco
open Paco
open RumpsteakV2.Protocol.Participation

/-! ## CProjectTransRel head preservation helpers -/

/-- A CProjectTransRel from `.end` can only target `.end`. -/
theorem CProjectTransRel_source_end {b : LocalTypeR}
    (h : CProjectTransRel .end b) : b = .end := by
  -- Unpack the projection witness and use the end preservation lemma.
  rcases h with ⟨g, role, hproj, htrans, hwf⟩
  have hne : g.allCommsNonEmpty = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  have htrans_end := CProject_end_trans_end g role hproj hne
  simpa [htrans_end] using htrans

/-- A CProjectTransRel from `.var v` can only target `.var v`. -/
theorem CProjectTransRel_source_var {v : String} {b : LocalTypeR}
    (h : CProjectTransRel (.var v) b) : b = .var v := by
  -- Reduce to the variable trans lemma.
  rcases h with ⟨g, role, hproj, htrans, hwf⟩
  have hne : g.allCommsNonEmpty = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  have htrans_var := CProject_var_trans_var g role v hproj hne
  simpa [htrans_var] using htrans

/-- A CProjectTransRel from `.send` preserves the send constructor. -/
theorem CProjectTransRel_source_send {p : String} {bs : List (Label × LocalTypeR)} {b : LocalTypeR}
    (h : CProjectTransRel (.send p bs) b) : ∃ cs, b = .send p cs := by
  -- Pull out the trans witnesses and reconstruct the send branches.
  rcases h with ⟨g, role, hproj, htrans, hwf⟩
  obtain ⟨gbs', htrans_send, _, _⟩ :=
    CProject_send_implies_trans_send g role p bs hproj hwf
  refine ⟨transBranches gbs' role, ?_⟩
  simpa [htrans_send] using htrans

/-- A CProjectTransRel from `.recv` preserves the recv constructor. -/
theorem CProjectTransRel_source_recv {p : String} {bs : List (Label × LocalTypeR)} {b : LocalTypeR}
    (h : CProjectTransRel (.recv p bs) b) : ∃ cs, b = .recv p cs := by
  -- Pull out the trans witnesses and reconstruct the recv branches.
  rcases h with ⟨g, role, hproj, htrans, hwf⟩
  obtain ⟨gbs', htrans_recv, _, _⟩ :=
    CProject_recv_implies_trans_recv g role p bs hproj hwf
  refine ⟨transBranches gbs' role, ?_⟩
  simpa [htrans_recv] using htrans

/-- A CProjectTransRel from `.mu` preserves the mu constructor. -/
theorem CProjectTransRel_source_mu {v : String} {body : LocalTypeR} {b : LocalTypeR}
    (h : CProjectTransRel (.mu v body) b) : ∃ body', b = .mu v body' := by
  -- Use the mu trans lemma to expose the projected body.
  rcases h with ⟨g, role, hproj, htrans, hwf⟩
  have hne : g.allCommsNonEmpty = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  obtain ⟨gbody, htrans_mu, _, _, _⟩ :=
    CProject_mu_implies_trans_mu g role v body hproj hne
  refine ⟨trans gbody role, ?_⟩
  simpa [htrans_mu] using htrans

/-! ## CProjectTransRelComp composition lemma (3-hop) -/

/-! ## EQ2 unfolding helpers (for full-unfold route) -/

/-- Unfolding a global type preserves wellFormedness. -/
private theorem GlobalType.wellFormed_unfold (g : GlobalType)
    (hwf : g.wellFormed = true) : (GlobalType.unfold g).wellFormed = true := by
  -- Split on g and reuse the dedicated mu lemma.
  cases g with
  | mu t body =>
      simpa [GlobalType.unfold] using (GlobalType.wellFormed_mu_unfold t body hwf)
  | «end» =>
      simpa [GlobalType.unfold] using hwf
  | var t =>
      simpa [GlobalType.unfold] using hwf
  | comm sender receiver branches =>
      simpa [GlobalType.unfold] using hwf

/-- Iterated unfold preserves wellFormedness. -/
private theorem GlobalType.wellFormed_unfold_iter (g : GlobalType)
    (n : Nat) (hwf : g.wellFormed = true) :
    ((GlobalType.unfold)^[n] g).wellFormed = true := by
  induction n generalizing g with
  | zero =>
      -- No unfold steps.
      simpa using hwf
  | succ n ih =>
      -- One unfold then apply the IH.
      have hwf' : (GlobalType.unfold g).wellFormed = true :=
        GlobalType.wellFormed_unfold g hwf
      simpa [Function.iterate_succ_apply] using (ih (g := GlobalType.unfold g) hwf')

/-- Recursor-style unfold preserves wellFormedness. -/
private theorem GlobalType.wellFormed_unfold_rec (g : GlobalType)
    (n : Nat) (hwf : g.wellFormed = true) :
    (Nat.rec (motive := fun _ => GlobalType) g (fun _ acc => GlobalType.unfold acc) n).wellFormed = true := by
  induction n generalizing g with
  | zero =>
      -- Base case: no unfold.
      simpa using hwf
  | succ n ih =>
      -- Unfold once and apply the IH to the accumulator.
      have hwf' :
          (Nat.rec (motive := fun _ => GlobalType) g (fun _ acc => GlobalType.unfold acc) n).wellFormed = true :=
        ih (g := g) hwf
      simpa using (GlobalType.wellFormed_unfold
        (Nat.rec (motive := fun _ => GlobalType) g (fun _ acc => GlobalType.unfold acc) n) hwf')

/-- Helper: iterate unfold via the Nat.rec form used in trans proofs. -/
private abbrev unfoldRec (g : GlobalType) (n : Nat) : GlobalType :=
  -- Keep the unfold definition explicit for termination/rewrites.
  Nat.rec (motive := fun _ => GlobalType) g (fun _ acc => GlobalType.unfold acc) n

/-- Helper: unfoldRec preserves wellFormed. -/
private theorem wellFormed_unfoldRec (g : GlobalType) (n : Nat) (hwf : g.wellFormed = true) :
    (unfoldRec g n).wellFormed = true := by
  -- Reduce to the recursor lemma.
  simpa [unfoldRec] using GlobalType.wellFormed_unfold_rec g n hwf

/-! ### Unfold commuting for trans -/

/-- Helper: guarded mu case for trans_unfold_EQ2. -/
private theorem trans_unfold_EQ2_mu_guarded
    (t : String) (body : GlobalType) (role : String)
    (hproj' : trans (body.substitute t (.mu t body)) role =
      (trans body role).substitute t (trans (.mu t body) role))
    (hguard : (trans body role).isGuarded t = true) :
    EQ2 (trans (body.substitute t (.mu t body)) role)
      ((trans (.mu t body) role).unfold) := by
  -- Guarded trans produces a mu, so unfold is a substitution.
  have htrans_mu : trans (.mu t body) role = .mu t (trans body role) := by
    simp [Trans.trans, hguard]
  have hleft : trans (body.substitute t (.mu t body)) role =
      (trans body role).substitute t (.mu t (trans body role)) := by
    simpa [htrans_mu] using hproj'
  have hright : (trans (.mu t body) role).unfold =
      (trans body role).substitute t (.mu t (trans body role)) := by
    simp [LocalTypeR.unfold, htrans_mu]
  simpa [GlobalType.unfold, hleft, hright] using
    (EQ2_refl ((trans body role).substitute t (.mu t (trans body role))))

/-- Helper: unguarded mu case for trans_unfold_EQ2. -/
private theorem trans_unfold_EQ2_mu_unguarded
    (t : String) (body : GlobalType) (role : String)
    (hproj' : trans (body.substitute t (.mu t body)) role =
      (trans body role).substitute t (trans (.mu t body) role))
    (hguard : (trans body role).isGuarded t = false) :
    EQ2 (trans (body.substitute t (.mu t body)) role)
      ((trans (.mu t body) role).unfold) := by
  -- Unguarded trans collapses to end; use the unguarded substitution lemma.
  have htrans_end : trans (.mu t body) role = .end := by
    simp [Trans.trans, hguard]
  have hleft : trans (body.substitute t (.mu t body)) role =
      (trans body role).substitute t .end := by
    simpa [htrans_end] using hproj'
  have hright : (trans (.mu t body) role).unfold = .end := by
    simp [LocalTypeR.unfold, htrans_end]
  have heq : EQ2 ((trans body role).substitute t .end) .end :=
    RumpsteakV2.Proofs.Projection.SubstEndUnguarded.subst_end_unguarded_eq2_end
      (trans body role) t hguard
  simpa [GlobalType.unfold, hleft, hright] using heq

/-- Helper: mu case for trans_unfold_EQ2. -/
private theorem trans_unfold_EQ2_mu (t : String) (body : GlobalType) (role : String)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    EQ2 (trans (GlobalType.unfold (.mu t body)) role) ((trans (.mu t body) role).unfold) := by
  -- Commute trans with substitution from unfolding a mu.
  have hclosed : (.mu t body : GlobalType).isClosed = true :=
    GlobalType.isClosed_of_wellFormed (.mu t body) hwf
  have hproj := ProjSubst.proj_subst body t (.mu t body) role hclosed
  have hproj' : trans (body.substitute t (.mu t body)) role =
      (trans body role).substitute t (trans (.mu t body) role) := by
    simpa using hproj
  cases hguard : (trans body role).isGuarded t with
  | true =>
      simpa [GlobalType.unfold] using
        trans_unfold_EQ2_mu_guarded t body role hproj' hguard
  | false =>
      simpa [GlobalType.unfold] using
        trans_unfold_EQ2_mu_unguarded t body role hproj' hguard

/-- trans commutes with one unfold step up to EQ2. -/
private theorem trans_unfold_EQ2 (g : GlobalType) (role : String)
    (hwf : g.wellFormed = true) :
    EQ2 (trans (GlobalType.unfold g) role) ((trans g role).unfold) := by
  -- Split on g; only mu is non-trivial.
  cases g with
  | «end» =>
      -- unfold is identity; trans returns .end.
      have h := EQ2_unfold_right (EQ2_refl (trans (.end) role))
      simpa [GlobalType.unfold, Trans.trans, LocalTypeR.unfold] using h
  | var t =>
      -- unfold is identity; trans returns .var t.
      have h := EQ2_unfold_right (EQ2_refl (trans (.var t) role))
      simpa [GlobalType.unfold, Trans.trans, LocalTypeR.unfold] using h
  | comm sender receiver branches =>
      -- unfold is identity; trans never produces a mu for comm.
      have h := EQ2_unfold_right (EQ2_refl (trans (.comm sender receiver branches) role))
      simpa [GlobalType.unfold, Trans.trans, LocalTypeR.unfold] using h
  | mu t body =>
      -- Delegate the mu case to the specialized helper.
      exact trans_unfold_EQ2_mu t body role hwf

/-- trans after unfold is EQ2 to trans without unfold. -/
private theorem trans_unfold_to_trans (g : GlobalType) (role : String)
    (hwf : g.wellFormed = true) :
    EQ2 (trans (GlobalType.unfold g) role) (trans g role) := by
  -- Compose EQ2 across unfold and well-formedness witnesses.
  have hstep : EQ2 (trans (GlobalType.unfold g) role) ((trans g role).unfold) :=
    trans_unfold_EQ2 g role hwf
  have hback : EQ2 ((trans g role).unfold) (trans g role) :=
    EQ2_unfold_left (EQ2_refl (trans g role))
  have hWFc : LocalTypeR.WellFormed (trans g role) :=
    trans_wellFormed_of_wellFormed g role hwf
  have hWFb : LocalTypeR.WellFormed ((trans g role).unfold) :=
    LocalTypeR.WellFormed.unfold hWFc
  have hwf' : (GlobalType.unfold g).wellFormed = true :=
    GlobalType.wellFormed_unfold g hwf
  have hWFa : LocalTypeR.WellFormed (trans (GlobalType.unfold g) role) :=
    trans_wellFormed_of_wellFormed (GlobalType.unfold g) role hwf'
  exact EQ2_trans_wf hstep hback hWFa hWFb hWFc

/-- Iterated unfold commutes with trans up to EQ2. -/
private theorem trans_unfold_iter_EQ2 (g : GlobalType) (role : String)
    (n : Nat) (hwf : g.wellFormed = true) :
    EQ2
      (trans (unfoldRec g n) role)
      (trans g role) := by
  induction n generalizing g with
  | zero =>
      -- Base: 0 unfolds, reflexivity.
      simpa using (EQ2_refl (trans g role))
  | succ n ih =>
      -- Inductive step: unfold once, then compose EQ2.
      have hwf' : (unfoldRec g n).wellFormed = true := wellFormed_unfoldRec g n hwf
      have hstep :
          EQ2 (trans (GlobalType.unfold (unfoldRec g n)) role) (trans (unfoldRec g n) role) :=
        trans_unfold_to_trans (unfoldRec g n) role hwf'
      have hih : EQ2 (trans (unfoldRec g n) role) (trans g role) :=
        ih (g := g) hwf
      have hWF_mid : LocalTypeR.WellFormed (trans (unfoldRec g n) role) :=
        trans_wellFormed_of_wellFormed (unfoldRec g n) role hwf'
      have hWF_left : LocalTypeR.WellFormed (trans (GlobalType.unfold (unfoldRec g n)) role) :=
        trans_wellFormed_of_wellFormed (GlobalType.unfold (unfoldRec g n)) role
          (GlobalType.wellFormed_unfold (unfoldRec g n) hwf')
      have hWF_final : LocalTypeR.WellFormed (trans g role) :=
        trans_wellFormed_of_wellFormed g role hwf
      simpa using (EQ2_trans_wf hstep hih hWF_left hWF_mid hWF_final)

/-- Full unfold iteration commutes with trans up to EQ2. -/
private theorem trans_fullUnfoldIter_EQ2 (g : GlobalType) (role : String)
    (hwf : g.wellFormed = true) :
    EQ2 (trans (GlobalType.fullUnfoldIter g) role) (trans g role) := by
  -- Unfolding g.muHeight times is the full unfold.
  simpa [GlobalType.fullUnfoldIter] using
    (trans_unfold_iter_EQ2 g role g.muHeight hwf)

/-- Coq-style alias: trans commuting with full unfold. -/
private theorem proj_eq_full (g : GlobalType) (role : String)
    (hwf : g.wellFormed = true) :
    EQ2 (trans (GlobalType.fullUnfoldIter g) role) (trans g role) := by
  -- Keep the alias definally equal to the main lemma.
  exact trans_fullUnfoldIter_EQ2 g role hwf

/-- Iterated unfold on the left preserves EQ2. -/
private theorem EQ2_unfold_left_iter {a b : LocalTypeR} :
    EQ2 a b → ∀ n, EQ2 ((LocalTypeR.unfold)^[n] a) b := by
  intro h n
  induction n generalizing a with
  | zero =>
      -- No unfold steps.
      simpa using h
  | succ n ih =>
      -- Unfold once and use the IH.
      have h' : EQ2 (LocalTypeR.unfold a) b := EQ2_unfold_left h
      simpa [Function.iterate_succ_apply] using (ih h')

/-- Full unfold on the left preserves EQ2. -/
private theorem EQ2_unfold_left_fullUnfold {a b : LocalTypeR} (h : EQ2 a b) :
    EQ2 a.fullUnfold b := by
  -- Expand fullUnfold into muHeight unfolds.
  simpa [LocalTypeR.fullUnfold] using (EQ2_unfold_left_iter (a := a) (b := b) h a.muHeight)

/-- Full unfold on the right preserves EQ2. -/
private theorem EQ2_unfold_right_fullUnfold {a b : LocalTypeR} (h : EQ2 a b) :
    EQ2 a b.fullUnfold := by
  -- Expand fullUnfold into muHeight unfolds.
  simpa [LocalTypeR.fullUnfold] using (EQ2_unfold_right_iter (a := a) (b := b) h b.muHeight)

/-- Extend an EQ2_closure proof on the right by an EQ2 step. -/
private theorem EQ2_closure_extend_right
    {x y z : LocalTypeR}
    (hxy : EQ2_closure CProjectTransRelComp x y) (hyz : EQ2 y z)
    (hWFx : LocalTypeR.WellFormed x)
    (hWFy : LocalTypeR.WellFormed y)
    (hWFz : LocalTypeR.WellFormed z) :
    EQ2_closure CProjectTransRelComp x z := by
  -- Either extend a comp step or compose EQ2 directly.
  cases hxy with
  | inl hr => exact Or.inl (CProjectTransRelComp_extend_right hr hyz hWFx hWFy hWFz)
  | inr heq => exact Or.inr (EQ2_trans_wf heq hyz hWFx hWFy hWFz)

/-- EQ2 relates a mu type to its unfolding. -/
private theorem EQ2_mu_unfold_right (v : String) (body : LocalTypeR) :
    EQ2 (.mu v body) (body.substitute v (.mu v body)) := by
  -- Extract the unfold component from reflexivity.
  have hrefl := EQ2_refl (.mu v body)
  exact (EQ2.destruct hrefl).2

/-- Helper: right component for the mu/mu compose-through-mu case. -/
private theorem CProjectTransRel_EQ2_compose_through_mu_mu_mu_right
    {av v cv : String} {abody body cbody : LocalTypeR}
    (hmid_right :
      EQ2_closure CProjectTransRelComp
        (.mu av abody) (body.substitute v (.mu v body)))
    (heq_left : EQ2 (body.substitute v (.mu v body)) (.mu cv cbody))
    (hWFa : LocalTypeR.WellFormed (.mu av abody))
    (hWF_unfold_mu : LocalTypeR.WellFormed (body.substitute v (.mu v body)))
    (hWF_c : LocalTypeR.WellFormed (.mu cv cbody)) :
    EQ2_closure CProjectTransRelComp
      (.mu av abody) (cbody.substitute cv (.mu cv cbody)) := by
  -- Extend through the mu target and then unfold it.
  have hright_mid :
      EQ2_closure CProjectTransRelComp (.mu av abody) (.mu cv cbody) :=
    EQ2_closure_extend_right hmid_right heq_left hWFa hWF_unfold_mu hWF_c
  have hWF_unfold_c : LocalTypeR.WellFormed (cbody.substitute cv (.mu cv cbody)) :=
    LocalTypeR.WellFormed.unfold hWF_c
  exact EQ2_closure_extend_right hright_mid (EQ2_mu_unfold_right cv cbody) hWFa hWF_c hWF_unfold_c

/-- Composing EQ2 → CProjectTransRel → EQ2 (3-hop) satisfies EQ2F.
    Used to discharge the 3-hop case in CProjectTransRelComp_postfix. -/
theorem EQ2_CProjectTransRel_EQ2_compose
    {a c : LocalTypeR} {b b' : LocalTypeR}
    (heq1 : EQ2 a b) (hrel : CProjectTransRel b b') (heq2 : EQ2 b' c)
    (hWFa : LocalTypeR.WellFormed a) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) a c := by
  -- Use trans_eq_of_CProject to collapse the middle CProjectTransRel witness
  have hWFb : LocalTypeR.WellFormed b := CProjectTransRel_wf_left hrel
  rcases hrel with ⟨g, role, hproj, htrans, hwf⟩
  have hne : g.allCommsNonEmpty = true := by
    simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
    exact hwf.1.1.2
  have htrans_eq : trans g role = b := trans_eq_of_CProject g role b hproj hne
  have hb' : b' = b := by
    simpa [htrans_eq] using htrans
  subst hb'
  -- Now compose the two EQ2 steps and lift to the closure
  have heq_ac : EQ2 a c := EQ2_trans_wf heq1 heq2 hWFa hWFb hWFc
  have hF : EQ2F EQ2 a c := EQ2.destruct heq_ac
  exact EQ2F_mono (fun _ _ h => Or.inr h) hF

/-- Helper: mu/mu target case for CProjectTransRel_EQ2_compose_through_mu. -/
private theorem CProjectTransRel_EQ2_compose_through_mu_mu_mu
    {av v cv : String} {abody body cbody : LocalTypeR}
    (hmid_left :
      EQ2_closure CProjectTransRelComp
        (abody.substitute av (.mu av abody)) (.mu v body))
    (hmid_right :
      EQ2_closure CProjectTransRelComp
        (.mu av abody) (body.substitute v (.mu v body)))
    (heq : EQ2 (.mu v body) (.mu cv cbody))
    (hWFa : LocalTypeR.WellFormed (.mu av abody))
    (hWF_unfold_a : LocalTypeR.WellFormed (abody.substitute av (.mu av abody)))
    (hWF_mu : LocalTypeR.WellFormed (.mu v body))
    (hWF_unfold_mu : LocalTypeR.WellFormed (body.substitute v (.mu v body)))
    (hWF_c : LocalTypeR.WellFormed (.mu cv cbody)) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.mu av abody) (.mu cv cbody) := by
  -- Destructure EQ2 on mu/mu and extend both sides.
  rcases (by
    simpa [EQ2F] using (EQ2.destruct heq)) with ⟨heq_left, _heq_right⟩
  have hleft :
      EQ2_closure CProjectTransRelComp
        (abody.substitute av (.mu av abody)) (.mu cv cbody) :=
    EQ2_closure_extend_right hmid_left heq hWF_unfold_a hWF_mu hWF_c
  have hright :
      EQ2_closure CProjectTransRelComp
        (.mu av abody) (cbody.substitute cv (.mu cv cbody)) :=
    CProjectTransRel_EQ2_compose_through_mu_mu_mu_right
      hmid_right heq_left hWFa hWF_unfold_mu hWF_c
  exact ⟨hleft, hright⟩

/-- Helper: mu/non-mu target case for CProjectTransRel_EQ2_compose_through_mu. -/
private theorem CProjectTransRel_EQ2_compose_through_mu_mu_nonmu
    {av v : String} {abody body c : LocalTypeR}
    (hmid_left :
      EQ2_closure CProjectTransRelComp
        (abody.substitute av (.mu av abody)) (.mu v body))
    (heq : EQ2 (.mu v body) c)
    (hWF_unfold_a : LocalTypeR.WellFormed (abody.substitute av (.mu av abody)))
    (hWF_mu : LocalTypeR.WellFormed (.mu v body))
    (hWF_c : LocalTypeR.WellFormed c) :
    EQ2_closure CProjectTransRelComp (abody.substitute av (.mu av abody)) c := by
  -- Extend the left branch with the EQ2 step.
  exact EQ2_closure_extend_right hmid_left heq hWF_unfold_a hWF_mu hWF_c

/-- Helper: mu source case for CProjectTransRel_EQ2_compose_through_mu. -/
private theorem CProjectTransRel_EQ2_compose_through_mu_mu
    {av : String} {abody : LocalTypeR} {v : String} {body : LocalTypeR} {c : LocalTypeR}
    (hrel : CProjectTransRel (.mu av abody) (.mu v body))
    (heq : EQ2 (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed (.mu av abody))
    (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) (.mu av abody) c := by
  -- Use the postfix lemma to build the intermediate EQ2F step.
  have hmid : EQ2F (EQ2_closure CProjectTransRelComp) (.mu av abody) (.mu v body) :=
    CProjectTransRel_postfix _ _ hrel
  simp only [EQ2F] at hmid
  obtain ⟨hmid_left, hmid_right⟩ := hmid
  have hWF_mu : LocalTypeR.WellFormed (.mu v body) := CProjectTransRel_wf_right hrel
  have hWF_unfold_a : LocalTypeR.WellFormed (abody.substitute av (.mu av abody)) :=
    LocalTypeR.WellFormed.unfold hWFa
  have hWF_unfold_mu : LocalTypeR.WellFormed (body.substitute v (.mu v body)) :=
    LocalTypeR.WellFormed.unfold hWF_mu
  cases c with
  | mu cv cbody =>
      exact CProjectTransRel_EQ2_compose_through_mu_mu_mu
        hmid_left hmid_right heq hWFa hWF_unfold_a hWF_mu hWF_unfold_mu hWFc
  | «end» | var _ | send _ _ | recv _ _ =>
      simpa [EQ2F] using
        (CProjectTransRel_EQ2_compose_through_mu_mu_nonmu
          hmid_left heq hWF_unfold_a hWF_mu hWFc)

/-- Compose an EQ2/CProjectTransRel/EQ2 chain through a mu target. -/
theorem CProjectTransRel_EQ2_compose_through_mu
    {a c : LocalTypeR} {v : String} {body : LocalTypeR}
    (hrel : CProjectTransRel a (.mu v body))
    (heq : EQ2 (.mu v body) c)
    (hWFa : LocalTypeR.WellFormed a) (hWFc : LocalTypeR.WellFormed c) :
    EQ2F (EQ2_closure CProjectTransRelComp) a c := by
  -- Only a mu source can project to a mu target.
  cases a with
  | mu av abody =>
      exact CProjectTransRel_EQ2_compose_through_mu_mu hrel heq hWFa hWFc
  | «end» =>
      cases (CProjectTransRel_source_end (b := .mu v body) hrel)
  | var x =>
      cases (CProjectTransRel_source_var (v := x) (b := .mu v body) hrel)
  | send p bs =>
      rcases CProjectTransRel_source_send (p := p) (bs := bs) (b := .mu v body) hrel with ⟨cs, hEq⟩
      cases hEq
  | recv p bs =>
      rcases CProjectTransRel_source_recv (p := p) (bs := bs) (b := .mu v body) hrel with ⟨cs, hEq⟩
      cases hEq

end RumpsteakV2.Protocol.Projection.Project
