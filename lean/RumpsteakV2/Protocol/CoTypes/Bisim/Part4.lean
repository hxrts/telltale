import RumpsteakV2.Protocol.CoTypes.Bisim.Part3

/-! # Bisim Part 4: Equivalence with EQ2

Proves Bisim implies EQ2 and establishes EQ2 incompatibility lemmas.
-/

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace RumpsteakV2.Protocol.CoTypes.Bisim
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.CoTypes.Observable
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.CoinductiveRel
/-! ## Equivalence with EQ2

The membership predicates in BisimF correspond to unfolding behavior in EQ2F.
We prove Bisim ↔ EQ2, which enables deriving EQ2_trans from Bisim.trans. -/

/-- Convert BranchesRelBisim to BranchesRel (same structure, different namespace). -/
theorem BranchesRelBisim_to_BranchesRel {R : Rel}
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRel R bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih => exact List.Forall₂.cons ⟨hbc.1, hbc.2⟩ ih

/-- Convert BranchesRel to BranchesRelBisim (same structure, different namespace). -/
theorem BranchesRel_to_BranchesRelBisim {R : Rel}
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRel R bs cs) :
    BranchesRelBisim R bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih => exact List.Forall₂.cons ⟨hbc.1, hbc.2⟩ ih

private theorem BranchesRel_to_BranchesRelBisim_EQ2WF
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRel EQ2 bs cs)
    (hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2)
    (hWFcs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2) :
    BranchesRelBisim (fun x y => EQ2 x y ∧ LocalTypeR.WellFormed x ∧ LocalTypeR.WellFormed y) bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons hd_bs hd_cs tl_bs tl_cs hbc _ ih =>
      have hmem_hd_bs : hd_bs ∈ hd_bs :: tl_bs := List.mem_cons_self
      have hmem_hd_cs : hd_cs ∈ hd_cs :: tl_cs := List.mem_cons_self
      have hWFt : LocalTypeR.WellFormed hd_bs.2 := hWFbs hd_bs hmem_hd_bs
      have hWFu : LocalTypeR.WellFormed hd_cs.2 := hWFcs hd_cs hmem_hd_cs
      apply List.Forall₂.cons
      · exact ⟨hbc.1, ⟨hbc.2, hWFt, hWFu⟩⟩
      · exact ih (fun lb hmem => hWFbs lb (List.mem_cons_of_mem _ hmem))
          (fun lb hmem => hWFcs lb (List.mem_cons_of_mem _ hmem))

/-- If two types can both send to the same partner with Bisim-related branches,
    they are Bisim equivalent.

    The proof constructs a witness relation that includes the pair plus all
    continuation pairs from Bisim. -/
theorem Bisim_of_same_send {a b : LocalTypeR} {p : String}
    {bsa bsb : List (Label × LocalTypeR)}
    (ha : CanSend a p bsa) (hb : CanSend b p bsb)
    (hbr : BranchesRelBisim Bisim bsa bsb) : Bisim a b := by
  -- Define witness relation: includes this pair + all Bisim pairs
  let R : Rel := fun x y =>
    (∃ p' bsa' bsb', CanSend x p' bsa' ∧ CanSend y p' bsb' ∧ BranchesRelBisim Bisim bsa' bsb') ∨
    (∃ p' bsa' bsb', CanRecv x p' bsa' ∧ CanRecv y p' bsb' ∧ BranchesRelBisim Bisim bsa' bsb') ∨
    Bisim x y
  use R
  constructor
  · -- Show R is a post-fixpoint of BisimF
    intro x y hxy
    cases hxy with
    | inl hSend =>
      obtain ⟨p', bsa', bsb', hxSend, hySend, hbr'⟩ := hSend
      -- Lift Bisim to R in the branches
      have hbr_R : BranchesRelBisim R bsa' bsb' :=
        BranchesRelBisim.mono (fun a b hBisim => Or.inr (Or.inr hBisim)) hbr'
      exact BisimF.eq_send hxSend hySend hbr_R
    | inr hRest =>
      cases hRest with
      | inl hRecv =>
        obtain ⟨p', bsa', bsb', hxRecv, hyRecv, hbr'⟩ := hRecv
        have hbr_R : BranchesRelBisim R bsa' bsb' :=
          BranchesRelBisim.mono (fun a b hBisim => Or.inr (Or.inr hBisim)) hbr'
        exact BisimF.eq_recv hxRecv hyRecv hbr_R
      | inr hBisim =>
        -- x and y are Bisim, extract witness and use its post-fixpoint property
        obtain ⟨R', hR'post, hxy'⟩ := hBisim
        have hf : BisimF R' x y := hR'post x y hxy'
        -- Lift BisimF R' to BisimF R using monotonicity
        -- R' ⊆ Bisim ⊆ R
        have hR'_to_Bisim : ∀ a b, R' a b → Bisim a b := fun a b h => ⟨R', hR'post, h⟩
        have hR'_to_R : ∀ a b, R' a b → R a b := fun a b h => Or.inr (Or.inr (hR'_to_Bisim a b h))
        exact BisimF.mono hR'_to_R x y hf
  · -- Show R a b via the send case
    exact Or.inl ⟨p, bsa, bsb, ha, hb, hbr⟩

/-- If two types can both recv from the same partner with Bisim-related branches,
    they are Bisim equivalent. -/
theorem Bisim_of_same_recv {a b : LocalTypeR} {p : String}
    {bsa bsb : List (Label × LocalTypeR)}
    (ha : CanRecv a p bsa) (hb : CanRecv b p bsb)
    (hbr : BranchesRelBisim Bisim bsa bsb) : Bisim a b := by
  -- Use same witness relation as Bisim_of_same_send
  let R : Rel := fun x y =>
    (∃ p' bsa' bsb', CanSend x p' bsa' ∧ CanSend y p' bsb' ∧ BranchesRelBisim Bisim bsa' bsb') ∨
    (∃ p' bsa' bsb', CanRecv x p' bsa' ∧ CanRecv y p' bsb' ∧ BranchesRelBisim Bisim bsa' bsb') ∨
    Bisim x y
  use R
  constructor
  · -- Same post-fixpoint proof as Bisim_of_same_send
    intro x y hxy
    cases hxy with
    | inl hSend =>
      obtain ⟨p', bsa', bsb', hxSend, hySend, hbr'⟩ := hSend
      have hbr_R : BranchesRelBisim R bsa' bsb' :=
        BranchesRelBisim.mono (fun a b hBisim => Or.inr (Or.inr hBisim)) hbr'
      exact BisimF.eq_send hxSend hySend hbr_R
    | inr hRest =>
      cases hRest with
      | inl hRecv =>
        obtain ⟨p', bsa', bsb', hxRecv, hyRecv, hbr'⟩ := hRecv
        have hbr_R : BranchesRelBisim R bsa' bsb' :=
          BranchesRelBisim.mono (fun a b hBisim => Or.inr (Or.inr hBisim)) hbr'
        exact BisimF.eq_recv hxRecv hyRecv hbr_R
      | inr hBisim =>
        obtain ⟨R', hR'post, hxy'⟩ := hBisim
        have hf : BisimF R' x y := hR'post x y hxy'
        have hR'_to_Bisim : ∀ a b, R' a b → Bisim a b := fun a b h => ⟨R', hR'post, h⟩
        have hR'_to_R : ∀ a b, R' a b → R a b := fun a b h => Or.inr (Or.inr (hR'_to_Bisim a b h))
        exact BisimF.mono hR'_to_R x y hf
  · -- Show R a b via the recv case
    exact Or.inr (Or.inl ⟨p, bsa, bsb, ha, hb, hbr⟩)

/-- Helper: unfolds-to-end implies EQ2 to .end through unfolding.
    If a unfolds to end, then EQ2 a .end (since unfolding preserves EQ2). -/
theorem UnfoldsToEnd.toEQ2 {a : LocalTypeR} (h : UnfoldsToEnd a) :
    EQ2 a .end := by
  induction h with
  | base => exact EQ2_refl _
  | mu hinner ih =>
    exact EQ2.construct (by simpa [EQ2F] using ih)

/-- Helper: unfolds-to-var implies EQ2 to that var. -/
theorem UnfoldsToVar.toEQ2 {a : LocalTypeR} {v : String} (h : UnfoldsToVar a v) :
    EQ2 a (.var v) := by
  induction h with
  | base => exact EQ2_refl _
  | mu hinner ih =>
    exact EQ2.construct (by simpa [EQ2F] using ih)

/-- Duality is compatible with EQ2. -/
theorem EQ2_dual_compat {a b : LocalTypeR} (h : EQ2 a b) : EQ2 a.dual b.dual :=
  EQ2_dual h

/-- Helper: can-send implies EQ2 to the corresponding send type. -/
theorem CanSend.toEQ2 {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs) : EQ2 a (.send p bs) := by
  refine CanSend.rec (motive := fun a p bs _ => EQ2 a (.send p bs)) ?base ?mu h
  · exact EQ2_refl _
  · intro t body p bs h' ih
    exact EQ2.construct (by simpa [EQ2F] using ih)

/-- Helper: can-recv implies EQ2 to the corresponding recv type. -/
theorem CanRecv.toEQ2 {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs) : EQ2 a (.recv p bs) := by
  -- Reduce recv to send via duality, then dualize the EQ2 witness.
  have hsend : CanSend a.dual p (LocalTypeR.dualBranches bs) := CanRecv.dual h
  have hsend_eq : EQ2 a.dual (.send p (LocalTypeR.dualBranches bs)) := CanSend.toEQ2 hsend
  have hdual := EQ2_dual_compat hsend_eq
  simpa [LocalTypeR.dual, LocalTypeR.dual_dual, dualBranches_dualBranches] using hdual

/-- Helper: CanRecvD implies EQ2 to the corresponding recv type. -/
theorem CanRecvD.toEQ2 {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecvD a p bs) : EQ2 a (.recv p bs) := by
  -- Convert the alias to CanRecv, then reuse CanRecv.toEQ2.
  exact CanRecv.toEQ2 ((CanRecvD_iff_CanRecv).1 h)

/-- Convert BranchesRelBisim to BranchesRel EQ2 when the underlying relation implies EQ2. -/
theorem BranchesRelBisim.toEQ2 {R : Rel} (hR : ∀ a b, R a b → EQ2 a b)
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRel EQ2 bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    exact List.Forall₂.cons ⟨hbc.1, hR _ _ hbc.2⟩ ih

/-- Bisim implies EQ2.

    This is the key theorem: membership-based bisimulation implies coinductive equality.
    The proof uses the EQ2 coinduction principle with Bisim as the witness relation.

    Proof idea:
    - Show that Bisim is a post-fixpoint of EQ2F
    - Case on BisimF to determine observable behavior
    - Use the toEQ2 helpers to convert membership predicates to EQ2 proofs
    - Apply EQ2_coind -/
theorem Bisim.toEQ2 {a b : LocalTypeR} (h : Bisim a b) : EQ2 a b := by
  -- Use EQ2_coind_upto which allows using EQ2 directly in the post-fixpoint proof
  apply EQ2_coind_upto (R := Bisim)
  · -- Show: ∀ x y, Bisim x y → EQ2F (EQ2_closure Bisim) x y
    intro x y hBisim
    obtain ⟨R, hRpost, hxy⟩ := hBisim
    have hf : BisimF R x y := hRpost x y hxy
    -- Case on BisimF to determine observable behavior
    cases hf with
    | eq_end hx hy =>
      -- Both unfold to end, so both are EQ2 to .end
      have hxeq : EQ2 x .end := UnfoldsToEnd.toEQ2 hx
      have hyeq : EQ2 y .end := UnfoldsToEnd.toEQ2 hy
      -- EQ2 x y follows by coinduction through the end constructor
      have hxy_eq2 : EQ2 x y := EQ2_trans_via_end hxeq (EQ2_symm hyeq)
      -- Lift EQ2F EQ2 to EQ2F (EQ2_closure Bisim) using monotonicity
      have hf_eq2 : EQ2F EQ2 x y := EQ2.destruct hxy_eq2
      exact EQ2F.mono (fun _ _ h => Or.inr h) x y hf_eq2
    | eq_var hx hy =>
      -- Both unfold to the same var
      have hxeq : EQ2 x (.var _) := UnfoldsToVar.toEQ2 hx
      have hyeq : EQ2 y (.var _) := UnfoldsToVar.toEQ2 hy
      have hxy_eq2 : EQ2 x y := EQ2_trans_via_var hxeq (EQ2_symm hyeq)
      have hf_eq2 : EQ2F EQ2 x y := EQ2.destruct hxy_eq2
      exact EQ2F.mono (fun _ _ h => Or.inr h) x y hf_eq2
    | @eq_send _ _ partner bsa bsb hx hy hbr =>
      -- Key insight: R ⊆ Bisim since R is a post-fixpoint of BisimF
      have hR_to_Bisim : ∀ a b, R a b → Bisim a b := fun a b hr => ⟨R, hRpost, hr⟩
      -- Lift branches to EQ2_closure Bisim
      have hbr_closure : BranchesRelBisim (EQ2_closure Bisim) bsa bsb :=
        BranchesRelBisim.mono (fun a b h => Or.inl (hR_to_Bisim a b h)) hbr
      -- Convert to BranchesRel for EQ2F (extracted as helper to avoid induction scope issues)
      have hbr_rel : BranchesRel (EQ2_closure Bisim) bsa bsb :=
        BranchesRelBisim_to_BranchesRel hbr_closure
      -- Case on the actual constructors of x and y
      -- Lift branch relation to Bisim for use in Bisim_of_same_send/recv
      have hbr_bisim : BranchesRelBisim Bisim bsa bsb :=
        BranchesRelBisim.mono (fun a b h => hR_to_Bisim a b h) hbr
      cases hx with
      | base =>
        -- x = send partner bsa directly
        cases hy with
        | base =>
          -- y = send partner bsb directly
          -- EQ2F at (send, send) = (partner = partner) ∧ BranchesRel closure bsa bsb
          -- simp reduces partner = partner to True since they're definitionally equal
          simp only [EQ2F]
          exact ⟨trivial, hbr_rel⟩
        | mu hinner =>
          -- y = mu s body, need EQ2F closure (send partner bsa) (mu s body)
          -- which is: closure (send partner bsa) (body.substitute s (mu s body))
          simp only [EQ2F, EQ2_closure]
          -- Both can send to partner with related branches, so they're Bisim
          have hBisim := Bisim_of_same_send CanSend.base hinner hbr_bisim
          exact Or.inl hBisim
      | mu hinner =>
        -- x = mu t body, need EQ2F closure (mu t body) y
        -- Must case on hy to make y concrete for the match to reduce
        cases hy with
        | base =>
          -- y = send partner bsb
          simp only [EQ2F, EQ2_closure]
          have hBisim := Bisim_of_same_send hinner CanSend.base hbr_bisim
          exact Or.inl hBisim
        | mu hinner' =>
          -- y = mu s body'
          -- EQ2F at (mu, mu) = closure pair ∧ closure pair
          simp only [EQ2F, EQ2_closure]
          constructor
          · have hBisim := Bisim_of_same_send hinner (CanSend.mu hinner') hbr_bisim
            exact Or.inl hBisim
          · have hBisim := Bisim_of_same_send (CanSend.mu hinner) hinner' hbr_bisim
            exact Or.inl hBisim
    | @eq_recv _ _ partner bsa bsb hx hy hbr =>
      -- Similar to eq_send with recv
      have hR_to_Bisim : ∀ a b, R a b → Bisim a b := fun a b hr => ⟨R, hRpost, hr⟩
      have hbr_closure : BranchesRelBisim (EQ2_closure Bisim) bsa bsb :=
        BranchesRelBisim.mono (fun a b h => Or.inl (hR_to_Bisim a b h)) hbr
      have hbr_rel : BranchesRel (EQ2_closure Bisim) bsa bsb :=
        BranchesRelBisim_to_BranchesRel hbr_closure
      have hbr_bisim : BranchesRelBisim Bisim bsa bsb :=
        BranchesRelBisim.mono (fun a b h => hR_to_Bisim a b h) hbr
      cases hx with
      | base =>
        cases hy with
        | base =>
          simp only [EQ2F]
          exact ⟨trivial, hbr_rel⟩
        | mu hinner =>
          simp only [EQ2F, EQ2_closure]
          have hBisim := Bisim_of_same_recv CanRecv.base hinner hbr_bisim
          exact Or.inl hBisim
      | mu hinner =>
        -- x = mu t body, need EQ2F closure (mu t body) y
        -- Must case on hy to make y concrete for the match to reduce
        cases hy with
        | base =>
          -- y = recv partner bsb
          simp only [EQ2F, EQ2_closure]
          have hBisim := Bisim_of_same_recv hinner CanRecv.base hbr_bisim
          exact Or.inl hBisim
        | mu hinner' =>
          -- y = mu s body'
          -- EQ2F at (mu, mu) = closure pair ∧ closure pair
          simp only [EQ2F, EQ2_closure]
          constructor
          · have hBisim := Bisim_of_same_recv hinner (CanRecv.mu hinner') hbr_bisim
            exact Or.inl hBisim
          · have hBisim := Bisim_of_same_recv (CanRecv.mu hinner) hinner' hbr_bisim
            exact Or.inl hBisim
  · exact h

/-! ## EQ2 Incompatibility with Observable Behaviors

These lemmas show that `EQ2 .end x` is incompatible with observable behaviors
other than `UnfoldsToEnd`. The proofs use induction on the observable predicates. -/

/-- `EQ2 .end x` is incompatible with `CanSend x p bs`.

    Proof by induction on CanSend. Each constructor exposes a communication head
    that contradicts `EQ2F EQ2 .end _` = False for sends. -/
theorem EQ2_end_not_CanSend {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (hcan : CanSend x p bs) (heq : EQ2 .end x) : False := by
  revert heq
  refine CanSend.rec (motive := fun x p bs _ => EQ2 .end x → False) ?base ?mu hcan
  · intro partner branches heq
    -- x = .send p bs, EQ2 .end (.send p bs) contradicts EQ2F definition
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body p bs h ih heq
    -- x = .mu t body, unfold the EQ2 on the right
    exact ih (by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .end) (b := .mu t body) heq))

/-- `EQ2 .end x` is incompatible with `CanRecv x p bs`. -/
theorem EQ2_end_not_CanRecv {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (hcan : CanRecv x p bs) (heq : EQ2 .end x) : False := by
  have hcan' : CanSend x.dual p (LocalTypeR.dualBranches bs) := CanRecv.dual hcan
  have heq' : EQ2 .end x.dual := by
    have h' := EQ2_dual_compat (a := .end) (b := x) heq
    simpa [LocalTypeR.dual] using h'
  exact EQ2_end_not_CanSend hcan' heq'

/-- `EQ2 .end x` is incompatible with `UnfoldsToVar x v`. -/
theorem EQ2_end_not_UnfoldsToVar {x : LocalTypeR} {v : String}
    (hunf : UnfoldsToVar x v) (heq : EQ2 .end x) : False := by
  revert heq
  refine UnfoldsToVar.rec (motive := fun x v _ => EQ2 .end x → False) ?base ?mu hunf
  · intro v heq
    -- x = .var v, EQ2 .end (.var v) contradicts EQ2F definition
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body v h ih heq
    -- x = .mu t body, unfold the EQ2 on the right
    have heq' : EQ2 .end (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .end) (b := .mu t body) heq)
    exact ih heq'

/-! ## EQ2 Incompatibility: Send vs Observable Behaviors -/

theorem EQ2_send_not_UnfoldsToEnd {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (hunf : UnfoldsToEnd x) (heq : EQ2 (.send p bs) x) : False := by
  revert heq
  refine UnfoldsToEnd.rec (motive := fun x _ => EQ2 (.send p bs) x → False) ?base ?mu hunf
  · intro heq
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body h ih heq
    have heq' : EQ2 (.send p bs) (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .send p bs) (b := .mu t body) heq)
    exact ih heq'

theorem EQ2_send_not_UnfoldsToVar {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    {v : String} (hunf : UnfoldsToVar x v) (heq : EQ2 (.send p bs) x) : False := by
  revert heq
  refine UnfoldsToVar.rec (motive := fun x v _ => EQ2 (.send p bs) x → False) ?base ?mu hunf
  · intro v heq
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body v h ih heq
    have heq' : EQ2 (.send p bs) (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .send p bs) (b := .mu t body) heq)
    exact ih heq'

theorem EQ2_recv_not_UnfoldsToEnd {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (hunf : UnfoldsToEnd x) (heq : EQ2 (.recv p bs) x) : False := by
  revert heq
  refine UnfoldsToEnd.rec (motive := fun x _ => EQ2 (.recv p bs) x → False) ?base ?mu hunf
  · intro heq
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body h ih heq
    have heq' : EQ2 (.recv p bs) (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .recv p bs) (b := .mu t body) heq)
    exact ih heq'

theorem EQ2_recv_not_UnfoldsToVar {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    {v : String} (hunf : UnfoldsToVar x v) (heq : EQ2 (.recv p bs) x) : False := by
  revert heq
  refine UnfoldsToVar.rec (motive := fun x v _ => EQ2 (.recv p bs) x → False) ?base ?mu hunf
  · intro v heq
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body v h ih heq
    have heq' : EQ2 (.recv p bs) (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .recv p bs) (b := .mu t body) heq)
    exact ih heq'

theorem EQ2_recv_not_CanSend {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    {q : String} {cs : List (Label × LocalTypeR)} (hcan : CanSend x q cs)
    (heq : EQ2 (.recv p bs) x) : False := by
  revert heq
  refine CanSend.rec (motive := fun x q cs _ => EQ2 (.recv p bs) x → False) ?base ?mu hcan
  · intro partner branches heq
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body q cs h ih heq
    have heq' : EQ2 (.recv p bs) (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .recv p bs) (b := .mu t body) heq)
    exact ih heq'

theorem EQ2_send_not_CanRecv {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    {q : String} {cs : List (Label × LocalTypeR)} (hcan : CanRecv x q cs)
    (heq : EQ2 (.send p bs) x) : False := by
  -- Dualize the problem and use the recv-vs-send incompatibility.
  have hcan' : CanSend x.dual q (LocalTypeR.dualBranches cs) := CanRecv.dual hcan
  have heq' : EQ2 (.recv p (LocalTypeR.dualBranches bs)) x.dual := by
    -- Dual of send is recv with dualized branches.
    have h' := EQ2_dual_compat (a := .send p bs) (b := x) heq
    simpa [LocalTypeR.dual] using h'
  exact EQ2_recv_not_CanSend (x := x.dual) (p := p)
    (bs := LocalTypeR.dualBranches bs) (q := q) (cs := LocalTypeR.dualBranches cs) hcan' heq'

/-- `EQ2 (.var v) x` is incompatible with `UnfoldsToEnd x`. -/
theorem EQ2_var_not_UnfoldsToEnd {x : LocalTypeR} {v : String}
    (hunf : UnfoldsToEnd x) (heq : EQ2 (.var v) x) : False := by
  revert heq
  refine UnfoldsToEnd.rec (motive := fun x _ => EQ2 (.var v) x → False) ?base ?mu hunf
  · intro heq
    -- x = .end, EQ2 (.var v) .end contradicts EQ2F definition
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body h ih heq
    have heq' : EQ2 (.var v) (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .var v) (b := .mu t body) heq)
    exact ih heq'

/-- `EQ2 (.var v) x` is incompatible with `UnfoldsToVar x w` when w ≠ v. -/
theorem EQ2_var_not_UnfoldsToVar_diff {x : LocalTypeR} {v w : String}
    (hunf : UnfoldsToVar x w) (heq : EQ2 (.var v) x) (hne : w ≠ v) : False := by
  revert heq hne
  refine UnfoldsToVar.rec (motive := fun x w _ => EQ2 (.var v) x → w ≠ v → False) ?base ?mu hunf
  · intro w heq hne
    -- x = .var w, EQ2 (.var v) (.var w) requires v = w
    have hv : v = w := by
      simpa [EQ2F] using (EQ2.destruct heq)
    exact hne hv.symm
  · intro t body w h ih heq hne
    have heq' : EQ2 (.var v) (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .var v) (b := .mu t body) heq)
    exact ih heq' hne

/-- `EQ2 (.var v) x` is incompatible with `CanSend x p bs`. -/
theorem EQ2_var_not_CanSend {x : LocalTypeR} {v : String} {p : String}
    {bs : List (Label × LocalTypeR)}
    (hcan : CanSend x p bs) (heq : EQ2 (.var v) x) : False := by
  revert heq
  refine CanSend.rec (motive := fun x p bs _ => EQ2 (.var v) x → False) ?base ?mu hcan
  · intro partner branches heq
    simpa [EQ2F] using (EQ2.destruct heq)
  · intro t body p bs h ih heq
    have heq' : EQ2 (.var v) (body.substitute t (.mu t body)) := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_right (a := .var v) (b := .mu t body) heq)
    exact ih heq'

/-- `EQ2 (.var v) x` is incompatible with `CanRecv x p bs`. -/
theorem EQ2_var_not_CanRecv {x : LocalTypeR} {v : String} {p : String}
    {bs : List (Label × LocalTypeR)}
    (hcan : CanRecv x p bs) (heq : EQ2 (.var v) x) : False := by
  have hcan' : CanSend x.dual p (LocalTypeR.dualBranches bs) := CanRecv.dual hcan
  have heq' : EQ2 (.var v) x.dual := by
    have h' := EQ2_dual_compat (a := .var v) (b := x) heq
    simpa [LocalTypeR.dual] using h'
  exact EQ2_var_not_CanSend hcan' heq'

end RumpsteakV2.Protocol.CoTypes.Bisim
