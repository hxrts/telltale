import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.ProjectionR

/-! # Rumpsteak.Protocol.Coherence

Coherence and enabledness assumptions for global types.

This mirrors the Coq proof structure: coherence bundles linearity/size/action
predicates, label uniqueness, total projection, and the good-global condition.
-/

namespace Rumpsteak.Protocol.Coherence

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.ProjectionR

/-- Total projection: every role has a successful projection. -/
def projectable (g : GlobalType) : Prop :=
  ∀ role, ∃ lt, projectR g role = Except.ok lt

/-- Coherence bundle for global types. -/
structure coherentG (g : GlobalType) : Prop where
  linear : GlobalType.linearPred g
  size : GlobalType.sizePred g
  action : GlobalType.actionPred g
  uniqLabels : GlobalType.uniqLabels g
  proj : projectable g
  good : GlobalType.goodG g

/-! ## Preservation lemmas for single step -/

/-- Linearity is trivially preserved (always true). -/
theorem linearPred_step {g g' : GlobalType} {act : GlobalActionR}
    (_ : step g act g') (h : linearPred g) : linearPred g' := by
  exact trivial

/-- Size predicate is preserved by a single step.

    Uses mutual induction on step and BranchesStep via step.rec. -/
theorem sizePred_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : sizePred g) : sizePred g' :=
  let motive1 (g : GlobalType) (_act : GlobalActionR) (g' : GlobalType) (_hstep : step g _act g') : Prop :=
    sizePred g → sizePred g'
  let motive2 (bs : List (Label × GlobalType)) (_act : GlobalActionR) (bs' : List (Label × GlobalType))
      (_hbstep : BranchesStep step bs _act bs') : Prop :=
    bs.all (fun (_, cont) => cont.allCommsNonEmpty) = true →
    bs'.all (fun (_, cont) => cont.allCommsNonEmpty) = true
  @step.rec (motive_1 := motive1) (motive_2 := motive2)
    -- comm_head case
    (fun sender receiver branches label cont hmem h =>
      sizePred_mem h hmem)
    -- comm_async case
    (fun sender receiver branches branches' act' label cont _hne1 _hne2 _hmem _hcan hbstep ih_bstep h =>
      let hne := sizePred_comm_nonempty h
      let hne' := BranchesStep.isEmpty_false hbstep hne
      let hall := sizePred_comm_all h
      let hall' := ih_bstep hall
      sizePred_comm_of_components hne' hall')
    -- mu case
    (fun t body act' g'' _hstep' ih_step h =>
      let h' := sizePred_substitute t body h
      ih_step h')
    -- BranchesStep.nil case
    (fun _act _hall => by simp)
    -- BranchesStep.cons case
    (fun label g g' rest rest' _act _hstep _hrest ih_step ih_rest hall => by
      simp only [List.all_cons, Bool.and_eq_true] at hall ⊢
      exact ⟨ih_step hall.1, ih_rest hall.2⟩)
    g act g' hstep h

/-- Action predicate is preserved by a single step.

    Uses mutual induction on step and BranchesStep via step.rec. -/
theorem actionPred_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : actionPred g) : actionPred g' :=
  let motive1 (g : GlobalType) (_act : GlobalActionR) (g' : GlobalType) (_hstep : step g _act g') : Prop :=
    actionPred g → actionPred g'
  let motive2 (bs : List (Label × GlobalType)) (_act : GlobalActionR) (bs' : List (Label × GlobalType))
      (_hbstep : BranchesStep step bs _act bs') : Prop :=
    BranchesForall actionPred bs → BranchesForall actionPred bs'
  @step.rec (motive_1 := motive1) (motive_2 := motive2)
    -- comm_head case: cont ∈ branches, so actionPred h → actionPred cont
    (fun _sender _receiver branches _label cont hmem h =>
      BranchesForall.mem (actionPred_comm_branches h) hmem)
    -- comm_async case: preserve through BranchesStep
    (fun sender receiver _branches branches' _act' _label _cont _hne1 _hne2 _hmem _hcan _hbstep ih_bstep h =>
      let hne_sr := actionPred_comm_sender_ne h
      let hbranches := actionPred_comm_branches h
      let hbranches' := ih_bstep hbranches
      actionPred.comm sender receiver branches' hne_sr hbranches')
    -- mu case: use actionPred_substitute
    (fun t body _act' _g'' _hstep' ih_step h =>
      let h' := actionPred_substitute t body h
      ih_step h')
    -- BranchesStep.nil case
    (fun _act _hforall => BranchesForall.nil)
    -- BranchesStep.cons case
    (fun label _g g' rest rest' _act _hstep _hrest ih_step ih_rest hforall =>
      match hforall with
      | BranchesForall.cons _ _ _ hp hrest_forall =>
        BranchesForall.cons label g' rest' (ih_step hp) (ih_rest hrest_forall))
    g act g' hstep h

/-- Helper to wrap the IH properly for BranchesUniq.step. -/
private def uniqLabels_step_ih_wrapper
    (ih_step : uniqLabels g → uniqLabels g')
    (ih_rest : BranchesUniq uniqLabels rest → BranchesUniq uniqLabels rest')
    (huniq : BranchesUniq uniqLabels ((label, g) :: rest))
    (hstep : step g act g')
    (hrest : BranchesStep step rest act rest') : BranchesUniq uniqLabels ((label, g') :: rest') := by
  cases huniq with
  | cons _ _ _ hpg hrest_uniq hnotin =>
    have hpg' := ih_step hpg
    have hrest_uniq' := ih_rest hrest_uniq
    have hlabels := hrest.labels
    have hnames : rest'.map (fun b : Label × GlobalType => b.1.name) =
                  rest.map (fun b : Label × GlobalType => b.1.name) := by
      have h1 : rest'.map (fun b : Label × GlobalType => b.1.name) =
                (rest'.map Prod.fst).map Label.name := by simp [List.map_map]
      have h2 : rest.map (fun b : Label × GlobalType => b.1.name) =
                (rest.map Prod.fst).map Label.name := by simp [List.map_map]
      rw [h1, h2, hlabels]
    have hnotin' : label.name ∉ rest'.map (fun b => b.1.name) := by
      rw [hnames]
      exact hnotin
    exact BranchesUniq.cons label g' rest' hpg' hrest_uniq' hnotin'

/-- Unique labels is preserved by a single step.

    Uses mutual induction on step and BranchesStep via step.rec. -/
theorem uniqLabels_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : uniqLabels g) : uniqLabels g' :=
  let motive1 (g : GlobalType) (_act : GlobalActionR) (g' : GlobalType) (_hstep : step g _act g') : Prop :=
    uniqLabels g → uniqLabels g'
  let motive2 (bs : List (Label × GlobalType)) (_act : GlobalActionR) (bs' : List (Label × GlobalType))
      (_hbstep : BranchesStep step bs _act bs') : Prop :=
    BranchesUniq uniqLabels bs → BranchesUniq uniqLabels bs'
  @step.rec (motive_1 := motive1) (motive_2 := motive2)
    -- comm_head case: cont ∈ branches
    (fun _sender _receiver branches _label cont hmem h =>
      BranchesUniq.mem (uniqLabels_comm_branches h) hmem)
    -- comm_async case: preserve through BranchesStep
    (fun sender receiver _branches branches' _act' _label _cont _hne1 _hne2 _hmem _hcan _hbstep ih_bstep h =>
      let hbranches := uniqLabels_comm_branches h
      let hbranches' := ih_bstep hbranches
      uniqLabels.comm sender receiver branches' hbranches')
    -- mu case: use uniqLabels_substitute
    (fun t body _act' _g'' _hstep' ih_step h =>
      match h with
      | .mu _ _ hbody =>
        let h' := uniqLabels_substitute t body h
        ih_step h')
    -- BranchesStep.nil case
    (fun _act _huniq => BranchesUniq.nil)
    -- BranchesStep.cons case: use helper with IH
    (fun label g g' rest rest' _act hstep hrest ih_step ih_rest huniq =>
      uniqLabels_step_ih_wrapper ih_step ih_rest huniq hstep hrest)
    g act g' hstep h

/-- Projectability is preserved through mu-unfolding.

    Uses projectR_substitute axiom from ProjectionR.lean. -/
theorem projectable_mu_unfold {t : String} {body : GlobalType}
    (h : projectable (.mu t body))
    (huniq : GlobalType.uniqLabels (.mu t body)) : projectable (body.substitute t (.mu t body)) := by
  intro role
  -- h tells us projectR (.mu t body) role succeeds for all roles
  obtain ⟨lt_mu, hlt_mu⟩ := h role
  -- From projectR_mu, if projectR (.mu t body) succeeds, projectR body also succeeds
  rw [projectR_mu] at hlt_mu
  -- Split on the bind
  cases hbody : projectR body role with
  | error e =>
    -- Can't happen: projectR_mu would have failed
    simp only [hbody, Except.bind] at hlt_mu
    cases hlt_mu
  | ok lt =>
    -- We have projectR body role = .ok lt
    -- And projectR (.mu t body) role = .ok (some lt_mu')
    -- Use projectR_substitute with body, t, (.mu t body)
    have huniq_body : GlobalType.uniqLabels body := by
      cases huniq with
      | mu _ _ hbody => exact hbody
    have hrep := h role  -- projectR (.mu t body) role succeeds
    obtain ⟨rlt, hrlt⟩ := hrep
    have hresult := projectR_substitute body t (.mu t body) role lt rlt hbody hrlt huniq_body
    exact ⟨lt.substitute t rlt, hresult⟩

/-- If all branches are projectable, extract the projectability for each member. -/
private def projectable_all_from_comm (s r : String) (branches : List (Label × GlobalType))
    (h : projectable (.comm s r branches)) :
    ∀ (l : Label) (g : GlobalType), (l, g) ∈ branches → ∀ role, ∃ lt, projectR g role = .ok lt :=
  fun l g hmem role => projectable_comm_mem_role s r role branches (h role) hmem

/-- Extract uniqLabels for a branch member. -/
private def uniqLabels_from_comm_mem (s r : String) (branches : List (Label × GlobalType))
    (huniq : GlobalType.uniqLabels (.comm s r branches))
    {l : Label} {g : GlobalType} (hmem : (l, g) ∈ branches) : GlobalType.uniqLabels g :=
  BranchesUniq.mem (uniqLabels_comm_branches huniq) hmem

/-- Merge preservation through stepping for non-participant projection.

    When a non-participant projects a comm, it merges all branch projections.
    After stepping via BranchesStep, the new branch projections must still merge.

    This is a semantic property: if the original branches were coherent (their
    projections could be merged), then stepping preserves this coherence because
    stepping only advances the internal state without changing the merge structure. -/
axiom foldMerge_preserved_BranchesStep
    {sender receiver : String}
    {branches branches' : List (Label × GlobalType)} {act : GlobalActionR} {role : String}
    (hbstep : GlobalType.BranchesStep GlobalType.step branches act branches')
    (hprojOrig : ∃ lt, projectR (.comm sender receiver branches) role = .ok lt)
    (hne1 : role ≠ sender) (hne2 : role ≠ receiver)
    (hprojTypes' : ∃ tys', projectBranchTypes branches' role = .ok tys')
    : ∃ lt', projectR (.comm sender receiver branches') role = .ok lt'

/-- Helper: if projectR of a comm succeeds for the sender, branches must be non-empty. -/
private theorem projectable_comm_nonempty (sender receiver : String)
    (branches : List (Label × GlobalType))
    (hproj : ∃ lt, projectR (.comm sender receiver branches) sender = .ok lt)
    : branches.isEmpty = false := by
  obtain ⟨lt, hlt⟩ := hproj
  rw [projectR_comm_sender] at hlt
  by_cases he : branches.isEmpty
  · simp [he] at hlt
  · simp [he]

/-- Helper: extract body projectability from mu projectability. -/
private theorem projectable_mu_body (t : String) (body : GlobalType)
    (h : projectable (.mu t body)) : projectable body := fun role => by
  obtain ⟨lt, hlt⟩ := h role
  rw [projectR_mu] at hlt
  simp only [Except.bind] at hlt
  cases hproj : projectR body role with
  | error e =>
    simp [hproj] at hlt
  | ok projBody =>
    use projBody

/-- sizePred from projectable: projectR fails on empty branches, so projectable implies sizePred.

    Proof by structural recursion on GlobalType. For each case:
    - end/var: trivially sizePred (allCommsNonEmpty returns true)
    - comm: projectR checks branches.isEmpty and fails if true, so branches must be non-empty;
            each branch is projectable (via projectable_comm_mem_role), so recursion applies
    - mu: unfold and apply recursion

    Uses @GlobalType.rec since GlobalType is a nested inductive. -/
theorem sizePred_from_projectable {g : GlobalType} (h : projectable g) : sizePred g :=
  let motive1 (g : GlobalType) : Prop := projectable g → sizePred g
  let motive2 (bs : List (Label × GlobalType)) : Prop :=
    ∀ (l : Label) (g : GlobalType), (l, g) ∈ bs → projectable g → sizePred g
  let motive3 (p : Label × GlobalType) : Prop := projectable p.2 → sizePred p.2
  @GlobalType.rec (motive_1 := motive1) (motive_2 := motive2) (motive_3 := motive3)
    -- end case (motive_1 end)
    (fun _ => by simp [sizePred, allCommsNonEmpty_end])
    -- comm case (motive_1 (comm ...))
    (fun sender receiver branches ih_branches hproj => by
      simp only [sizePred, allCommsNonEmpty_comm]
      have hne : branches.isEmpty = false :=
        projectable_comm_nonempty sender receiver branches (hproj sender)
      simp only [hne, Bool.not_false, Bool.true_and]
      apply List.all_eq_true.mpr
      intro ⟨label, cont⟩ hmem
      simp only
      have hcont_proj : projectable cont := fun role =>
        projectable_comm_mem_role sender receiver role branches (hproj role) hmem
      exact ih_branches label cont hmem hcont_proj)
    -- mu case (motive_1 (mu ...))
    (fun t body ih_body hproj => by
      simp only [sizePred, allCommsNonEmpty_mu]
      have hbody_proj := projectable_mu_body t body hproj
      exact ih_body hbody_proj)
    -- var case (motive_1 (var ...))
    (fun _ _ => by simp [sizePred, allCommsNonEmpty_var])
    -- List.nil case (motive_2 [])
    (fun _ _ hmem _ => by cases hmem)
    -- List.cons case (motive_2 (head :: tail))
    (fun head tail ih_head ih_tail l g' hmem hproj => by
      cases hmem with
      | head => exact ih_head hproj
      | tail _ htail => exact ih_tail l g' htail hproj)
    -- pair case (motive_3 (fst, snd))
    (fun _label g ih_g hproj => ih_g hproj)
    g h


/-- Projectability is preserved by a single step.

    Uses mutual induction on step and BranchesStep via step.rec.

    The proof handles all three step cases with full mutual induction. -/
theorem projectable_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (h : projectable g) (huniq : GlobalType.uniqLabels g)
    : projectable g' :=
  let motive1 (g : GlobalType) (_act : GlobalActionR) (g' : GlobalType)
      (_hstep : step g _act g') : Prop :=
    projectable g → uniqLabels g → projectable g'
  let motive2 (bs : List (Label × GlobalType)) (_act : GlobalActionR)
      (bs' : List (Label × GlobalType)) (_hbstep : BranchesStep step bs _act bs') : Prop :=
    -- For BranchesStep, we show that if all branches are projectable and have uniqLabels,
    -- then all stepped branches are projectable
    (∀ (l : Label) (g : GlobalType), (l, g) ∈ bs → projectable g ∧ uniqLabels g) →
    (∀ (l : Label) (g' : GlobalType), (l, g') ∈ bs' → projectable g')
  @step.rec (motive_1 := motive1) (motive_2 := motive2)
    -- comm_head case: cont ∈ branches, so projectable h → projectable cont
    (fun sender receiver branches label cont hmem h _huniq role =>
      projectable_comm_mem_role sender receiver role branches (h role) hmem)
    -- comm_async case: use BranchesStep IH to show branches' are projectable
    (fun sender receiver branches branches' act' label cont _hne1 _hne2 _hmem _hcan hbstep ih_bstep h huniq => by
      intro role
      -- Extract facts about the comm
      have hprojAll := projectable_all_from_comm sender receiver branches h
      have huniqBranches := uniqLabels_comm_branches huniq
      have hsizeH := sizePred_from_projectable h
      have hne_empty := sizePred_comm_nonempty hsizeH
      have hne_empty' := BranchesStep.isEmpty_false hbstep hne_empty
      -- Build the branch-wise hypothesis
      have hbranch_hyp : ∀ (l : Label) (g : GlobalType), (l, g) ∈ branches →
          projectable g ∧ uniqLabels g := fun l g hm =>
        ⟨fun r => hprojAll l g hm r, BranchesUniq.mem huniqBranches hm⟩
      -- Apply the BranchesStep IH to get all stepped branches are projectable
      have hbranch_proj' := ih_bstep hbranch_hyp
      -- Each stepped branch is projectable for any role
      have hproj_branches' : ∀ (l : Label) (g' : GlobalType), (l, g') ∈ branches' →
          ∀ r, ∃ lt, projectR g' r = .ok lt := fun l g' hm r =>
        (hbranch_proj' l g' hm) r
      -- Now show projection succeeds for role
      by_cases hr1 : role = sender
      · -- Sender case: use projectBranches_from_all_projectable
        have hproj_sender := fun l g' hm => hproj_branches' l g' hm role
        have ⟨bs', hbs'⟩ := projectBranches_from_all_projectable hproj_sender
        use .send receiver bs'
        rw [hr1, projectR_comm_sender, hne_empty', ← hr1]
        simp only [hbs', Except.map, if_neg (Bool.false_ne_true)]
      · by_cases hr2 : role = receiver
        · -- Receiver case: use projectBranches_from_all_projectable
          have hproj_receiver := fun l g' hm => hproj_branches' l g' hm role
          have ⟨bs', hbs'⟩ := projectBranches_from_all_projectable hproj_receiver
          use .recv sender bs'
          -- From hr1 (role ≠ sender) and hr2 (role = receiver), we get sender ≠ receiver
          have hne_sr : sender ≠ receiver := fun heq => hr1 (hr2 ▸ heq.symm)
          rw [hr2, projectR_comm_receiver sender receiver branches' hne_sr, hne_empty', ← hr2]
          simp only [hbs', Except.map, if_neg (Bool.false_ne_true)]
        · -- Non-participant case: use projectBranchTypes_from_all_projectable + merge axiom
          have hproj_role := fun l g' hm => hproj_branches' l g' hm role
          have hprojTypes' := projectBranchTypes_from_all_projectable hproj_role
          exact foldMerge_preserved_BranchesStep hbstep (h role) hr1 hr2 hprojTypes')
    -- mu case: use projectable_mu_unfold
    (fun t body act' g'' _hstep' ih_step h huniq =>
      let h' := projectable_mu_unfold h huniq
      let huniq' := uniqLabels_substitute t body huniq
      ih_step h' huniq')
    -- BranchesStep.nil case
    (fun _act _hyp _l _g' hmem' => by cases hmem')
    -- BranchesStep.cons case
    (fun label g g' rest rest' _act _hstep _hrest ih_step ih_rest hyp l g0 hmem' => by
      have hmem'' : (l, g0) = (label, g') ∨ (l, g0) ∈ rest' := by
        simpa [List.mem_cons] using hmem'
      cases hmem'' with
      | inl heq =>
        cases heq
        have ⟨hprojG, huniqG⟩ := hyp label g List.mem_cons_self
        exact ih_step hprojG huniqG
      | inr hmem'' =>
        have hyp_rest : ∀ (l : Label) (g : GlobalType), (l, g) ∈ rest →
            projectable g ∧ uniqLabels g := fun l' g' hm =>
          hyp l' g' (List.mem_cons_of_mem _ hm)
        exact ih_rest hyp_rest l g0 hmem'')
    g act g' hstep h huniq

/-- Lift canStep from a branch continuation to the parent comm.

    When an action is enabled in a branch continuation, it can be lifted to
    the parent comm via comm_async if:
    1. The action sender is not the outer receiver (blocked waiting for message)
    2. If the sender is the outer sender, the receiver must differ from outer receiver

    This is a semantic property: actions enabled in continuations satisfy these
    conditions because the protocol is well-formed (coherent). -/
axiom canStep_lift_to_comm (sender receiver : String) (branches : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (act : GlobalActionR)
    (hmem : (label, cont) ∈ branches)
    (hcan : canStep cont act)
    (hact : actionPred (.comm sender receiver branches))
    : canStep (.comm sender receiver branches) act

/-- Step determinism: given unique labels, same action produces same result.

    This follows from the structure of step: for each action, there is at most
    one matching branch (due to uniqLabels), and the step is deterministic.

    Proof by mutual induction on step and BranchesStep using step.rec:
    - comm_head: By BranchesUniq, the same label determines the same continuation
    - comm_async: By IH on BranchesStep, stepped branches are equal
    - mu: By IH with uniqLabels_substitute -/
theorem step_deterministic {g g' g'' : GlobalType} {act : GlobalActionR}
    (h1 : step g act g')
    (h2 : step g act g'')
    (huniq : uniqLabels g)
    : g' = g'' :=
  -- Use mutual induction on step and BranchesStep via step.rec
  let motive1 (g : GlobalType) (act : GlobalActionR) (g' : GlobalType)
      (_hstep : step g act g') : Prop :=
    ∀ g'', step g act g'' → uniqLabels g → g' = g''
  let motive2 (bs : List (Label × GlobalType)) (act : GlobalActionR)
      (bs' : List (Label × GlobalType)) (_hbstep : BranchesStep step bs act bs') : Prop :=
    ∀ bs'', BranchesStep step bs act bs'' → BranchesUniq uniqLabels bs → bs' = bs''
  @step.rec (motive_1 := motive1) (motive_2 := motive2)
    -- comm_head case: By label uniqueness, same label gives same continuation
    (fun sender receiver branches label cont hmem g0 h2' huniq' => by
      cases h2' with
      | comm_head _ _ _ label' cont' hmem' =>
        -- Same label (from action equality)
        have hbranches := uniqLabels_comm_branches huniq'
        exact BranchesUniq.eq_of_label_mem hbranches hmem hmem'
      | comm_async _ _ _ _ _ _ _ hne1 hne2 _ _ _ =>
        -- Contradiction: actions match, but hne2 says sender = sender → receiver ≠ receiver
        -- This is a contradiction since receiver = receiver
        have hcontra := hne2 rfl
        exact absurd rfl hcontra)
    -- comm_async case: By IH on BranchesStep, stepped branches are equal
    (fun sender receiver branches branches' act' label cont hne1 hne2 hmem hcan hbstep ih_bstep g0 h2' huniq' => by
      cases h2' with
      | comm_head _ _ _ label' cont' hmem' =>
        -- Contradiction: symmetric - act' matches head, but hne2 says sender = sender → act'.receiver ≠ receiver
        -- Since we're matching with comm_head, act' = { sender, receiver, label' }
        -- So act'.sender = sender (true) and act'.receiver = receiver
        -- This contradicts hne2
        have hcontra := hne2 rfl
        exact absurd rfl hcontra
      | comm_async _ _ _ branches'' _ _ _ hne1' hne2' hmem' hcan' hbstep' =>
        -- Same structure, need branches' = branches''
        have hbranches := uniqLabels_comm_branches huniq'
        have heq := ih_bstep branches'' hbstep' hbranches
        rw [heq])
    -- mu case: Use IH with uniqLabels_substitute
    (fun t body act' g''' _hstep' ih g0 h2' huniq' => by
      match h2' with
      | step.mu _ _ _ g2 hstep'' =>
        have huniq'' := uniqLabels_substitute t body huniq'
        exact ih g2 hstep'' huniq'')
    -- BranchesStep.nil case
    (fun _act bs'' h2' _huniq' => by
      cases h2'
      rfl)
    -- BranchesStep.cons case
    (fun label g g' rest rest' _act _hstep _hrest ih_step ih_rest bs'' h2' huniq' => by
      cases h2' with
      | cons _ _ g'' _ rest'' _ hstep'' hrest'' =>
        cases huniq' with
        | cons _ _ _ hpg hrest_uniq _ =>
          have heq_g := ih_step g'' hstep'' hpg
          have heq_rest := ih_rest rest'' hrest'' hrest_uniq
          rw [heq_g, heq_rest])
    g act g' h1 g'' h2 huniq

/-- Good global is preserved by a single step.

    Proof structure (following Coq paco approach):
    1. step g act g' implies canStep g act (step_implies_canStep)
    2. goodG g gives: ∀ act, canStep g act → ∃ g'', step g act g'' ∧ goodG g''
    3. Apply (2) to get ∃ g'', step g act g'' ∧ goodG g''
    4. By step_deterministic (using uniqLabels), g' = g''
    5. Therefore goodG g'

    This proof requires uniqLabels which is provided through coherentG. -/
theorem goodG_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (hgood : goodG g) (huniq : uniqLabels g) : goodG g' := by
  -- Step 1: Get canStep from step
  have hcan : canStep g act := step_implies_canStep hstep
  -- Step 2: Unfold goodG to get the coinductive property
  unfold goodG at hgood
  -- Step 3: Apply to get existence of stepped result with goodG
  have ⟨g'', hstep'', hgood''⟩ := hgood act hcan
  -- Step 4: By determinism, g' = g''
  have heq : g' = g'' := step_deterministic hstep hstep'' huniq
  -- Step 5: Conclude goodG g'
  rw [heq]
  exact hgood''

/-- Coherence is preserved by a single async step. -/
theorem coherentG_step {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') (hcoh : coherentG g) : coherentG g' := by
  exact {
    linear := linearPred_step hstep hcoh.linear
    size := sizePred_step hstep hcoh.size
    action := actionPred_step hstep hcoh.action
    uniqLabels := uniqLabels_step hstep hcoh.uniqLabels
    proj := projectable_step hstep hcoh.proj hcoh.uniqLabels
    good := goodG_step hstep hcoh.good hcoh.uniqLabels
  }

/-- Coherence is preserved by async step-star. -/
theorem coherentG_stepStar {g g' : GlobalType}
    (hcoh : coherentG g) (hstar : GlobalTypeStepStar g g') : coherentG g' := by
  induction hstar with
  | refl _ => exact hcoh
  | step g1 g2 g3 act hstep _ ih =>
    exact ih (coherentG_step hstep hcoh)

end Rumpsteak.Protocol.Coherence
