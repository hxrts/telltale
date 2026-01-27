import RumpsteakV2.Proofs.Safety.Determinism.Part1

namespace RumpsteakV2.Proofs.Safety.Determinism
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Semantics.Environment
/-! ## Diamond Property for Independent Actions

For independent actions (different sender-receiver pairs), we do have
a diamond property: they commute.
-/

/-- Two actions are independent if they involve disjoint role pairs. -/
def IndependentActions (act₁ act₂ : GlobalActionR) : Prop :=
  act₁.sender ≠ act₂.sender ∧
  act₁.sender ≠ act₂.receiver ∧
  act₁.receiver ≠ act₂.sender ∧
  act₁.receiver ≠ act₂.receiver

/-- Independent actions can't both be comm_head for the same communication.
    If act₁ = {s, r, l₁} and act₂ = {s, r, l₂}, then sender₁ = sender₂, violating independence. -/
theorem independent_not_both_head {act₁ act₂ : GlobalActionR} {s r : String}
    (hind : IndependentActions act₁ act₂)
    (h₁ : act₁.sender = s ∧ act₁.receiver = r)
    (h₂ : act₂.sender = s ∧ act₂.receiver = r) : False := by
  have hs : act₁.sender = act₂.sender := h₁.1.trans h₂.1.symm
  exact hind.1 hs

/-- IndependentActions is symmetric. -/
theorem IndependentActions.symm {act₁ act₂ : GlobalActionR}
    (h : IndependentActions act₁ act₂) : IndependentActions act₂ act₁ :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

/-- The diamond property result is symmetric in act₁/act₂.
    This allows us to prove only one direction of asymmetric cases. -/
theorem step_diamond_symm {g₁ g₂ g₃ : GlobalType} {act₁ act₂ : GlobalActionR}
    (h : step g₁ act₂ g₃ ∧ step g₂ act₁ g₃) :
    step g₂ act₁ g₃ ∧ step g₁ act₂ g₃ :=
  ⟨h.2, h.1⟩

/-- BranchesStep preserves membership: if (l, g) ∈ bs and BranchesStep bs act bs',
    then there exists g' such that step g act g' and (l, g') ∈ bs'. -/
theorem BranchesStep_mem {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    {l : Label} {g : GlobalType}
    (hbs : BranchesStep step bs act bs')
    (hmem : (l, g) ∈ bs) :
    ∃ g', step g act g' ∧ (l, g') ∈ bs' := by
  induction hbs with
  | nil => cases hmem
  | cons label head head' rest rest' _ hhead hrest ih =>
      cases hmem with
      | head =>
          -- (l, g) is the head of the list, l = label, g = head
          exact ⟨head', hhead, .head _⟩
      | tail _ hmem' =>
          -- (l, g) is in the rest
          obtain ⟨g', hstep, hmem''⟩ := ih hmem'
          exact ⟨g', hstep, .tail _ hmem''⟩

/-- Inverse of BranchesStep_mem: if (l, g') ∈ bs' after BranchesStep bs act bs',
    then there exists g such that (l, g) ∈ bs and step g act g'. -/
theorem BranchesStep_mem_inv {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    {l : Label} {g' : GlobalType}
    (hbs : BranchesStep step bs act bs')
    (hmem : (l, g') ∈ bs') :
    ∃ g, step g act g' ∧ (l, g) ∈ bs := by
  induction hbs with
  | nil => cases hmem
  | cons label head head' rest rest' _ hhead hrest ih =>
      cases hmem with
      | head =>
          exact ⟨head, hhead, .head _⟩
      | tail _ hmem' =>
          obtain ⟨g, hstep, hmem''⟩ := ih hmem'
          exact ⟨g, hstep, .tail _ hmem''⟩

/-- BranchesStep matches the length and labels of the input list. -/
theorem BranchesStep_labels {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    (hbs : BranchesStep step bs act bs') :
    bs.map Prod.fst = bs'.map Prod.fst := by
  induction hbs with
  | nil => rfl
  | cons label _ _ _ _ _ _ _ ih =>
      simp only [List.map_cons]
      rw [ih]

/-- canStep for an action on a type requires the action to be enabled somewhere in the type. -/
theorem canStep_comm_head {s r : String} {branches : List (Label × GlobalType)}
    {l : Label} {cont : GlobalType}
    (hmem : (l, cont) ∈ branches) :
    canStep (.comm s r branches) { sender := s, receiver := r, label := l } := by
  exact canStep.comm_head s r branches l cont hmem


/-- uniqueBranchLabelsBranches implies each continuation has uniqueBranchLabels. -/
theorem uniqueBranchLabelsBranches_mem {branches : List (Label × GlobalType)} {lbl : Label} {g : GlobalType}
    (huniq : uniqueBranchLabelsBranches branches = true)
    (hmem : (lbl, g) ∈ branches) :
    g.uniqueBranchLabels = true := by
  induction branches with
  | nil => cases hmem
  | cons hd tl ih =>
      simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq
      cases hmem with
      | head => exact huniq.1
      | tail _ hmem' => exact ih huniq.2 hmem'

/-- BranchesStep preserves uniqueBranchLabelsBranches. -/
theorem BranchesStep_preserves_uniqueBranchLabelsBranches {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    (huniq : uniqueBranchLabelsBranches bs = true)
    (hbs : BranchesStep step bs act bs')
    (ih : ∀ g g', g.uniqueBranchLabels = true → step g act g' → g'.uniqueBranchLabels = true) :
    uniqueBranchLabelsBranches bs' = true := by
  induction hbs with
  | nil => rfl
  | cons lbl head head' rest rest' _ hhead hrest ih_rest =>
      simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq ⊢
      constructor
      · exact ih head head' huniq.1 hhead
      · exact ih_rest huniq.2 ih

/-- BranchesStep preserves branchLabels (the list of labels doesn't change). -/
theorem BranchesStep_preserves_branchLabels {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    (hbs : BranchesStep step bs act bs') :
    branchLabels bs' = branchLabels bs := by
  induction hbs with
  | nil => rfl
  | cons lbl _ _ _ _ _ _ _ ih =>
      unfold branchLabels at *
      simp only [List.map_cons]
      rw [ih]

/-- uniqueBranchLabels is preserved by step.
    This is needed for the diamond property to maintain well-formedness.

    **Note:** This proof uses @step.rec for the nested induction. The structure
    mirrors global_step_det but with uniqueBranchLabels preservation as the goal.
    The key insight is that:
    - comm_head: continuation inherits uniqueness from branch list
    - comm_async: BranchesStep preserves labels (so Nodup is preserved) and
                  each branch continuation preserves uniqueness by IH
    - mu: substitution preserves uniqueness, then apply IH
-/
private abbrev UniqueStepMotive (g : GlobalType) (act : GlobalActionR) (g' : GlobalType)
    (_ : step g act g') : Prop :=
  -- Uniqueness-preservation motive for step recursion.
  g.uniqueBranchLabels = true → g'.uniqueBranchLabels = true

private abbrev UniqueBranchMotive (bs : List (Label × GlobalType)) (act : GlobalActionR)
    (bs' : List (Label × GlobalType)) (_ : BranchesStep step bs act bs') : Prop :=
  -- Uniqueness + label preservation for branch steps.
  uniqueBranchLabelsBranches bs = true →
    uniqueBranchLabelsBranches bs' = true ∧ branchLabels bs' = branchLabels bs

private theorem uniqueBranchLabels_preserved_comm_head
    (sender receiver : String) (branches : List (Label × GlobalType)) (label : Label) (cont : GlobalType)
    (hmem : (label, cont) ∈ branches)
    (huniq : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true) :
    cont.uniqueBranchLabels = true := by
  -- The continuation inherits uniqueness from the branch list.
  simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq
  exact uniqueBranchLabelsBranches_mem huniq.2 hmem

private theorem uniqueBranchLabels_preserved_comm_async
    (sender receiver : String) (branches branches' : List (Label × GlobalType)) (act' : GlobalActionR)
    (label : Label) (cont : GlobalType) (_hns : act'.sender ≠ receiver)
    (_hcond : act'.sender = sender → act'.receiver ≠ receiver)
    (_hmem : (label, cont) ∈ branches) (_hcan : canStep cont act')
    (hbs : BranchesStep step branches act' branches')
    (ih_bs : UniqueBranchMotive branches act' branches' hbs)
    (huniq : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true) :
    (GlobalType.comm sender receiver branches').uniqueBranchLabels = true := by
  -- BranchesStep preserves labels; uniqueness reduces to tail uniqueness.
  simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq ⊢
  obtain ⟨huniq_bs', hlabels⟩ := ih_bs huniq.2
  constructor
  · rw [hlabels]; exact huniq.1
  · exact huniq_bs'

private theorem uniqueBranchLabels_preserved_mu
    (t : String) (body : GlobalType) (act' : GlobalActionR) (g'' : GlobalType)
    (hstep : step (body.substitute t (.mu t body)) act' g'')
    (ih : UniqueStepMotive (body.substitute t (.mu t body)) act' g'' hstep)
    (huniq : (GlobalType.mu t body).uniqueBranchLabels = true) :
    g''.uniqueBranchLabels = true := by
  -- Push uniqueness through substitution, then apply IH.
  simp only [GlobalType.uniqueBranchLabels] at huniq
  have huniq_sub : (body.substitute t (GlobalType.mu t body)).uniqueBranchLabels = true :=
    GlobalType.uniqueBranchLabels_substitute body t (.mu t body) huniq huniq
  exact ih huniq_sub

private theorem uniqueBranchLabels_preserved_branches_nil
    (_act' : GlobalActionR) (_huniq : uniqueBranchLabelsBranches [] = true) :
    uniqueBranchLabelsBranches [] = true ∧ branchLabels [] = branchLabels [] := by
  -- Nil case: trivial.
  exact ⟨rfl, rfl⟩

private theorem uniqueBranchLabels_preserved_branches_cons
    (lbl : Label) (gHead gHead' : GlobalType) (restTail restTail' : List (Label × GlobalType))
    (act' : GlobalActionR) (hstep : step gHead act' gHead')
    (hbstep : BranchesStep step restTail act' restTail')
    (ih_step : UniqueStepMotive gHead act' gHead' hstep)
    (ih_bstep : UniqueBranchMotive restTail act' restTail' hbstep)
    (huniq : uniqueBranchLabelsBranches ((lbl, gHead) :: restTail) = true) :
    uniqueBranchLabelsBranches ((lbl, gHead') :: restTail') = true ∧
      branchLabels ((lbl, gHead') :: restTail') = branchLabels ((lbl, gHead) :: restTail) := by
  -- Combine head uniqueness with the tail IH and preserve labels.
  simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq ⊢
  obtain ⟨huniq_rest, hlabels_rest⟩ := ih_bstep huniq.2
  constructor
  · exact ⟨ih_step huniq.1, huniq_rest⟩
  · simpa [branchLabels] using congrArg (fun xs => lbl :: xs) hlabels_rest

/-- Unique branch labels are preserved by a single step. -/
theorem uniqueBranchLabels_preserved_by_step {g g' : GlobalType} {act : GlobalActionR}
    (huniq : g.uniqueBranchLabels = true)
    (hstep : step g act g') :
    g'.uniqueBranchLabels = true :=
  (@step.rec
    (motive_1 := UniqueStepMotive)
    (motive_2 := UniqueBranchMotive)
    uniqueBranchLabels_preserved_comm_head
    uniqueBranchLabels_preserved_comm_async
    uniqueBranchLabels_preserved_mu
    uniqueBranchLabels_preserved_branches_nil
    uniqueBranchLabels_preserved_branches_cons
    (t := hstep)) huniq

/-- Every step corresponds to a canStep. -/
theorem step_implies_canStep {g g' : GlobalType} {act : GlobalActionR}
    (h : step g act g') : canStep g act :=
  @step.rec
    (motive_1 := fun g act _ _ => canStep g act)
    (motive_2 := fun bs act _ _ => BranchesCanStep bs act)
    (fun sender receiver branches label cont hmem =>
      canStep.comm_head sender receiver branches label cont hmem)
    (fun sender receiver branches branches' act label cont hns hcond hmem hcan hbs ih_branches =>
      canStep.comm_async sender receiver branches act label cont hns hcond hmem ih_branches hcan)
    (fun t body act g' hstep ih =>
      canStep.mu t body act ih)
    (fun act => BranchesCanStep.nil act)
    (fun label g g' rest rest' act hstep hrest ih_head ih_rest =>
      BranchesCanStep.cons label g rest act ih_head ih_rest)
    (t := h)

/-- Diamond property for global type step with independent actions.
    This is the core lemma: independent actions on global types commute.

    **Proof strategy:**
    - Case analysis on h₁ and h₂
    - comm_head + comm_head: impossible (violates independence)
    - comm_head + comm_async: use BranchesStep_mem
    - comm_async + comm_head: symmetric
    - comm_async + comm_async: use mutual IH via @step.rec
    - mu + mu: use IH on unfolded body
-/
private abbrev DiamondStepMotive (act₂ : GlobalActionR) (g : GlobalType) (act₁ : GlobalActionR)
    (g₁ : GlobalType) (_ : step g act₁ g₁) : Prop :=
  -- Diamond motive for step recursion.
  g.uniqueBranchLabels = true →
    IndependentActions act₁ act₂ →
    ∀ g₂, step g act₂ g₂ →
      ∃ g₃, step g₁ act₂ g₃ ∧ step g₂ act₁ g₃ ∧ g₃.uniqueBranchLabels = true

private abbrev DiamondBranchMotive (act₂ : GlobalActionR) (bs : List (Label × GlobalType))
    (act₁ : GlobalActionR) (bs₁ : List (Label × GlobalType))
    (_ : BranchesStep step bs act₁ bs₁) : Prop :=
  -- Diamond motive for branch-step recursion.
  uniqueBranchLabelsBranches bs = true →
    IndependentActions act₁ act₂ →
    ∀ bs₂, BranchesStep step bs act₂ bs₂ →
      ∃ bs₃, BranchesStep step bs₁ act₂ bs₃ ∧
             BranchesStep step bs₂ act₁ bs₃ ∧
             uniqueBranchLabelsBranches bs₃ = true

private theorem diamond_comm_head {act₂ : GlobalActionR}
    (sender receiver : String) (branches : List (Label × GlobalType)) (label₁ : Label) (cont₁ : GlobalType)
    (hmem₁ : (label₁, cont₁) ∈ branches)
    (huniq' : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true)
    (hind' : IndependentActions { sender := sender, receiver := receiver, label := label₁ } act₂)
    (g₂' : GlobalType) (h₂' : step (.comm sender receiver branches) act₂ g₂') :
    ∃ g₃, step cont₁ act₂ g₃ ∧
      step g₂' { sender := sender, receiver := receiver, label := label₁ } g₃ ∧
      g₃.uniqueBranchLabels = true := by
  -- Head/head is impossible; head/async steps via BranchesStep_mem.
  cases h₂' with
  | comm_head _ _ _ _ _ _ =>
      exact absurd rfl hind'.1
  | comm_async _ _ _ branches' _ _ _ _ _ _ _ hbs₂ =>
      obtain ⟨cont₁', hstep_cont, hmem₁'⟩ := BranchesStep_mem hbs₂ hmem₁
      simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq'
      refine ⟨cont₁', hstep_cont, ?_, ?_⟩
      · exact step.comm_head sender receiver branches' label₁ cont₁' hmem₁'
      · exact uniqueBranchLabels_preserved_by_step (uniqueBranchLabelsBranches_mem huniq'.2 hmem₁) hstep_cont

private theorem diamond_comm_async_head {act₂ : GlobalActionR}
    (sender receiver : String) (branches branches₁ : List (Label × GlobalType)) (act₁' : GlobalActionR)
    (label₁ : Label) (cont₁ : GlobalType) (_hns₁ : act₁'.sender ≠ receiver)
    (_hcond₁ : act₁'.sender = sender → act₁'.receiver ≠ receiver)
    (_hmem₁ : (label₁, cont₁) ∈ branches) (_hcan₁ : canStep cont₁ act₁')
    (hbs₁ : BranchesStep step branches act₁' branches₁)
    (huniq' : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true)
    (_hind' : IndependentActions act₁' act₂)
    (label₂ : Label) (cont₂ : GlobalType) (hmem₂ : (label₂, cont₂) ∈ branches)
    (hact₂ : act₂ = { sender := sender, receiver := receiver, label := label₂ }) :
    ∃ g₃, step (.comm sender receiver branches₁) act₂ g₃ ∧
      step cont₂ act₁' g₃ ∧ g₃.uniqueBranchLabels = true := by
  -- Use BranchesStep_mem to find the stepped continuation in branches₁.
  obtain ⟨cont₂', hstep_cont, hmem₂'⟩ := BranchesStep_mem hbs₁ hmem₂
  simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq'
  refine ⟨cont₂', ?_, hstep_cont, ?_⟩
  · simpa [hact₂] using (step.comm_head sender receiver branches₁ label₂ cont₂' hmem₂')
  exact uniqueBranchLabels_preserved_by_step (uniqueBranchLabelsBranches_mem huniq'.2 hmem₂) hstep_cont

private theorem canStep_of_branchesStep_mem
    {bs bs' : List (Label × GlobalType)} {act : GlobalActionR}
    {label : Label} {cont : GlobalType}
    (hbs : BranchesStep step bs act bs') (hmem : (label, cont) ∈ bs) :
    canStep cont act := by
  -- Extract the step from BranchesStep, then use step_implies_canStep.
  obtain ⟨_, hstep, _⟩ := BranchesStep_mem hbs hmem
  exact step_implies_canStep hstep

private theorem comm_unique_from_branches_step {act₁' act₂ : GlobalActionR}
    (sender receiver : String) (branches branches₁ branches₃ : List (Label × GlobalType))
    (huniq' : decide (branchLabels branches).Nodup = true ∧ uniqueBranchLabelsBranches branches = true)
    (hbs₁ : BranchesStep step branches act₁' branches₁)
    (hbs₁_to_3 : BranchesStep step branches₁ act₂ branches₃)
    (huniq_bs₃ : uniqueBranchLabelsBranches branches₃ = true) :
    (GlobalType.comm sender receiver branches₃).uniqueBranchLabels = true := by
  -- Branch labels are preserved along BranchesStep; reuse the original head uniqueness.
  simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true]
  have hlabels₃ := BranchesStep_preserves_branchLabels hbs₁_to_3
  have hlabels₁ := BranchesStep_preserves_branchLabels hbs₁
  rw [hlabels₃, hlabels₁]
  exact ⟨huniq'.1, huniq_bs₃⟩

private theorem diamond_comm_async_async {act₂ : GlobalActionR}
    (sender receiver : String) (branches branches₁ : List (Label × GlobalType)) (act₁' : GlobalActionR)
    (label₁ : Label) (cont₁ : GlobalType) (hns₁ : act₁'.sender ≠ receiver)
    (hcond₁ : act₁'.sender = sender → act₁'.receiver ≠ receiver)
    (hmem₁ : (label₁, cont₁) ∈ branches) (_hcan₁ : canStep cont₁ act₁')
    (hbs₁ : BranchesStep step branches act₁' branches₁)
    (ih_bs : DiamondBranchMotive act₂ branches act₁' branches₁ hbs₁)
    (huniq' : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true)
    (hind' : IndependentActions act₁' act₂)
    (branches₂ : List (Label × GlobalType)) (label₂ : Label) (cont₂ : GlobalType)
    (hns₂ : act₂.sender ≠ receiver)
    (hcond₂ : act₂.sender = sender → act₂.receiver ≠ receiver)
    (hmem₂ : (label₂, cont₂) ∈ branches) (_hcan₂ : canStep cont₂ act₂)
    (hbs₂ : BranchesStep step branches act₂ branches₂) :
    ∃ g₃, step (.comm sender receiver branches₁) act₂ g₃ ∧
      step (.comm sender receiver branches₂) act₁' g₃ ∧ g₃.uniqueBranchLabels = true := by
  -- Use the BranchesStep diamond IH and then rewrap comm_async.
  simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true] at huniq'
  obtain ⟨branches₃, hbs₁_to_3, hbs₂_to_3, huniq_bs₃⟩ := ih_bs huniq'.2 hind' branches₂ hbs₂
  obtain ⟨cont₂', hstep_cont₂, hmem₂_in_bs₁⟩ := BranchesStep_mem hbs₁ hmem₂
  obtain ⟨cont₁', hstep_cont₁, hmem₁_in_bs₂⟩ := BranchesStep_mem hbs₂ hmem₁
  have hcan₂' : canStep cont₂' act₂ := canStep_of_branchesStep_mem hbs₁_to_3 hmem₂_in_bs₁
  have hcan₁' : canStep cont₁' act₁' := canStep_of_branchesStep_mem hbs₂_to_3 hmem₁_in_bs₂
  refine ⟨.comm sender receiver branches₃,
      step.comm_async sender receiver branches₁ branches₃ act₂ label₂ cont₂' hns₂ hcond₂ hmem₂_in_bs₁ hcan₂' hbs₁_to_3,
      step.comm_async sender receiver branches₂ branches₃ act₁' label₁ cont₁' hns₁ hcond₁ hmem₁_in_bs₂ hcan₁' hbs₂_to_3, ?_⟩
  exact comm_unique_from_branches_step sender receiver branches branches₁ branches₃
    huniq' hbs₁ hbs₁_to_3 huniq_bs₃

private theorem diamond_comm_async {act₂ : GlobalActionR}
    (sender receiver : String) (branches branches₁ : List (Label × GlobalType)) (act₁' : GlobalActionR)
    (label₁ : Label) (cont₁ : GlobalType) (hns₁ : act₁'.sender ≠ receiver)
    (hcond₁ : act₁'.sender = sender → act₁'.receiver ≠ receiver)
    (hmem₁ : (label₁, cont₁) ∈ branches) (hcan₁ : canStep cont₁ act₁')
    (hbs₁ : BranchesStep step branches act₁' branches₁)
    (ih_bs : DiamondBranchMotive act₂ branches act₁' branches₁ hbs₁)
    (huniq' : (GlobalType.comm sender receiver branches).uniqueBranchLabels = true)
    (hind' : IndependentActions act₁' act₂)
    (g₂' : GlobalType) (h₂' : step (.comm sender receiver branches) act₂ g₂') :
    ∃ g₃, step (.comm sender receiver branches₁) act₂ g₃ ∧
      step g₂' act₁' g₃ ∧ g₃.uniqueBranchLabels = true := by
  -- Dispatch on the second step constructor.
  cases h₂' with
  | comm_head sender' receiver' branches' label₂ _ hmem₂ =>
      exact diamond_comm_async_head sender receiver branches branches₁ act₁' label₁ cont₁
        hns₁ hcond₁ hmem₁ hcan₁ hbs₁ huniq' hind' label₂ g₂' hmem₂ rfl
  | comm_async sender' receiver' branches' branches₂ act₂ label₂ cont₂ hns₂ hcond₂ hmem₂ hcan₂ hbs₂ =>
      exact diamond_comm_async_async sender receiver branches branches₁ act₁' label₁ cont₁
        hns₁ hcond₁ hmem₁ hcan₁ hbs₁ ih_bs huniq' hind'
        branches₂ label₂ cont₂ hns₂ hcond₂ hmem₂ hcan₂ hbs₂

private theorem diamond_mu {act₂ : GlobalActionR}
    (t : String) (body : GlobalType) (act₁' : GlobalActionR) (g₁' : GlobalType)
    (hstep₁ : step (body.substitute t (.mu t body)) act₁' g₁')
    (ih_step : DiamondStepMotive act₂ (body.substitute t (.mu t body)) act₁' g₁' hstep₁)
    (huniq' : (GlobalType.mu t body).uniqueBranchLabels = true)
    (hind' : IndependentActions act₁' act₂) (g₂' : GlobalType)
    (h₂' : step (.mu t body) act₂ g₂') :
    ∃ g₃, step g₁' act₂ g₃ ∧ step g₂' act₁' g₃ ∧ g₃.uniqueBranchLabels = true := by
  -- Reduce to the unfolded body.
  cases h₂' with
  | mu _ _ _ g₂'' hstep₂ =>
      simp only [GlobalType.uniqueBranchLabels] at huniq'
      have huniq_sub := GlobalType.uniqueBranchLabels_substitute body t (.mu t body) huniq' huniq'
      exact ih_step huniq_sub hind' _ hstep₂

private theorem diamond_branches_nil {act₂ : GlobalActionR}
    (act₁' : GlobalActionR) (_huniq' : uniqueBranchLabelsBranches [] = true)
    (_hind' : IndependentActions act₁' act₂) (bs₂ : List (Label × GlobalType))
    (hbs₂ : BranchesStep step [] act₂ bs₂) :
    ∃ bs₃, BranchesStep step [] act₂ bs₃ ∧ BranchesStep step bs₂ act₁' bs₃ ∧
      uniqueBranchLabelsBranches bs₃ = true := by
  -- Nil branches are stable.
  cases hbs₂ with
  | nil => exact ⟨[], .nil act₂, .nil act₁', rfl⟩

private theorem diamond_branches_cons {act₂ : GlobalActionR}
    (label : Label) (head head₁ : GlobalType) (rest rest₁ : List (Label × GlobalType))
    (act₁' : GlobalActionR) (hstep : step head act₁' head₁)
    (hbs : BranchesStep step rest act₁' rest₁)
    (ih_step : DiamondStepMotive act₂ head act₁' head₁ hstep)
    (ih_bs : DiamondBranchMotive act₂ rest act₁' rest₁ hbs)
    (huniq' : uniqueBranchLabelsBranches ((label, head) :: rest) = true)
    (hind' : IndependentActions act₁' act₂) (bs₂ : List (Label × GlobalType))
    (hbs₂ : BranchesStep step ((label, head) :: rest) act₂ bs₂) :
    ∃ bs₃, BranchesStep step ((label, head₁) :: rest₁) act₂ bs₃ ∧
      BranchesStep step bs₂ act₁' bs₃ ∧ uniqueBranchLabelsBranches bs₃ = true := by
  -- Combine the head diamond and the tail diamond.
  cases hbs₂ with
  | cons _ _ head₂ _ rest₂ _ hhead₂ hrest₂ =>
      simp only [uniqueBranchLabelsBranches, Bool.and_eq_true] at huniq'
      obtain ⟨head₃, hh₁_to_h₃, hh₂_to_h₃, huniq_h₃⟩ := ih_step huniq'.1 hind' head₂ hhead₂
      obtain ⟨rest₃, hr₁_to_r₃, hr₂_to_r₃, huniq_r₃⟩ := ih_bs huniq'.2 hind' rest₂ hrest₂
      refine ⟨(label, head₃) :: rest₃,
        .cons label head₁ head₃ rest₁ rest₃ act₂ hh₁_to_h₃ hr₁_to_r₃,
        .cons label head₂ head₃ rest₂ rest₃ act₁' hh₂_to_h₃ hr₂_to_r₃, ?_⟩
      simp only [uniqueBranchLabelsBranches, Bool.and_eq_true]
      exact ⟨huniq_h₃, huniq_r₃⟩

/-- Independent actions form a diamond under unique branch labels. -/
theorem step_diamond_independent {g g₁ g₂ : GlobalType} {act₁ act₂ : GlobalActionR}
    (hind : IndependentActions act₁ act₂)
    (huniq : g.uniqueBranchLabels = true)
    (h₁ : step g act₁ g₁)
    (h₂ : step g act₂ g₂) :
    ∃ g₃, step g₁ act₂ g₃ ∧ step g₂ act₁ g₃ ∧ g₃.uniqueBranchLabels = true :=
  (@step.rec
    (motive_1 := DiamondStepMotive act₂)
    (motive_2 := DiamondBranchMotive act₂)
    diamond_comm_head
    diamond_comm_async
    diamond_mu
    diamond_branches_nil
    diamond_branches_cons
    (t := h₁)) huniq hind g₂ h₂

/-- Diamond property for independent actions.

If two independent actions are both enabled, they commute:
taking them in either order reaches the same final configuration.

**Proof strategy:**
1. Use step_diamond_independent to get the common global type g₃
2. Construct c₃ with global type g₃ and environment c.env
3. Show both step paths work with uniqueBranchLabels preserved
-/
theorem diamond_independent {c c₁ c₂ : Configuration} {act₁ act₂ : GlobalActionR}
    (hind : IndependentActions act₁ act₂)
    (h₁ : ConfigStep c c₁ act₁)
    (h₂ : ConfigStep c c₂ act₂) :
    ∃ c₃, ConfigStep c₁ c₃ act₂ ∧ ConfigStep c₂ c₃ act₁ := by
  obtain ⟨huniq₁, hstep₁, henv₁⟩ := h₁
  obtain ⟨_huniq₂, hstep₂, henv₂⟩ := h₂
  -- Use the global-level diamond lemma
  obtain ⟨g₃, hg₁_to_g₃, hg₂_to_g₃, huniq₃⟩ := step_diamond_independent hind huniq₁ hstep₁ hstep₂
  -- Get uniqueBranchLabels for intermediate states
  have huniq_g₁ := uniqueBranchLabels_preserved_by_step huniq₁ hstep₁
  have huniq_g₂ := uniqueBranchLabels_preserved_by_step huniq₁ hstep₂
  -- Construct the common configuration
  let c₃ : Configuration := ⟨g₃, c.env⟩
  use c₃
  constructor
  · -- ConfigStep c₁ c₃ act₂
    exact ⟨huniq_g₁, hg₁_to_g₃, henv₁.symm⟩
  · -- ConfigStep c₂ c₃ act₁
    exact ⟨huniq_g₂, hg₂_to_g₃, henv₂.symm⟩

/-! ## Claims Bundle -/

/-- Claims bundle for determinism. -/
structure Claims where
  /-- Global step determinism (requires uniqueBranchLabels). -/
  global_step_det : ∀ {g g₁ g₂ : GlobalType} {act : GlobalActionR},
      g.uniqueBranchLabels = true → step g act g₁ → step g act g₂ → g₁ = g₂
  /-- Environment step determinism. -/
  env_step_det : ∀ {env env₁ env₂ : EnvConfig} {act : EnvAction},
      EnvConfigStep env act env₁ → EnvConfigStep env act env₂ → env₁ = env₂
  /-- Configuration step determinism. -/
  config_step_det : ∀ {c c₁ c₂ : Configuration} {act : GlobalActionR},
      ConfigStep c c₁ act → ConfigStep c c₂ act → c₁ = c₂
  /-- Diamond property for independent actions. -/
  diamond_independent : ∀ {c c₁ c₂ : Configuration} {act₁ act₂ : GlobalActionR},
      IndependentActions act₁ act₂ →
      ConfigStep c c₁ act₁ → ConfigStep c c₂ act₂ →
      ∃ c₃, ConfigStep c₁ c₃ act₂ ∧ ConfigStep c₂ c₃ act₁

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  -- Package determinism theorems.
  global_step_det := global_step_det
  env_step_det := env_step_det
  config_step_det := config_step_det
  diamond_independent := diamond_independent

end RumpsteakV2.Proofs.Safety.Determinism
