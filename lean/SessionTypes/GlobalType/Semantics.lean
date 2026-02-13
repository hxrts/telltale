import SessionTypes.GlobalType.Core

set_option linter.dupNamespace false

/-! # SessionTypes.GlobalType.Semantics

Actions, step semantics, wellFormed predicate, and canStep-implies-step theorems.
-/

/-
The Problem. Global types need operational semantics defining how protocols evolve
through communication steps. The semantics must handle asynchrony (actions can be
delayed past unrelated communications) and recursion (mu-unfolding).

Solution Structure. Defines `GlobalType.wellFormed` combining allVarsBound,
allCommsNonEmpty, noSelfComm, and isProductive. `GlobalActionR` represents actions
with sender, receiver, and label. `canStep` is an inductive predicate for enabledness
with cases for immediate communication, async permutation, and mu-unfolding.
`BranchesStep` handles branch-wise stepping.
-/

namespace SessionTypes.GlobalType
/-! ## Actions and Step Semantics -/

/-- Well-formedness predicate for global types. -/
def GlobalType.wellFormed (g : GlobalType) : Bool :=
  g.allVarsBound && g.allCommsNonEmpty && g.noSelfComm && g.isProductive

/-- Global action with payload label (sender, receiver, label). -/
structure GlobalActionR where
  sender : String
  receiver : String
  label : Label
  deriving Repr, DecidableEq, Inhabited

mutual
  /-- Global enabledness: an action is available in the global type. -/
  inductive canStep : GlobalType → GlobalActionR → Prop where
    | comm_head (sender receiver : String) (branches : List (Label × GlobalType))
        (label : Label) (cont : GlobalType) :
        (label, cont) ∈ branches →
        canStep (.comm sender receiver branches) { sender := sender, receiver := receiver, label := label }
    | comm_async (sender receiver : String) (branches : List (Label × GlobalType))
        (act : GlobalActionR) (label : Label) (cont : GlobalType) :
        act.sender ≠ receiver →
        (act.sender = sender → act.receiver ≠ receiver) →
        (label, cont) ∈ branches →
        BranchesCanStep branches act →
        canStep cont act →
        canStep (.comm sender receiver branches) act
    | mu (t : String) (body : GlobalType) (act : GlobalActionR) :
        canStep (body.substitute t (.mu t body)) act →
        canStep (.mu t body) act

  /-- Branch-wise enabledness: every branch can step with act. -/
  inductive BranchesCanStep : List (Label × GlobalType) → GlobalActionR → Prop where
    | nil (act : GlobalActionR) : BranchesCanStep [] act
    | cons (label : Label) (g : GlobalType) (rest : List (Label × GlobalType)) (act : GlobalActionR) :
        canStep g act →
        BranchesCanStep rest act →
        BranchesCanStep ((label, g) :: rest) act
end

/-! ## Branch-Wise and Global Step Relations -/

/-- Branch-wise step for async commutation. -/
inductive BranchesStep (stepFn : GlobalType → GlobalActionR → GlobalType → Prop) :
    List (Label × GlobalType) → GlobalActionR → List (Label × GlobalType) → Prop where
  | nil (act : GlobalActionR) : BranchesStep stepFn [] act []
  | cons (label : Label) (g g' : GlobalType) (rest rest' : List (Label × GlobalType))
      (act : GlobalActionR) :
      stepFn g act g' →
      BranchesStep stepFn rest act rest' →
      BranchesStep stepFn ((label, g) :: rest) act ((label, g') :: rest')

/-- Global async step relation (allows skipping unrelated prefixes). -/
inductive step : GlobalType → GlobalActionR → GlobalType → Prop where
  | comm_head (sender receiver : String) (branches : List (Label × GlobalType))
      (label : Label) (cont : GlobalType) :
      (label, cont) ∈ branches →
      step (.comm sender receiver branches) { sender := sender, receiver := receiver, label := label } cont
  | comm_async (sender receiver : String) (branches branches' : List (Label × GlobalType))
      (act : GlobalActionR) (label : Label) (cont : GlobalType) :
      act.sender ≠ receiver →
      (act.sender = sender → act.receiver ≠ receiver) →
      (label, cont) ∈ branches →
      canStep cont act →
      BranchesStep step branches act branches' →
      step (.comm sender receiver branches) act (.comm sender receiver branches')
  | mu (t : String) (body : GlobalType) (act : GlobalActionR) (g' : GlobalType) :
      step (body.substitute t (.mu t body)) act g' →
      step (.mu t body) act g'

/-! ## canStep implies step

This connects the enabledness predicate to the step relation. -/

/-- If canStep g act holds via comm_head, then step g act cont for the continuation.

This specialized lemma handles the synchronous case directly. -/
theorem canStep_comm_head_implies_step (sender receiver : String)
    (branches : List (Label × GlobalType)) (label : Label) (cont : GlobalType)
    (hmem : (label, cont) ∈ branches) :
    step (.comm sender receiver branches) { sender, receiver, label } cont :=
  step.comm_head sender receiver branches label cont hmem

/-- Predicate: canStep derivation is "synchronous" (no async commutation).

This characterizes canStep derivations that arise from ReachesComm:
only comm_head at the base, wrapped by mu unfoldings. -/
inductive SyncCanStep : GlobalType → GlobalActionR → Prop where
  | comm_head (sender receiver : String) (branches : List (Label × GlobalType))
      (label : Label) (cont : GlobalType) :
      (label, cont) ∈ branches →
      SyncCanStep (.comm sender receiver branches) { sender, receiver, label }
  | mu (t : String) (body : GlobalType) (act : GlobalActionR) :
      SyncCanStep (body.substitute t (.mu t body)) act →
      SyncCanStep (.mu t body) act

/-- SyncCanStep implies canStep. -/
theorem SyncCanStep.toCanStep {g : GlobalType} {act : GlobalActionR}
    (h : SyncCanStep g act) : canStep g act := by
  induction h with
  | comm_head sender receiver branches label cont hmem =>
      exact canStep.comm_head sender receiver branches label cont hmem
  | mu t body act _ ih =>
      exact canStep.mu t body act ih

/-- SyncCanStep implies step (no async case needed).

This is the specialized version for derivations from ReachesComm. -/
theorem syncCanStep_implies_step (g : GlobalType) (act : GlobalActionR)
    (hcan : SyncCanStep g act) :
    ∃ g', step g act g' := by
  induction hcan with
  | comm_head sender receiver branches label cont hmem =>
      -- Head case: step to the continuation directly.
      exact ⟨cont, step.comm_head sender receiver branches label cont hmem⟩
  | mu t body act _ ih =>
      -- Mu case: step the unfolded body.
      have ⟨g', hstep⟩ := ih
      exact ⟨g', step.mu t body act g' hstep⟩

/-! ## canStep implies step (mutual with BranchesCanStep) -/

/-- If canStep g act, then there exists g' such that step g act g'. -/
theorem canStep_implies_step (g : GlobalType) (act : GlobalActionR)
    (hcan : canStep g act) :
    ∃ g', step g act g' := by
  refine (canStep.rec
    (motive_1 := fun g act _ => ∃ g', step g act g')
    (motive_2 := fun branches act _ => ∃ branches', BranchesStep step branches act branches')
    ?comm_head ?comm_async ?mu ?nil ?cons hcan)
  · intro sender receiver branches label cont hmem
    exact ⟨cont, step.comm_head sender receiver branches label cont hmem⟩
  · intro sender receiver branches act label cont hns hsr hmem _hbranches hcan_cont ih_branches _ih_cont
    have ⟨branches', hbstep⟩ := ih_branches
    exact ⟨.comm sender receiver branches',
      step.comm_async sender receiver branches branches' act label cont hns hsr hmem hcan_cont hbstep⟩
  · intro t body act _hcan_unf ih
    have ⟨g', hstep⟩ := ih
    exact ⟨g', step.mu t body act g' hstep⟩
  · intro act
    exact ⟨[], BranchesStep.nil act⟩
  · intro label g rest act _hcan_head _hcan_rest ih_head ih_rest
    have ⟨g', hstep⟩ := ih_head
    have ⟨rest', hrest_step⟩ := ih_rest
    exact ⟨(label, g') :: rest',
      BranchesStep.cons label g g' rest rest' act hstep hrest_step⟩

/-- If every branch can step with act, then branches can step in lockstep. -/
theorem branchesCanStep_implies_branchesStep
    (branches : List (Label × GlobalType)) (act : GlobalActionR)
    (hcan : BranchesCanStep branches act) :
    ∃ branches', BranchesStep step branches act branches' := by
  refine (BranchesCanStep.rec
    (motive_1 := fun g act _ => ∃ g', step g act g')
    (motive_2 := fun branches act _ => ∃ branches', BranchesStep step branches act branches')
    ?comm_head ?comm_async ?mu ?nil ?cons hcan)
  · intro sender receiver branches label cont hmem
    exact ⟨cont, step.comm_head sender receiver branches label cont hmem⟩
  · intro sender receiver branches act label cont hns hsr hmem _hbranches hcan_cont ih_branches _ih_cont
    have ⟨branches', hbstep⟩ := ih_branches
    exact ⟨.comm sender receiver branches',
      step.comm_async sender receiver branches branches' act label cont hns hsr hmem hcan_cont hbstep⟩
  · intro t body act _hcan_unf ih
    have ⟨g', hstep⟩ := ih
    exact ⟨g', step.mu t body act g' hstep⟩
  · intro act
    exact ⟨[], BranchesStep.nil act⟩
  · intro label g rest act _hcan_head _hcan_rest ih_head ih_rest
    have ⟨g', hstep⟩ := ih_head
    have ⟨rest', hrest_step⟩ := ih_rest
    exact ⟨(label, g') :: rest',
      BranchesStep.cons label g g' rest rest' act hstep hrest_step⟩

/-! ## Helper lemmas for eraseDups membership

These use well-founded recursion on list length since `eraseDups_cons` expands to
use `filter`, which shrinks the list. -/

/-- Helper for mem_of_mem_eraseDups using termination_by. -/
private def mem_of_mem_eraseDups_aux {α : Type*} [BEq α] (a : α) (l : List α)
    (h : a ∈ l.eraseDups) : a ∈ l :=
  match l with
  | [] => by simp [List.eraseDups] at h
  | x :: xs => by
      rw [List.eraseDups_cons] at h
      simp only [List.mem_cons] at h ⊢
      cases h with
      | inl hax => left; exact hax
      | inr hrest =>
          right
          have := mem_of_mem_eraseDups_aux a (xs.filter (fun b => !b == x)) hrest
          exact List.mem_filter.mp this |>.1
termination_by l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ xs)

/-- Elements of eraseDups are elements of the original list. -/
theorem mem_of_mem_eraseDups {a : String} {l : List String}
    (h : a ∈ l.eraseDups) : a ∈ l :=
  mem_of_mem_eraseDups_aux a l h

/-! ## eraseDups Membership: Forward Direction -/

/-- Helper for mem_eraseDups_of_mem using termination_by. -/
private def mem_eraseDups_of_mem_aux {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) (l : List α) (h : a ∈ l) : a ∈ l.eraseDups :=
  match l with
  | [] => by simp at h
  | x :: xs => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons] at h ⊢
      cases h with
      | inl hax =>
          left; exact hax
      | inr hxs =>
          by_cases heq : a = x
          · left; exact heq
          · right
            have hfilter : a ∈ xs.filter (fun b => !b == x) := by
              rw [List.mem_filter]
              constructor
              · exact hxs
              · simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
                exact heq
            exact mem_eraseDups_of_mem_aux a (xs.filter (fun b => !b == x)) hfilter
termination_by l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ xs)

/-- Elements of the original list are in eraseDups. -/
theorem mem_eraseDups_of_mem {a : String} {l : List String}
    (h : a ∈ l) : a ∈ l.eraseDups :=
  mem_eraseDups_of_mem_aux a l h

/-! ## eraseDups Nodup Construction -/

/-- Helper for nodup_eraseDups using termination_by. -/
private def nodup_eraseDups_aux {α : Type*} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup :=
  match l with
  | [] => by simp [List.eraseDups, List.Nodup]
  | x :: xs => by
      rw [List.eraseDups_cons]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        have hfilt : x ∈ xs.filter (fun b => !b == x) := mem_of_mem_eraseDups_aux x _ hmem
        rw [List.mem_filter] at hfilt
        have heq : (!x == x) = false := by simp
        rw [heq] at hfilt
        exact Bool.false_ne_true hfilt.2
      · exact nodup_eraseDups_aux (xs.filter (fun b => !b == x))
termination_by l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ xs)

/-- eraseDups produces a list with no duplicates. -/
theorem nodup_eraseDups {α : Type*} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup :=
  nodup_eraseDups_aux l

/-! ## roles_nodup Derivation -/

/-- GlobalType.roles always produces a Nodup list. -/
def GlobalType.roles_nodup : (g : GlobalType) → g.roles.Nodup
  | .end => List.Pairwise.nil
  | .var _ => List.Pairwise.nil
  | .mu _ body => GlobalType.roles_nodup body
  | .comm _ _ _ => nodup_eraseDups _
  | .delegate _ _ _ _ _ => nodup_eraseDups _

/-! ## Substitution preserves role containment

These lemmas show that substituting a mu-type for its variable doesn't add new roles. -/

mutual
  private theorem substitute_roles_subset_comm (sender receiver : String)
      (branches : List (Label × GlobalType)) (t : String) (repl : GlobalType) :
      ∀ p, p ∈ ((GlobalType.comm sender receiver branches).substitute t repl).roles →
        p ∈ (GlobalType.comm sender receiver branches).roles ∨ p ∈ repl.roles := by
    -- Comm case: split into head roles and branch roles.
    intro p hp
    simp only [GlobalType.substitute, GlobalType.roles] at hp ⊢
    have hp' := mem_of_mem_eraseDups hp
    simp only [List.mem_append] at hp'
    cases hp' with
    | inl hsr =>
        left
        exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inl hsr))
    | inr hbranches =>
        have ih := substituteBranches_roles_subset branches t repl p hbranches
        cases ih with
        | inl horiginal =>
            left
            exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inr horiginal))
        | inr hrepl => right; exact hrepl

  /-- Substitution can only introduce roles from the replacement type. -/
  theorem substitute_roles_subset (g : GlobalType) (t : String) (repl : GlobalType) :
      ∀ p, p ∈ (g.substitute t repl).roles → p ∈ g.roles ∨ p ∈ repl.roles :=
    match g with
    | .end => fun _ hp => by simp [GlobalType.substitute, GlobalType.roles] at hp
    | .var s => fun p hp => by
        simp only [GlobalType.substitute] at hp
        split at hp
        · right; exact hp
        · simp [GlobalType.roles] at hp
    | .mu s inner => fun p hp => by
        simp only [GlobalType.substitute, GlobalType.roles] at hp ⊢
        split at hp
        · left; exact hp
        · have ih := substitute_roles_subset inner t repl p hp
          cases ih with
          | inl hl => left; exact hl
          | inr hr => right; exact hr
    | .comm sender receiver branches => fun p hp => by
        exact substitute_roles_subset_comm sender receiver branches t repl p hp
    | .delegate delegator delegatee sid role cont => fun p hp => by
        simp only [GlobalType.substitute, GlobalType.roles] at hp ⊢
        have hp' := mem_of_mem_eraseDups hp
        simp only [List.mem_append] at hp'
        cases hp' with
        | inl hpq =>
            left
            exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inl hpq))
        | inr hcont =>
            have ih := substitute_roles_subset cont t repl p hcont
            cases ih with
            | inl horiginal =>
                left
                exact mem_eraseDups_of_mem (List.mem_append.mpr (Or.inr horiginal))
            | inr hrepl => right; exact hrepl

  /-- Branch substitution preserves role containment. -/
  theorem substituteBranches_roles_subset (branches : List (Label × GlobalType))
      (t : String) (repl : GlobalType) :
      ∀ p, p ∈ rolesOfBranches (substituteBranches branches t repl) →
           p ∈ rolesOfBranches branches ∨ p ∈ repl.roles :=
    match branches with
    | [] => fun _ hp => by simp [substituteBranches, rolesOfBranches] at hp
    | (label, cont) :: rest => fun p hp => by
        simp only [substituteBranches, rolesOfBranches, List.mem_append] at hp ⊢
        cases hp with
        | inl hl =>
            have ih := substitute_roles_subset cont t repl p hl
            cases ih with
            | inl hcont => left; left; exact hcont
            | inr hrepl => right; exact hrepl
        | inr hr =>
            have ih := substituteBranches_roles_subset rest t repl p hr
            cases ih with
            | inl hrest => left; right; exact hrest
            | inr hrepl => right; exact hrepl
end

/-- Substituting mu t body for var t in body doesn't add new roles. -/
theorem substitute_mu_roles_subset (body : GlobalType) (t : String) :
    ∀ p, p ∈ (body.substitute t (.mu t body)).roles → p ∈ body.roles := by
  intro p hp
  have h := substitute_roles_subset body t (.mu t body) p hp
  cases h with
  | inl hl => exact hl
  | inr hr =>
      simp only [GlobalType.roles] at hr
      exact hr

end SessionTypes.GlobalType
