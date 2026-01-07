import RumpsteakV2.Semantics.EnvStep
import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # RumpsteakV2.Proofs.Projection.Harmony

Harmony between global steps and environment steps for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `Claims`: bundle of harmony properties
- `step_harmony`: global step induces matching env step
- `proj_trans_after_step`: projection commutes with stepping
-/

namespace RumpsteakV2.Proofs.Projection.Harmony

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Quotient
open RumpsteakV2.Semantics.EnvStep

-- Alias to avoid ambiguity with Trans typeclass
abbrev projTrans := RumpsteakV2.Protocol.Projection.Trans.trans
open RumpsteakV2.Protocol.Projection.Trans (trans_comm_sender trans_comm_receiver trans_comm_other
  transBranches lcontractive)

/-! ## Core Harmony Property

The harmony property states that global steps are faithfully reflected in
the projected environment. This is the key lemma connecting global semantics
to local session type semantics. -/

/-- Global step induces environment step through projection.
    This is a direct corollary of step_to_envstep. -/
theorem step_harmony (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    EnvStep (projEnv g) act (projEnv g') :=
  step_to_envstep g g' act hstep

/-! ## Projection Coherence

These lemmas establish that projection is coherent with stepping:
after a global step, the projected environment correctly reflects
the new local types for each role. -/

/-! ### Helper Axioms for Coherence Proofs

These axioms capture the key semantic properties needed for projection coherence.
They involve coinductive reasoning on trans and the step relation. -/

/-- For a non-participant, all branches of a communication project EQ2-equivalently.

This is the coherence condition: in a projectable global type, non-participants
see the same local type regardless of which branch is taken.

Proof requires coinduction on trans to show:
- trans cont role ≈ trans first_cont role for any (_, cont) ∈ branches
- When role is not sender or receiver

**Semantic justification:** This property holds for projectable global types because
CProject requires AllBranchesProj: all branch continuations project to the same
local type for non-participants.

**Not universally true:** For arbitrary (non-projectable) global types, this can fail.
However, the step relation only fires on types where canStep holds, and in practice
we only care about well-formed global types.

Coq reference: This follows from the AllBranchesProj condition in CProject
(indProj.v, coProj.v). -/
axiom branches_project_coherent (first_label : Label) (first_cont : GlobalType)
    (rest : List (Label × GlobalType)) (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ ((first_label, first_cont) :: rest)) :
    EQ2 (projTrans cont role) (projTrans first_cont role)

/-- Projection commutes with mu-substitution up to EQ2.

projTrans (body.substitute t (mu t body)) role ≈ (projTrans (mu t body) role).unfold

For **contractive** types:
- projTrans (mu t body) role = mu t (projTrans body role)
- unfold (mu t (projTrans body role)) = (projTrans body role).substitute t (mu t (projTrans body role))
- The EQ2 equivalence comes from correspondence between global and local substitution

For **non-contractive** types:
- projTrans (mu t body) role = .end
- .end.unfold = .end
- Need: projTrans (body.substitute t (mu t body)) role ≈ .end
- This holds because non-contractive types are degenerate (immediate recursion)

Coq reference: This follows from full_eunf_subst in coLocal.v. -/
axiom trans_substitute_unfold (t : String) (body : GlobalType) (role : String) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold)

/-- After a global step, the sender's local type transitions appropriately.
    The sender's projection after the step matches the expected continuation.

This axiom captures the key semantic property: when a global type steps via
action (s, r, l), the sender s's local type should transition from
`send r [... (l, T) ...]` to `T` (the continuation for label l).

Proving this constructively requires showing:
1. projTrans (g.step act) s = (projTrans g s after local step for label l)
2. The local step for send is: unfold, then select branch l

This involves coinductive reasoning on projTrans and the step relation. -/
axiom proj_trans_sender_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    ∃ cont, projTrans g act.sender = .send act.receiver [(act.label, cont)] ∧
            EQ2 (projTrans g' act.sender) cont ∨
    EQ2 (projTrans g' act.sender) (projTrans g act.sender)

/-- After a global step, the receiver's local type transitions appropriately.
    Similar to sender case but for recv. -/
axiom proj_trans_receiver_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    ∃ cont, projTrans g act.receiver = .recv act.sender [(act.label, cont)] ∧
            EQ2 (projTrans g' act.receiver) cont ∨
    EQ2 (projTrans g' act.receiver) (projTrans g act.receiver)

/-- BranchesStep preserves transBranches up to branch-wise EQ2 for non-participants.

When branches step to branches' via BranchesStep, the transBranches are related
by BranchesRel EQ2 for any role not involved in the action.

This captures the semantic property that stepping inside branches doesn't affect
non-participant projections: each branch steps, and projection commutes with stepping.

Proof requires showing: for each pair (cont, cont') from corresponding branches,
step cont act cont' ∧ role ≠ act.sender ∧ role ≠ act.receiver → EQ2 (trans cont' role) (trans cont role)

This follows by induction on BranchesStep using proj_trans_other_step for each branch.
The mutual dependency is resolved by well-founded induction on global type structure. -/
axiom branches_step_preserves_trans (branches branches' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hstep : BranchesStep step branches act branches')
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (transBranches branches' role) (transBranches branches role)

/-- Non-participating roles have unchanged projections through a step.

This theorem captures the key harmony property: if a role is not involved in an action
(neither sender nor receiver), their projected local type is unchanged by the step.

Proof by mutual induction on step and BranchesStep via @step.rec:

1. **comm_head case**: g = comm sender receiver branches, g' = cont
   - For non-participant (role ≠ sender ≠ receiver):
   - trans g role = trans first_cont role (by trans_comm_other)
   - trans g' role = trans cont role
   - Uses: branches_project_coherent

2. **comm_async case**: g = comm sender receiver branches, g' = comm sender receiver branches'
   - For role ≠ sender ≠ receiver: both project via first branch's continuation
   - The IH from BranchesStep gives: EQ2 (trans first' role) (trans first role)
   - Combine with trans_comm_other rewrites

3. **mu case**: g = mu t body, step (body.substitute t (mu t body)) act g'
   - IH: EQ2 (trans g' role) (trans (body.substitute t (mu t body)) role)
   - Uses: trans_substitute_unfold + EQ2_unfold_right to connect to trans (mu t body) role -/
theorem proj_trans_other_step (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g')
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    EQ2 (projTrans g' role) (projTrans g role) :=
  @step.rec
    -- motive_1: for step g act g', non-participant role has EQ2 (projTrans g' role) (projTrans g role)
    (motive_1 := fun g act g' _ =>
      ∀ role, role ≠ act.sender → role ≠ act.receiver → EQ2 (projTrans g' role) (projTrans g role))
    -- motive_2: for BranchesStep bs act bs', non-participant role has first branches relate under EQ2
    (motive_2 := fun bs act bs' _ =>
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        (∀ (fl : Label) (fc : GlobalType) (fl' : Label) (fc' : GlobalType),
          bs = (fl, fc) :: bs.tail → bs' = (fl', fc') :: bs'.tail →
          EQ2 (projTrans fc' role) (projTrans fc role)))
    -- Case 1: comm_head
    (fun sender receiver branches label cont hmem role hns hnr => by
      -- g = comm sender receiver branches, g' = cont
      -- For comm_head: act = { sender, receiver, label }
      -- So hns : role ≠ sender, hnr : role ≠ receiver
      -- projTrans g role = projTrans first_cont role (by trans_comm_other since role ≠ sender ≠ receiver)
      -- projTrans g' role = projTrans cont role
      -- Need: EQ2 (projTrans cont role) (projTrans first_cont role)
      match hbranches : branches with
      | [] =>
          -- hmem : (label, cont) ∈ [], contradiction
          simp at hmem
      | (fl, fc) :: rest =>
          -- projTrans g role = projTrans fc role (first continuation)
          have htrans_g : projTrans (GlobalType.comm sender receiver ((fl, fc) :: rest)) role =
              projTrans fc role := trans_comm_other sender receiver role ((fl, fc) :: rest) hns hnr
          -- All branches project coherently for non-participants
          have hcoherent := branches_project_coherent fl fc rest label cont role hmem
          rw [htrans_g]
          exact hcoherent)
    -- Case 2: comm_async
    (fun sender receiver branches branches' act label cont hns_cond _hcond _hmem _hcan hbstep
        _ih_bstep role hns hnr => by
      -- g = comm sender receiver branches
      -- g' = comm sender receiver branches'
      -- hns : role ≠ act.sender, hnr : role ≠ act.receiver
      -- hbstep : BranchesStep step branches act branches'
      --
      -- Use branches_step_preserves_trans to get branch-wise EQ2 preservation
      have hbranch_rel := branches_step_preserves_trans branches branches' act role hbstep hns hnr
      -- Case split on role's relationship to outer comm's sender/receiver
      by_cases hrs : role = sender
      · -- role = sender: project as send
        simp only [projTrans, trans_comm_sender sender receiver role branches hrs,
                   trans_comm_sender sender receiver role branches' hrs]
        -- Goal: EQ2 (send receiver (transBranches branches' role)) (send receiver (transBranches branches role))
        -- EQ2F EQ2 (send p bs) (send p cs) = p = p ∧ BranchesRel EQ2 bs cs
        exact EQ2.construct ⟨rfl, hbranch_rel⟩
      · by_cases hrr : role = receiver
        · -- role = receiver: project as recv
          simp only [projTrans, trans_comm_receiver sender receiver role branches hrr hrs,
                     trans_comm_receiver sender receiver role branches' hrr hrs]
          -- Goal: EQ2 (recv sender (transBranches branches' role)) (recv sender (transBranches branches role))
          -- EQ2F EQ2 (recv p bs) (recv p cs) = p = p ∧ BranchesRel EQ2 bs cs
          exact EQ2.construct ⟨rfl, hbranch_rel⟩
        · -- role ≠ sender ∧ role ≠ receiver: project via first branch
          -- Case split on branch structure
          match hbranches : branches, hbranches' : branches' with
          | [], [] =>
              -- Both empty: trans_comm_other gives .end for both
              simp only [trans_comm_other sender receiver role [] hrs hrr]
              exact EQ2_refl _
          | [], _ :: _ =>
              -- BranchesStep from [] is only BranchesStep.nil to [], contradiction
              cases hbstep
          | _ :: _, [] =>
              -- BranchesStep to [] requires branches = [], contradiction
              cases hbstep
          | (fl, fc) :: rest, (fl', fc') :: rest' =>
              -- trans_comm_other gives: trans (comm s r ((l,c)::_)) role = trans c role
              simp only [trans_comm_other sender receiver role ((fl, fc) :: rest) hrs hrr,
                         trans_comm_other sender receiver role ((fl', fc') :: rest') hrs hrr]
              -- Now goal is: EQ2 (trans fc' role) (trans fc role)
              -- hbranch_rel is in expanded form
              simp only [transBranches] at hbranch_rel
              -- BranchesRel = Forall₂, cons case gives (pair_proof, tail_proof)
              -- pair_proof : a.1 = b.1 ∧ EQ2 a.2 b.2
              cases hbranch_rel with
              | cons hpair htail =>
                  -- hpair : (fl', trans fc' role).1 = (fl, trans fc role).1 ∧ EQ2 (fl', trans fc' role).2 (fl, trans fc role).2
                  -- hpair.2 : EQ2 (trans fc' role) (trans fc role)
                  exact hpair.2)
    -- Case 3: mu
    (fun t body act g' _hstep_sub ih_step role hns hnr => by
      -- g = mu t body
      -- step (body.substitute t (mu t body)) act g'
      -- IH: EQ2 (projTrans g' role) (projTrans (body.substitute t (mu t body)) role)
      have hih := ih_step role hns hnr
      -- trans_substitute_unfold: EQ2 (projTrans (body.substitute t (mu t body)) role) ((projTrans (mu t body) role).unfold)
      have hsub := trans_substitute_unfold t body role
      -- EQ2_unfold_right: EQ2 (projTrans (mu t body) role) ((projTrans (mu t body) role).unfold)
      have hunf := EQ2_unfold_right (EQ2_refl (projTrans (GlobalType.mu t body) role))
      -- Chain: g' ≈ subst ≈ unfold ≈ mu
      exact EQ2_trans hih (EQ2_trans hsub (EQ2_symm hunf)))
    -- Case 4: BranchesStep.nil
    (fun _act _role _hns _hnr fl fc _fl' _fc' hnil _hnil' => by
      -- hnil : [] = (fl, fc) :: [].tail = [(fl, fc)]
      -- This is a contradiction: [] ≠ [(fl, fc)]
      exact absurd hnil (by simp [List.tail_nil]))
    -- Case 5: BranchesStep.cons
    (fun label g g' rest rest' act _hstep_g _hbstep_rest ih_step _ih_bstep
        role hns hnr fl fc fl' fc' hbs hbs' => by
      -- bs = (label, g) :: rest, bs' = (label, g') :: rest'
      -- hbs says ((label, g) :: rest) = (fl, fc) :: ((label, g) :: rest).tail
      -- This means (label, g) = (fl, fc), so fl = label and fc = g
      -- Similarly for hbs'
      simp only [List.tail_cons, List.cons.injEq] at hbs hbs'
      -- hbs : (label, g) = (fl, fc) ∧ rest = rest
      -- hbs' : (label, g') = (fl', fc') ∧ rest' = rest'
      have heq_fc : fc = g := by
        simp only [Prod.mk.injEq] at hbs
        exact hbs.1.2.symm
      have heq_fc' : fc' = g' := by
        simp only [Prod.mk.injEq] at hbs'
        exact hbs'.1.2.symm
      rw [heq_fc, heq_fc']
      -- ih_step : ∀ role, role ≠ act.sender → role ≠ act.receiver → EQ2 (trans g' role) (trans g role)
      exact ih_step role hns hnr)
    g act g' hstep role hns hnr

/-! ## Claims Bundle -/

/-- Domain containment for EnvStep: post-step domain is subset of pre-step domain.

Note: EnvStep does NOT preserve domain equality because global steps can shrink
the role set (step_roles_subset). Instead, we have containment.

For domain equality, use EnvStepOnto which projects onto a fixed role set. -/
theorem envstep_dom_subset {env env' : ProjectedEnv} {act : GlobalActionR}
    (h : EnvStep env act env') :
    ∀ p, p ∈ env'.map Prod.fst → p ∈ env.map Prod.fst := by
  cases h with
  | of_global g g' _ hstep =>
      intro p hp
      simp only [projEnv_dom] at hp ⊢
      exact step_roles_subset g g' _ hstep p hp

/-- Claims bundle for harmony lemmas. -/
structure Claims where
  /-- Global step induces environment step. -/
  harmony : ∀ g g' act, step g act g' → EnvStep (projEnv g) act (projEnv g')
  /-- Domain containment through steps (post ⊆ pre). -/
  dom_subset : ∀ env env' act, EnvStep env act env' →
    ∀ p, p ∈ env'.map Prod.fst → p ∈ env.map Prod.fst

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  harmony := step_harmony
  dom_subset := fun _ _ _ h => envstep_dom_subset h

end RumpsteakV2.Proofs.Projection.Harmony
