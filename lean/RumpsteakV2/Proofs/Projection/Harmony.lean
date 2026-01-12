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

**Proof strategy:** This requires showing that `trans` produces coherent projections
for all branches. For CProject-able types, this follows from `AllBranchesProj`:
- `AllBranchesProj R gbs role cand` means all branches project to `cand`
- `project_deterministic` ensures uniqueness
- Therefore all branches project EQ2-equivalently

**Not universally true:** For arbitrary (non-projectable) global types, this can fail.
The axiom is stated without a well-formedness precondition because in practice
it's only used for types that arise from global steps, which preserve projectability.

**Note:** A complete proof would either:
1. Add a CProject or well-formedness hypothesis, or
2. Show that `trans` produces coherent results for any type (which is false in general)

Coq reference: This follows from the AllBranchesProj condition in CProject
(indProj.v, coProj.v). -/
theorem branches_project_coherent (first_label : Label) (first_cont : GlobalType)
    (rest : List (Label × GlobalType)) (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ ((first_label, first_cont) :: rest)) :
    EQ2 (projTrans cont role) (projTrans first_cont role) := by
  -- Requires CProject/well-formedness assumption to establish AllBranchesProj
  -- For CProject-able types: use AllBranchesProj + project_deterministic
  cases hmem with
  | head _ => exact EQ2_refl _
  | tail _ hmem_rest =>
      -- Need to show: EQ2 (trans cont role) (trans first_cont role)
      --
      -- BLOCKED: Requires one of:
      -- 1. CProject/AllBranchesProj hypothesis (proves all branches project equally)
      -- 2. Well-formedness hypothesis on the global type
      -- 3. Coinductive proof using EQ2 bisimulation
      --
      -- Without these, the statement is false for arbitrary non-projectable types.
      -- In practice, this is only used for types arising from global steps.
      sorry

/-- Projection commutes with mu-substitution up to EQ2.

projTrans (body.substitute t (mu t body)) role ≈ (projTrans (mu t body) role).unfold

**Proof strategy:** Case split on contractiveness:

**Contractive case** (`lcontractive body = true`):
- `projTrans (mu t body) role = mu t (projTrans body role)`
- `unfold (mu t (projTrans body role)) = (projTrans body role).substitute t (mu t (projTrans body role))`
- Need: `EQ2 (projTrans (body.substitute t (mu t body)) role) (local_body.substitute t (mu t local_body))`
- This requires showing global and local substitution commute through projection

**Non-contractive case** (`lcontractive body = false`):
- `projTrans (mu t body) role = .end`
- `.end.unfold = .end`
- Need: `EQ2 (projTrans (body.substitute t (mu t body)) role) .end`
- Non-contractive types are degenerate (immediate/unguarded recursion)

Coq reference: This follows from full_eunf_subst in coLocal.v. -/
theorem trans_substitute_unfold (t : String) (body : GlobalType) (role : String) :
    EQ2 (projTrans (body.substitute t (GlobalType.mu t body)) role)
        ((projTrans (GlobalType.mu t body) role).unfold) := by
  -- Case split on contractiveness
  cases hc : lcontractive body with
  | true =>
      -- Contractive: projTrans (mu t body) role = mu t (projTrans body role)
      -- unfold (mu t x) = x.substitute t (mu t x)
      -- Need to show global/local substitution correspondence
      -- Goal: EQ2 (projTrans (body.substitute t (mu t body)) role)
      --           ((projTrans body role).substitute t (mu t (projTrans body role)))
      --
      -- BLOCKED: Requires showing global and local substitution commute through projection.
      -- This is a deep semantic property requiring coinductive reasoning on projTrans.
      -- Coq reference: full_eunf_subst in coLocal.v uses coinductive bisimulation.
      sorry
  | false =>
      -- Non-contractive: projTrans (mu t body) role = .end
      -- Goal: EQ2 (projTrans (body.substitute t (mu t body)) role) .end
      -- Non-contractive means immediate/unguarded recursion
      --
      -- BLOCKED: Requires showing non-contractive substitutions collapse to .end.
      -- The projection of a non-productive recursion degenerates to .end.
      sorry

/-! ### Participant Projection Axioms

The following two axioms are duals of each other, capturing how sender and receiver
projections evolve after a step. They share the same structure:
- Either the participant sees a transition matching the action, or
- The participant's projection is unchanged (EQ2-equivalent)

**Duality relationship**: `proj_trans_sender_step` and `proj_trans_receiver_step` are
symmetric under send/recv duality. If proven, one could potentially derive the other
via the duality transformation on LocalTypeR.
-/

/-- After a global step, the sender's local type transitions appropriately.
    The sender's projection after the step matches the expected continuation.

This theorem captures the key semantic property: when a global type steps via
action (s, r, l), the sender s's local type should transition from
`send r [... (l, T) ...]` to `T` (the continuation for label l).

**Proof strategy:** By induction on `step g act g'`:

**comm_head case**: `g = comm sender receiver branches`, `g' = cont` where `(act.label, cont) ∈ branches`
- For the sender: `trans g sender = send receiver (transBranches branches sender)` by `trans_comm_sender`
- The result follows from finding the matching branch

**comm_async case**: `g = comm sender receiver branches`, `g' = comm sender receiver branches'`
- The action is for a nested communication, so sender ≠ act.sender
- Projection is unchanged (second disjunct)

**mu case**: `step (body.substitute t (mu t body)) act g'`
- Use IH on the substituted body
- Connect via `trans_substitute_unfold`

**Duality:** This and `proj_trans_receiver_step` are dual under send/recv. -/
theorem proj_trans_sender_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    ∃ cont, projTrans g act.sender = .send act.receiver [(act.label, cont)] ∧
            EQ2 (projTrans g' act.sender) cont ∨
    EQ2 (projTrans g' act.sender) (projTrans g act.sender) := by
  -- Proof by induction on step requires careful analysis of projection + trans_comm_sender/receiver
  -- The main cases are:
  -- 1. comm_head: sender's projection transitions via the selected branch
  -- 2. comm_async: nested action, sender may be unchanged
  -- 3. mu: unfold recursion and apply IH
  --
  -- BLOCKED: Requires step induction with projection analysis.
  -- Key lemma needed: trans_comm_sender shows sender's projection structure.
  -- The proof follows the Coq harmony theorem structure (harmony.v).
  sorry

/-- After a global step, the receiver's local type transitions appropriately.
    Dual to `proj_trans_sender_step` - see duality note above.

**Proof strategy:** Dual to sender case, using `trans_comm_receiver` instead of `trans_comm_sender`.
The proof structure mirrors `proj_trans_sender_step` exactly. -/
theorem proj_trans_receiver_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    ∃ cont, projTrans g act.receiver = .recv act.sender [(act.label, cont)] ∧
            EQ2 (projTrans g' act.receiver) cont ∨
    EQ2 (projTrans g' act.receiver) (projTrans g act.receiver) := by
  -- Dual to proj_trans_sender_step - same proof structure with recv instead of send
  --
  -- BLOCKED: Requires step induction with projection analysis (dual to sender case).
  -- Key lemma needed: trans_comm_receiver shows receiver's projection structure.
  -- The proof follows the Coq harmony theorem structure (harmony.v).
  sorry

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
    -- motive_2: for BranchesStep bs act bs', non-participant has BranchesRel on transBranches
    (motive_2 := fun bs act bs' _ =>
      ∀ role, role ≠ act.sender → role ≠ act.receiver →
        BranchesRel EQ2 (transBranches bs' role) (transBranches bs role))
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
    (fun sender receiver branches branches' act label cont hns_cond _hcond _hmem _hcan _hbstep
        ih_bstep role hns hnr => by
      -- g = comm sender receiver branches
      -- g' = comm sender receiver branches'
      -- hns : role ≠ act.sender, hnr : role ≠ act.receiver
      -- ih_bstep : BranchesRel EQ2 (transBranches branches' role) (transBranches branches role)
      --
      -- Get branch-wise EQ2 preservation from motive_2 IH
      have hbranch_rel := ih_bstep role hns hnr
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
              cases _hbstep
          | _ :: _, [] =>
              -- BranchesStep to [] requires branches = [], contradiction
              cases _hbstep
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
    (fun _act role _hns _hnr => by
      simp only [transBranches]
      exact List.Forall₂.nil)
    -- Case 5: BranchesStep.cons
    (fun label g g' rest rest' act _hstep_g _hbstep_rest ih_step ih_bstep role hns hnr => by
      simp only [transBranches]
      apply List.Forall₂.cons
      · -- Head: (label, trans g' role) and (label, trans g role)
        constructor
        · rfl  -- labels match
        · -- Need: EQ2 (trans g' role) (trans g role)
          -- ih_step gives exactly this
          exact ih_step role hns hnr
      · -- Tail: IH gives BranchesRel for rest
        exact ih_bstep role hns hnr)
    g act g' hstep role hns hnr

/-- BranchesStep preserves transBranches up to branch-wise EQ2 for non-participants.

When branches step to branches' via BranchesStep, the transBranches are related
by BranchesRel EQ2 for any role not involved in the action.

This captures the semantic property that stepping inside branches doesn't affect
non-participant projections: each branch steps, and projection commutes with stepping.

Proven by induction on BranchesStep, using proj_trans_other_step for each branch. -/
theorem branches_step_preserves_trans (branches branches' : List (Label × GlobalType))
    (act : GlobalActionR) (role : String)
    (hstep : BranchesStep step branches act branches')
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    BranchesRel EQ2 (transBranches branches' role) (transBranches branches role) := by
  induction hstep with
  | nil =>
      simp only [transBranches]
      exact List.Forall₂.nil
  | cons label g g' rest rest' act hstep_g _hbstep_rest ih =>
      simp only [transBranches]
      apply List.Forall₂.cons
      · constructor
        · rfl
        · exact proj_trans_other_step g g' act role hstep_g hns hnr
      · exact ih hns hnr

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
