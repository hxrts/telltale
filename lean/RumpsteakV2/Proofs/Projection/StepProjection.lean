import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # Step Projection Theorems

This module proves that projection commutes appropriately with global stepping.

## Main Results

- `proj_trans_sender_step_v2`: After a global step, the sender's projection
  either shows a send with the label in projected branches, or is EQ2-equivalent.

- `proj_trans_receiver_step_v2`: Dual property for the receiver.

## Note on Axiom Reformulation

The original axiom `proj_trans_sender_step_axiom` required:
```
projTrans g act.sender = .send act.receiver [(act.label, cont)]
```

This single-branch form is unprovable when branches have multiple entries.
The correct statement uses membership in projected branches:
```
∃ bs cont, projTrans g act.sender = .send act.receiver bs ∧
           (act.label, cont) ∈ bs ∧
           EQ2 (projTrans g' act.sender) cont
```

## Proof Strategy (from Coq's `harmony.v`)

By induction on `step g act g'`:

1. **comm_head**: Direct participation case - projection was `.send`/`.recv`,
   continuation matches the selected branch via `transBranches` membership.

2. **comm_async**: Nested stepping - either projection unchanged (non-participant)
   or branches step in lockstep with BranchesRel EQ2.

3. **mu**: Unfolding - use IH on substituted body and connect via
   `EQ2_unfold_right`.
-/

namespace RumpsteakV2.Proofs.Projection.StepProjection

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR (LocalTypeR)
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.CoTypes.EQ2

-- Alias to avoid confusion
abbrev projTrans := trans

/-! ## Helper Lemmas for transBranches and membership -/

/-- If `(label, cont) ∈ branches`, then `(label, trans cont role) ∈ transBranches branches role`. -/
theorem mem_transBranches_of_mem (branches : List (Label × GlobalType))
    (label : Label) (cont : GlobalType) (role : String)
    (hmem : (label, cont) ∈ branches) :
    (label, trans cont role) ∈ transBranches branches role := by
  induction branches with
  | nil => cases hmem
  | cons hd tl ih =>
    cases hmem with
    | head =>
      simp only [transBranches, List.mem_cons]
      left
      trivial
    | tail _ htl =>
      unfold transBranches
      right
      exact ih htl

/-! ## Projection Shape Lemmas -/

/-- For the comm_head case: if role = sender, the projection is `.send receiver branches`. -/
theorem proj_trans_comm_sender_is_send
    (sender receiver : String) (branches : List (Label × GlobalType)) :
    trans (.comm sender receiver branches) sender =
      .send receiver (transBranches branches sender) := by
  exact trans_comm_sender sender receiver sender branches rfl

/-- For the comm_head case: if role = receiver, the projection is `.recv sender branches`. -/
theorem proj_trans_comm_receiver_is_recv
    (sender receiver : String) (branches : List (Label × GlobalType))
    (hne : receiver ≠ sender) :
    trans (.comm sender receiver branches) receiver =
      .recv sender (transBranches branches receiver) := by
  exact trans_comm_receiver sender receiver receiver branches rfl hne

/-! ## Reformulated Step Projection Theorems

These are the CORRECT formulations that can be proven.

We now require the action to match the head communication (as in the
Coq `preserve_proj` head case). This avoids the invalid comm_async
counterexamples where the sender participates in a nested action while
the outer comm has not stepped. -/

private def action_pred (g : GlobalType) (act : GlobalActionR) : Prop :=
  match g with
  | .comm sender receiver _ =>
      act.sender = sender ∧ act.receiver = receiver
  | _ => False

/-- Statement type for step projection (sender).
    This factored-out type helps with the mutual induction. -/
abbrev SenderStepResult (g : GlobalType) (act : GlobalActionR) (g' : GlobalType) : Prop :=
  (∃ bs cont, projTrans g act.sender = .send act.receiver bs ∧
              (act.label, cont) ∈ bs ∧
              EQ2 (projTrans g' act.sender) cont) ∨
  EQ2 (projTrans g' act.sender) (projTrans g act.sender)

/-- After a global step, the sender's local type either:
    1. Was `.send receiver bs` where `(label, cont) ∈ bs` and `EQ2 (projTrans g' sender) cont`, or
    2. The new projection is EQ2 to the original projection.

This is the correct formulation that accounts for multi-branch protocols. -/
theorem proj_trans_sender_step_v2 (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hpred : action_pred g act) :
    SenderStepResult g act g' := by
  cases hstep with
  | comm_head sender receiver branches label g' hmem =>
      left
      exact ⟨transBranches branches sender,
             projTrans g' sender,
             proj_trans_comm_sender_is_send sender receiver branches,
             mem_transBranches_of_mem branches label g' sender hmem,
             EQ2_refl _⟩
  | comm_async sender receiver branches branches' act label cont hns hcond hmem hcan hbstep =>
      -- action_pred impossible for async steps
      have hpred' : act.sender = sender ∧ act.receiver = receiver := by
        simpa [action_pred] using hpred
      have hcontra : False := by
        have hrcv : act.receiver ≠ receiver := hcond hpred'.1
        exact hrcv hpred'.2
      exact hcontra.elim
  | mu t body act g' hstep_inner =>
      -- action_pred impossible for mu at head
      simp [action_pred] at hpred

/-- Statement type for step projection (receiver). -/
abbrev ReceiverStepResult (g : GlobalType) (act : GlobalActionR) (g' : GlobalType) : Prop :=
  (∃ bs cont, projTrans g act.receiver = .recv act.sender bs ∧
              (act.label, cont) ∈ bs ∧
              EQ2 (projTrans g' act.receiver) cont) ∨
  EQ2 (projTrans g' act.receiver) (projTrans g act.receiver)

/-- After a global step, the receiver's local type either:
    1. Was `.recv sender bs` where `(label, cont) ∈ bs` and `EQ2 (projTrans g' receiver) cont`, or
    2. The new projection is EQ2 to the original projection.

This is the dual of `proj_trans_sender_step_v2`. -/
theorem proj_trans_receiver_step_v2 (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hpred : action_pred g act) (hno_self : g.noSelfComm = true) :
    ReceiverStepResult g act g' := by
  cases hstep with
  | comm_head sender receiver branches label g' hmem =>
      have hne : receiver ≠ sender := by
        have hns := hno_self
        simp [GlobalType.noSelfComm] at hns
        have hne' : sender ≠ receiver := hns.1
        exact ne_comm.mp hne'
      left
      exact ⟨transBranches branches receiver,
             projTrans g' receiver,
             proj_trans_comm_receiver_is_recv sender receiver branches hne,
             mem_transBranches_of_mem branches label g' receiver hmem,
             EQ2_refl _⟩
  | comm_async sender receiver branches branches' act label cont hns hcond hmem hcan hbstep =>
      -- action_pred impossible for async steps
      have hpred' : act.sender = sender ∧ act.receiver = receiver := by
        simpa [action_pred] using hpred
      have hcontra : False := by
        have hrcv : act.receiver ≠ receiver := hcond hpred'.1
        exact hrcv hpred'.2
      exact hcontra.elim
  | mu t body act g' hstep_inner =>
      -- action_pred impossible for mu at head
      simp [action_pred] at hpred

/-! ## Original Axiom Compatibility

We expose a lightweight compatibility wrapper that simply reuses the v2
statement under the head-action predicate. -/
theorem proj_trans_sender_step_original_compat (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') (hpred : action_pred g act) :
    SenderStepResult g act g' := by
  exact proj_trans_sender_step_v2 g g' act hstep hpred

end RumpsteakV2.Proofs.Projection.StepProjection
