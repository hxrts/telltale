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
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Quotient
open RumpsteakV2.Semantics.EnvStep

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

/-- After a global step, the sender's local type transitions appropriately.
    The sender's projection after the step matches the expected continuation.

This axiom captures the key semantic property: when a global type steps via
action (s, r, l), the sender s's local type should transition from
`send r [... (l, T) ...]` to `T` (the continuation for label l).

Proving this constructively requires showing:
1. trans (g.step act) s = (trans g s after local step for label l)
2. The local step for send is: unfold, then select branch l

This involves coinductive reasoning on trans and the step relation. -/
axiom proj_trans_sender_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    ∃ cont, trans g act.sender = .send act.receiver [(act.label, cont)] ∧
            EQ2 (trans g' act.sender) cont ∨
    EQ2 (trans g' act.sender) (trans g act.sender)

/-- After a global step, the receiver's local type transitions appropriately.
    Similar to sender case but for recv. -/
axiom proj_trans_receiver_step (g g' : GlobalType) (act : GlobalActionR)
    (hstep : step g act g') :
    ∃ cont, trans g act.receiver = .recv act.sender [(act.label, cont)] ∧
            EQ2 (trans g' act.receiver) cont ∨
    EQ2 (trans g' act.receiver) (trans g act.receiver)

/-- Non-participating roles have unchanged projections through a step.

This axiom captures the key harmony property: if a role is not involved in an action
(neither sender nor receiver), their projected local type is unchanged by the step.

Proof sketch (by mutual induction on step and BranchesStep):

1. **comm_head case**: g = comm sender receiver branches, g' = cont
   - For non-participant (role ≠ sender ≠ receiver):
   - trans g role = trans first_cont role (by trans_comm_other)
   - trans g' role = trans cont role
   - Need: all branches project identically for non-participants (branches_project_eq)

2. **comm_async case**: g = comm sender receiver branches, g' = comm sender receiver branches'
   - For role = sender: both project to send receiver (transBranches ...)
     Need: transBranches branches ≈ transBranches branches' (by branch-wise IH)
   - For role = receiver: both project to recv sender (transBranches ...)
     Need: same as sender case
   - For role ≠ sender ≠ receiver: both project via first branch's continuation
     The IH from BranchesStep gives the result directly

3. **mu case**: g = mu t body, step (body.substitute t (mu t body)) act g'
   - trans g role = mu t (trans body role) (if contractive)
   - IH: EQ2 (trans g' role) (trans (body.substitute t (mu t body)) role)
   - Need: trans_substitute_EQ2 to connect substituted body to mu

The proof requires coinductive reasoning for trans_substitute_EQ2 and the
coherence condition branches_project_eq. -/
axiom proj_trans_other_step (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g')
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver) :
    EQ2 (trans g' role) (trans g role)

/-! ## Claims Bundle -/

/-- Claims bundle for harmony lemmas. -/
structure Claims where
  /-- Global step induces environment step. -/
  harmony : ∀ g g' act, step g act g' → EnvStep (projEnv g) act (projEnv g')
  /-- Domain is preserved through steps. -/
  dom_preserved : ∀ env env' act, EnvStep env act env' → env.map Prod.fst = env'.map Prod.fst

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  harmony := step_harmony
  dom_preserved := fun _ _ _ => envstep_preserves_dom

end RumpsteakV2.Proofs.Projection.Harmony
