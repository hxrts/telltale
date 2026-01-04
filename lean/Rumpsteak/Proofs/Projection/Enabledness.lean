import Rumpsteak.Protocol.Coherence
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.GlobalType

/-! # Projection Enabledness Bridge

Connect local enabledness to global enabledness under coherence.
This mirrors the Coq lemma `project_can_step` used in subject reduction.
-/

namespace Rumpsteak.Proofs.Projection.Enabledness

open Rumpsteak.Protocol.Coherence
open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.ProjectionR

/-- Head-enabledness from sender projection of a comm. -/
theorem canStep_comm_sender_head (sender receiver : String)
    (branches : List (Label × GlobalType))
    (bs : List (Label × LocalTypeR)) (label : Label) (cont : LocalTypeR)
    (hproj : projectR (.comm sender receiver branches) sender = .ok (.send receiver bs))
    (hmem : (label, cont) ∈ bs) :
    canStep (.comm sender receiver branches)
      (LocalActionR.toGlobal sender (LocalActionR.send receiver label)) := by
  have hprojBranches := projectR_comm_sender_inv sender receiver branches bs hproj
  obtain ⟨gcont, hmemg, _hprojg⟩ :=
    projectBranches_mem_proj branches sender label cont bs hprojBranches hmem
  exact canStep.comm_head sender receiver branches label gcont hmemg

/-- Head-enabledness from receiver projection of a comm. -/
theorem canStep_comm_receiver_head (sender receiver : String)
    (branches : List (Label × GlobalType))
    (bs : List (Label × LocalTypeR)) (label : Label) (cont : LocalTypeR)
    (hne : sender ≠ receiver)
    (hproj : projectR (.comm sender receiver branches) receiver = .ok (.recv sender bs))
    (hmem : (label, cont) ∈ bs) :
    canStep (.comm sender receiver branches)
      (LocalActionR.toGlobal receiver (LocalActionR.recv sender label)) := by
  have hprojBranches := projectR_comm_receiver_inv sender receiver branches bs hne hproj
  obtain ⟨gcont, hmemg, _hprojg⟩ :=
    projectBranches_mem_proj branches receiver label cont bs hprojBranches hmem
  exact canStep.comm_head sender receiver branches label gcont hmemg

/-- Non-participant safety: local enabled actions avoid the outer receiver (to be proved). -/
axiom nonparticipant_action_safe (sender receiver role : String)
    (branches : List (Label × GlobalType)) (lt : LocalTypeR) (act : LocalActionR)
    (hrole1 : role ≠ sender) (hrole2 : role ≠ receiver)
    (hproj : projectR (.comm sender receiver branches) role = .ok lt)
    (hstep : LocalTypeR.canStep lt act)
    (hact : GlobalType.actionPred (.comm sender receiver branches))
    : act.partner ≠ receiver

/-- Projection commutes with unfolding substitution. -/
theorem projectR_subst_mu (body : GlobalType) (t : String) (role : String) (lt : LocalTypeR)
    (hproj : projectR body role = .ok lt)
    (huniq : GlobalType.uniqLabels body) :
    projectR (body.substitute t (.mu t body)) role = .ok (lt.substitute t (.mu t lt)) := by
  let rlt : LocalTypeR := if lt == .end then .end else .mu t lt
  have hrep : projectR (.mu t body) role = .ok rlt := by
    simp [projectR_mu, hproj, rlt]
  have hproj' :
      projectR (body.substitute t (.mu t body)) role = .ok (lt.substitute t rlt) :=
    projectR_substitute body t (.mu t body) role lt rlt hproj hrep huniq
  have hlocal : lt.substitute t rlt = lt.substitute t (.mu t lt) := by
    by_cases hlt : lt == .end
    · simp [rlt, hlt]
    · simp [rlt, hlt]
  simpa [hlocal] using hproj'

/-- Projection-to-enabledness bridge (Coq `project_can_step`). -/
theorem project_can_step (g : GlobalType) (role : String) (lt : LocalTypeR)
    (act : LocalActionR)
    (hproj : projectR g role = Except.ok lt)
    (hstep : LocalTypeR.canStep lt act)
    (hact : GlobalType.actionPred g)
    (hsize : GlobalType.sizePred g)
    (huniq : GlobalType.uniqLabels g)
    : canStep g (LocalActionR.toGlobal role act) := by
  induction hstep generalizing g with
  | send_head partner branches label cont hmem =>
    cases g with
    | end =>
      simp [projectR] at hproj
    | var t =>
      simp [projectR] at hproj
    | mu t body =>
      have : False := projectR_mu_not_send t body role partner branches hproj
      cases this
    | comm sender receiver gbranches =>
      by_cases hroleSender : role = sender
      · subst hroleSender
        obtain ⟨hpartner, hprojBranches⟩ :=
          projectR_comm_sender_inv' sender receiver gbranches partner branches hproj
        subst hpartner
        exact canStep_comm_sender_head sender receiver gbranches branches label cont hproj hmem
      · by_cases hroleReceiver : role = receiver
        · subst hroleReceiver
          have hne : sender ≠ receiver := actionPred_comm_sender_ne hact
          have hpr := projectR_comm_receiver sender receiver gbranches hne
          simp [hpr] at hproj
        · -- non-participant: rely on safety axiom and commute through a branch
          have hne : sender ≠ receiver := actionPred_comm_sender_ne hact
          have hnonempty : gbranches.isEmpty = false :=
            sizePred_comm_nonempty (sender := sender) (receiver := receiver)
              (branches := gbranches) hsize
          obtain ⟨label0, g0, hmem0⟩ : ∃ label0 g0, (label0, g0) ∈ gbranches := by
            cases gbranches with
            | nil =>
              cases hnonempty
            | cons b rest =>
              exact ⟨b.1, b.2, by simp⟩
          have huniqComm : GlobalType.uniqLabels (.comm sender receiver gbranches) := by
            simpa using huniq
          have hproj0 : projectR g0 role = .ok lt :=
            projectR_comm_non_participant_mem sender receiver role gbranches lt
              hroleSender hroleReceiver hproj huniqComm label0 g0 hmem0
          have hact0 : GlobalType.actionPred g0 := by
            have hbranches := actionPred_comm_branches hact
            exact BranchesForall.mem hbranches hmem0
          have hsize0 : GlobalType.sizePred g0 := by
            exact sizePred_mem (sender := sender) (receiver := receiver)
              (branches := gbranches) hsize hmem0
          have huniq0 : GlobalType.uniqLabels g0 := by
            have hbranches := GlobalType.uniqLabels_comm_branches huniqComm
            exact GlobalType.BranchesUniq.mem hbranches hmem0
          have hcan0 := ih g0 hproj0 hact0 hsize0 huniq0
          -- Condition 1: act.sender ≠ receiver
          -- For send actions: act.sender = role ≠ receiver (by hroleReceiver)
          -- For recv actions: act.sender = act.partner, needs nonparticipant_action_safe
          have hsafe : act.partner ≠ receiver :=
            nonparticipant_action_safe sender receiver role gbranches lt act hroleSender hroleReceiver
              hproj hstep hact
          have hsender_ne : (LocalActionR.toGlobal role act).sender ≠ receiver := by
            cases act.kind <;> simp [LocalActionR.toGlobal, hroleReceiver, hsafe]
          -- Condition 2: act.sender = sender → act.receiver ≠ receiver (vacuously true for non-participants)
          -- For send: role = sender is false (by hroleSender), so vacuously true
          -- For recv: act.partner = sender → role ≠ receiver (true since role ≠ receiver)
          have hchannel_cond : (LocalActionR.toGlobal role act).sender = sender →
              (LocalActionR.toGlobal role act).receiver ≠ receiver := by
            intro heq
            cases act.kind <;> simp [LocalActionR.toGlobal] at heq ⊢
            · exact absurd heq.symm hroleSender
            · exact hroleReceiver
          exact canStep.comm_async sender receiver gbranches
            (LocalActionR.toGlobal role act) label0 g0 hsender_ne hchannel_cond hmem0 hcan0
  | recv_head partner branches label cont hmem =>
    cases g with
    | end =>
      simp [projectR] at hproj
    | var t =>
      simp [projectR] at hproj
    | mu t body =>
      have : False := projectR_mu_not_recv t body role partner branches hproj
      cases this
    | comm sender receiver gbranches =>
      by_cases hroleReceiver : role = receiver
      · subst hroleReceiver
        have hne : sender ≠ receiver := actionPred_comm_sender_ne hact
        obtain ⟨hpartner, hprojBranches⟩ :=
          projectR_comm_receiver_inv' sender receiver gbranches partner branches hne hproj
        subst hpartner
        exact canStep_comm_receiver_head sender receiver gbranches branches label cont hne hproj hmem
      · by_cases hroleSender : role = sender
        · subst hroleSender
          have hpr := projectR_comm_sender sender receiver gbranches
          simp [hpr] at hproj
        · -- non-participant: recv should not be enabled before outer receiver (axiomatized)
          have hsafe : act.partner ≠ receiver :=
            nonparticipant_action_safe sender receiver role gbranches lt act hroleSender hroleReceiver
              hproj hstep hact
          -- use the same comm-async reasoning as above
          have hnonempty : gbranches.isEmpty = false :=
            sizePred_comm_nonempty (sender := sender) (receiver := receiver)
              (branches := gbranches) hsize
          obtain ⟨label0, g0, hmem0⟩ : ∃ label0 g0, (label0, g0) ∈ gbranches := by
            cases gbranches with
            | nil =>
              cases hnonempty
            | cons b rest =>
              exact ⟨b.1, b.2, by simp⟩
          have huniqComm : GlobalType.uniqLabels (.comm sender receiver gbranches) := by
            simpa using huniq
          have hproj0 : projectR g0 role = .ok lt :=
            projectR_comm_non_participant_mem sender receiver role gbranches lt
              hroleSender hroleReceiver hproj huniqComm label0 g0 hmem0
          have hact0 : GlobalType.actionPred g0 := by
            have hbranches := actionPred_comm_branches hact
            exact BranchesForall.mem hbranches hmem0
          have hsize0 : GlobalType.sizePred g0 := by
            exact sizePred_mem (sender := sender) (receiver := receiver)
              (branches := gbranches) hsize hmem0
          have huniq0 : GlobalType.uniqLabels g0 := by
            have hbranches := GlobalType.uniqLabels_comm_branches huniqComm
            exact GlobalType.BranchesUniq.mem hbranches hmem0
          have hcan0 := ih g0 hproj0 hact0 hsize0 huniq0
          -- Same conditions as in send_head case above
          have hsender_ne : (LocalActionR.toGlobal role act).sender ≠ receiver := by
            cases act.kind <;> simp [LocalActionR.toGlobal, hroleReceiver, hsafe]
          have hchannel_cond : (LocalActionR.toGlobal role act).sender = sender →
              (LocalActionR.toGlobal role act).receiver ≠ receiver := by
            intro heq
            cases act.kind <;> simp [LocalActionR.toGlobal] at heq ⊢
            · exact absurd heq.symm hroleSender
            · exact hroleReceiver
          exact canStep.comm_async sender receiver gbranches
            (LocalActionR.toGlobal role act) label0 g0 hsender_ne hchannel_cond hmem0 hcan0
  | send_async partner branches act' label cont hnePartner hmem hstep_cont ih =>
    cases g with
    | end =>
      simp [projectR] at hproj
    | var t =>
      simp [projectR] at hproj
    | mu t body =>
      have : False := projectR_mu_not_send t body role partner branches hproj
      cases this
    | comm sender receiver gbranches =>
      by_cases hroleSender : role = sender
      · subst hroleSender
        obtain ⟨hpartner, hprojBranches⟩ :=
          projectR_comm_sender_inv' sender receiver gbranches partner branches hproj
        subst hpartner
        obtain ⟨gcont, hmemg, hprojg⟩ :=
          projectBranches_mem_proj gbranches sender label cont branches hprojBranches hmem
        have hact0 : GlobalType.actionPred gcont := by
          have hbranches := actionPred_comm_branches hact
          exact BranchesForall.mem hbranches hmemg
        have hsize0 : GlobalType.sizePred gcont := by
          exact sizePred_mem (sender := sender) (receiver := receiver)
            (branches := gbranches) hsize hmemg
        have huniqComm : GlobalType.uniqLabels (.comm sender receiver gbranches) := by
          simpa using huniq
        have huniq0 : GlobalType.uniqLabels gcont := by
          have hbranches := GlobalType.uniqLabels_comm_branches huniqComm
          exact GlobalType.BranchesUniq.mem hbranches hmemg
        have hcan0 := ih gcont hprojg hact0 hsize0 huniq0
        have hne : sender ≠ receiver := actionPred_comm_sender_ne hact
        -- Condition 1: act.sender ≠ receiver
        have hsender_ne : (LocalActionR.toGlobal role act').sender ≠ receiver := by
          cases act'.kind <;> simp [LocalActionR.toGlobal, hne, hnePartner]
        -- Condition 2: act.sender = sender → act.receiver ≠ receiver
        -- We're the sender, so need to show the receiver differs from outer receiver
        -- For send: sender = sender → act'.partner ≠ receiver (hnePartner gives receiver ≠ act'.partner)
        -- For recv: act'.partner = sender → sender ≠ receiver (true by hne)
        have hchannel_cond : (LocalActionR.toGlobal role act').sender = sender →
            (LocalActionR.toGlobal role act').receiver ≠ receiver := by
          intro heq
          cases act'.kind <;> simp [LocalActionR.toGlobal] at heq ⊢
          · exact hnePartner.symm
          · exact hne
        exact canStep.comm_async sender receiver gbranches
          (LocalActionR.toGlobal role act') label gcont hsender_ne hchannel_cond hmemg hcan0
      · by_cases hroleReceiver : role = receiver
        · subst hroleReceiver
          have hpr := projectR_comm_receiver sender receiver gbranches (actionPred_comm_sender_ne hact)
          simp [hpr] at hproj
        · -- non-participant: use safety + branch IH
          have hnonempty : gbranches.isEmpty = false :=
            sizePred_comm_nonempty (sender := sender) (receiver := receiver)
              (branches := gbranches) hsize
          obtain ⟨label0, g0, hmem0⟩ : ∃ label0 g0, (label0, g0) ∈ gbranches := by
            cases gbranches with
            | nil =>
              cases hnonempty
            | cons b rest =>
              exact ⟨b.1, b.2, by simp⟩
          have huniqComm : GlobalType.uniqLabels (.comm sender receiver gbranches) := by
            simpa using huniq
          have hproj0 : projectR g0 role = .ok lt :=
            projectR_comm_non_participant_mem sender receiver role gbranches lt
              hroleSender hroleReceiver hproj huniqComm label0 g0 hmem0
          have hact0 : GlobalType.actionPred g0 := by
            have hbranches := actionPred_comm_branches hact
            exact BranchesForall.mem hbranches hmem0
          have hsize0 : GlobalType.sizePred g0 := by
            exact sizePred_mem (sender := sender) (receiver := receiver)
              (branches := gbranches) hsize hmem0
          have huniq0 : GlobalType.uniqLabels g0 := by
            have hbranches := GlobalType.uniqLabels_comm_branches huniqComm
            exact GlobalType.BranchesUniq.mem hbranches hmem0
          have hcan0 := ih g0 hproj0 hact0 hsize0 huniq0
          -- Condition 1: act.sender ≠ receiver (needs nonparticipant_action_safe for recv case)
          have hsafe : act'.partner ≠ receiver :=
            nonparticipant_action_safe sender receiver role gbranches lt act' hroleSender hroleReceiver
              hproj hstep hact
          have hsender_ne : (LocalActionR.toGlobal role act').sender ≠ receiver := by
            cases act'.kind <;> simp [LocalActionR.toGlobal, hroleReceiver, hsafe]
          -- Condition 2: vacuously true for non-participants
          have hchannel_cond : (LocalActionR.toGlobal role act').sender = sender →
              (LocalActionR.toGlobal role act').receiver ≠ receiver := by
            intro heq
            cases act'.kind <;> simp [LocalActionR.toGlobal] at heq ⊢
            · exact absurd heq.symm hroleSender
            · exact hroleReceiver
          exact canStep.comm_async sender receiver gbranches
            (LocalActionR.toGlobal role act') label0 g0 hsender_ne hchannel_cond hmem0 hcan0
  | mu t body act' hstep' ih =>
    cases g with
    | end =>
      simp [projectR] at hproj
    | var t0 =>
      simp [projectR] at hproj
    | comm sender receiver gbranches =>
      have hpr := projectR_comm_sender sender receiver gbranches
      simp [hpr] at hproj
    | mu t0 body0 =>
      cases huniq with
      | mu _ _ huniqBody =>
      -- invert projection to get body projection
      simp [projectR_mu] at hproj
      cases hbody : projectR body0 role with
      | error e =>
        simp [hbody] at hproj
      | ok lt0 =>
        simp [hbody] at hproj
        split at hproj
        · cases hproj
        · cases hproj
          have hproj' : projectR (body0.substitute t0 (.mu t0 body0)) role =
              .ok (lt0.substitute t0 (.mu t0 lt0)) :=
            projectR_subst_mu body0 t0 role lt0 hbody huniqBody
          have hcan := ih (body0.substitute t0 (.mu t0 body0)) hproj' hact hsize huniq
          exact canStep.mu t0 body0 (LocalActionR.toGlobal role act') hcan

end Rumpsteak.Proofs.Projection.Enabledness
