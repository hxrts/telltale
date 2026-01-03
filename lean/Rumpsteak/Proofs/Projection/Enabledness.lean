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

/-- Projection-to-enabledness bridge (to be proved). -/
axiom project_can_step (g : GlobalType) (role : String) (lt : LocalTypeR)
    (act : LocalActionR)
    (hproj : projectR g role = Except.ok lt)
    (hstep : canStep lt act)
    (hcoh : coherentG g)
    : canStep g (LocalActionR.toGlobal role act)

end Rumpsteak.Proofs.Projection.Enabledness
