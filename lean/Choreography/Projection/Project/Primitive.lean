import Choreography.Projection.Trans.Core
import Choreography.Projection.Trans.Contractive

/-! # Choreography.Projection.Project.Primitive

Canonical low-level projection primitives exposed under
`Choreography.Projection.Project` without depending on higher-level
projectability APIs.
-/

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

/-- Canonical candidate projection function. -/
abbrev trans : GlobalType → String → LocalTypeR := Choreography.Projection.Trans.trans

/-- Canonical helper that projects communication branches. -/
abbrev transBranches : List (Label × GlobalType) → String → List BranchR :=
  Choreography.Projection.Trans.transBranches

/-- Canonical local-contractiveness check for globals. -/
abbrev lcontractive : GlobalType → Bool := Choreography.Projection.Trans.lcontractive

/-- Canonical sender-shape lemma for communication projection. -/
theorem trans_comm_sender
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hrole : role = sender) :
    trans (.comm sender receiver branches) role =
      .send receiver (transBranches branches role) :=
  Choreography.Projection.Trans.trans_comm_sender sender receiver role branches hrole

/-- Canonical receiver-shape lemma for communication projection. -/
theorem trans_comm_receiver
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hrole : role = receiver) (hneq : role ≠ sender) :
    trans (.comm sender receiver branches) role =
      .recv sender (transBranches branches role) :=
  Choreography.Projection.Trans.trans_comm_receiver sender receiver role branches hrole hneq

/-- Canonical non-participant shape lemma for communication projection. -/
theorem trans_comm_other
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hneq_sender : role ≠ sender) (hneq_receiver : role ≠ receiver) :
    trans (.comm sender receiver branches) role =
      match branches with
      | [] => .end
      | (_, cont) :: _ => trans cont role :=
  Choreography.Projection.Trans.trans_comm_other
    sender receiver role branches hneq_sender hneq_receiver

/-- Canonical closedness preservation for projection. -/
theorem trans_isClosed_of_isClosed (g : GlobalType) (role : String)
    (hclosed : g.isClosed = true) :
    (trans g role).isClosed = true :=
  Choreography.Projection.Trans.trans_isClosed_of_isClosed g role hclosed

/-- Canonical local well-formedness preservation for projection. -/
theorem trans_wellFormed_of_wellFormed (g : GlobalType) (role : String)
    (hwf : g.wellFormed = true) :
    LocalTypeR.WellFormed (trans g role) :=
  Choreography.Projection.Trans.trans_wellFormed_of_wellFormed g role hwf

end Choreography.Projection.Project
