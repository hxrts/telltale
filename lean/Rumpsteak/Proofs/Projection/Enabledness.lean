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

/-- Projection-to-enabledness bridge (to be proved). -/
axiom project_can_step (g : GlobalType) (role : String) (lt : LocalTypeR)
    (act : LocalActionR)
    (hproj : projectR g role = Except.ok lt)
    (hstep : canStep lt act)
    (hcoh : coherentG g)
    : canStep g (LocalActionR.toGlobal role act)

end Rumpsteak.Proofs.Projection.Enabledness
