import Telltale.Protocol.Projection.Trans
import Telltale.Protocol.Projection.Projectb
import Telltale.Protocol.Projection.ProjectProps
import Telltale.Protocol.Projection.Embed
import Telltale.Protocol.Projection.EmbedProps
import Telltale.Protocol.Projection.Project
import Telltale.Protocol.Projection.MutualTest
import Telltale.Protocol.Projection.MutualTestSizeOf
import Telltale.Protocol.Projection.MutualTestIncr

/-! # Telltale.Protocol.Projection

Projection API entry point for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `trans`
- `lcontractive`
- `projectb`
- `CProject` (determinism up to EQ2 via ProjectProps)
- `projectR?` (proof-carrying projection with soundness/completeness)
-/

namespace Telltale.Protocol.Projection

export Telltale.Protocol.Projection.Trans (trans lcontractive)
export Telltale.Protocol.Projection.Projectb (projectb CProject project_deterministic
  branches_proj_deterministic)
export Telltale.Protocol.Projection.Embed (CEmbed embed_deterministic branches_embed_deterministic
  embed_project_roundtrip branches_embed_project_roundtrip project_embed_roundtrip)
export Telltale.Protocol.Projection.Project (projectR? projectR?_sound projectR?_complete
  projectR?_some_iff_CProject projectR?_some_implies_projectb)

end Telltale.Protocol.Projection
