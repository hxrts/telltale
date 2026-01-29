import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.ProjectProps
import RumpsteakV2.Protocol.Projection.Embed
import RumpsteakV2.Protocol.Projection.EmbedProps
import RumpsteakV2.Protocol.Projection.Project
import RumpsteakV2.Protocol.Projection.MutualTest
import RumpsteakV2.Protocol.Projection.MutualTestSizeOf
import RumpsteakV2.Protocol.Projection.MutualTestIncr

/-! # RumpsteakV2.Protocol.Projection

Projection API entry point for V2.

## Expose

The following definitions form the semantic interface for proofs:

- `trans`
- `lcontractive`
- `projectb`
- `CProject` (determinism up to EQ2 via ProjectProps)
- `projectR?` (proof-carrying projection with soundness/completeness)
-/

namespace RumpsteakV2.Protocol.Projection

export RumpsteakV2.Protocol.Projection.Trans (trans lcontractive)
export RumpsteakV2.Protocol.Projection.Projectb (projectb CProject project_deterministic
  branches_proj_deterministic)
export RumpsteakV2.Protocol.Projection.Embed (CEmbed embed_deterministic branches_embed_deterministic
  embed_project_roundtrip branches_embed_project_roundtrip project_embed_roundtrip)
export RumpsteakV2.Protocol.Projection.Project (projectR? projectR?_sound projectR?_complete
  projectR?_some_iff_CProject projectR?_some_implies_projectb)

end RumpsteakV2.Protocol.Projection
