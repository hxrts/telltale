import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.Projection.Projectb
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
- `CProject`
-/

namespace RumpsteakV2.Protocol.Projection

export RumpsteakV2.Protocol.Projection.Trans (trans lcontractive)
export RumpsteakV2.Protocol.Projection.Projectb (projectb CProject)
-- TODO (Phase C): export RumpsteakV2.Protocol.Projection.Project (projectR?)

end RumpsteakV2.Protocol.Projection
