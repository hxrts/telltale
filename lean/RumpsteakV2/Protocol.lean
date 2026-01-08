import RumpsteakV2.Protocol.Core
import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.Projection
import RumpsteakV2.Protocol.CoTypes
import RumpsteakV2.Protocol.Semantics
import RumpsteakV2.Protocol.Spatial

/-! # RumpsteakV2.Protocol

Protocol entry point for V2, collecting core types, projection, and semantics.

## Expose

The following definitions form the semantic interface for proofs:

- Core: `Role`, `Action`, `LocalKind`, `LocalAction`, `LocalType`
- Global: `PayloadSort`, `Label`, `GlobalType`, `GlobalType.wellFormed`
- Local: `LocalTypeR`, `LocalTypeR.unfold`, `LocalTypeR.substitute`
- Projection: `trans`, `projectb`, `CProject`
- CoTypes: `EQ2`, `QLocalTypeR`, `QLocalTypeR.unfold`
- Semantics: `ProjectedEnv`, `projEnv`, `EnvStep`, `WellFormedEnv`
- Spatial: `SpatialReq`, `Topology`, `Satisfies`, `SpatialLe`
-/

namespace RumpsteakV2.Protocol

export RumpsteakV2.Protocol.Core
  (Role Action Action.origin Action.destination Action.label
    LocalKind LocalAction LocalType LocalKind.swap LocalAction.dual LocalType.dual)

export RumpsteakV2.Protocol.GlobalType
  (PayloadSort Label GlobalType GlobalType.wellFormed GlobalType.roles
    GlobalType.freeVars GlobalType.substitute)

export RumpsteakV2.Protocol.LocalTypeR
  (LocalTypeR LocalTypeR.dual LocalTypeR.unfold LocalTypeR.freeVars
    LocalTypeR.substitute)

export RumpsteakV2.Protocol.Projection
  (trans lcontractive projectb CProject)
-- TODO (Phase C): add projectR? once implemented

export RumpsteakV2.Protocol.CoTypes
  (EQ2 QLocalTypeR QLocalTypeR.unfold)

export RumpsteakV2.Protocol.Semantics
  (ProjectedEnv ProjectedEnv.lookup ProjectedEnv.set projEnv EnvStep WellFormedEnv)

export RumpsteakV2.Protocol.Spatial
  (SpatialReq Topology Satisfies SpatialLe spatial_le_sound)

end RumpsteakV2.Protocol
