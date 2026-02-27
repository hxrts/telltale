import Choreography.Projection.Erasure.Merge

/-! # Choreography.Projection.Erasure.PayloadCompat

Payload-annotation compatibility facade for erasure merge.

`merge` is now compatibility-gated at the canonical executable entrypoint.
This module preserves `mergeWithPayloadCompat` as a stable API alias.
-/

set_option autoImplicit false

namespace Choreography.Projection.Erasure

open SessionTypes.LocalTypeR

/-- Stable API alias for compatibility-gated merge. -/
def mergeWithPayloadCompat (t1 t2 : LocalTypeR) : Option LocalTypeR :=
  merge t1 t2

end Choreography.Projection.Erasure
