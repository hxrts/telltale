/-! # RumpsteakV2.Protocol.Projection.Trans

Candidate projection for V2 (Coq-style `trans`).

## Expose

The following definitions form the semantic interface for proofs:

- `trans`: candidate projection function
- `transBranches`: helper for projecting branch lists
- `lcontractive`: guardedness predicate for recursion
- `trans_freeVars_subset`: free variables are preserved
- `transBranches_freeVars_subset`: branch-wise free variable preservation
- `trans_comm_sender`: shape lemma for sender projection
- `trans_comm_receiver`: shape lemma for receiver projection
- `trans_comm_other`: shape lemma for non-participant projection
-/

import RumpsteakV2.Protocol.Projection.Trans.Core
import RumpsteakV2.Protocol.Projection.Trans.Participation
import RumpsteakV2.Protocol.Projection.Trans.Contractive
