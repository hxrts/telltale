/-! # RumpsteakV2.Protocol.Projection.Projectb

Boolean checker for V2 projection (`projectb`).

## Expose

The following definitions form the semantic interface for proofs:

- `projectb`: boolean projection checker
- `projectbBranches`: branch-wise projection for participants
- `projectbAllBranches`: single candidate check for non-participants
- `CProjectF`: one-step generator for coinductive projection
- `CProject`: coinductive projection relation (greatest fixed point of CProjectF)
- `CProject_coind`: coinduction principle for CProject
- `BranchesProjRel`: branch-wise projection for send/recv
- `AllBranchesProj`: all branches project to same candidate
- `projectb_end_end`: reflection lemma for end-end
- `projectb_var_var`: reflection lemma for var-var
- `projectb_mu_mu`: reflection lemma for mu-mu
- `projectb_comm_other`: reflection lemma for non-participant
-/

import RumpsteakV2.Protocol.Projection.Projectb.Part1
import RumpsteakV2.Protocol.Projection.Projectb.Part2
import RumpsteakV2.Protocol.Projection.Projectb.Part3
import RumpsteakV2.Protocol.Projection.Projectb.Part4
