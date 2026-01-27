import RumpsteakV2.Protocol.Projection.Project.ImplU

/-! # RumpsteakV2.Protocol.Projection.Project.CProjectU

Unfolding-insensitive projection relation and EQ2 closure path.

## Expose

The following definitions form the semantic interface for proofs:

- `CProjectU`: unfolding-insensitive projection relation
- `CProjectF_unfold`: generator for unfolded projection
- `CProjectUTransRel`: coinductive witness relation for unfolded projection
- `CProjectUTransRelComp`: composition closure for unfolded projection
-/

/-
The Problem. Package the unfolding-insensitive projection relation (CProjectU)
so proofs can depend on a stable interface while implementation details remain
in the Impl* modules.
Solution Structure. Re-export the unfolding-insensitive projection machinery
from `Project.ImplU` and document the public surface.
-/
