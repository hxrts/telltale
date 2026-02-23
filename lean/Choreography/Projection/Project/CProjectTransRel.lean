import Choreography.Projection.Project.ImplCompPostfix

/-! # Choreography.Projection.Project.CProjectTransRel

CProject-to-EQ2 transitivity path and coinduction relations.

## Expose

The following definitions form the semantic interface for proofs:

- `CProjectTransRel`: witness relation for coinduction
- `CProjectTransRelComp`: composition closure of the witness relation
- `c_project_trans_rel_comp_postfix`: postfix proof for the closure
- `c_project_implies_eq2_trans`: CProject implies EQ2 to trans
- `c_project_implies_eq2_trans_thm`: internal coinductive proof
-/

/-
The Problem. Provide a stable entry point for the coinductive projection-to-EQ2
transitivity path (CProjectTransRel and its composition variants) without exposing
implementation details.
Solution Structure. Re-export the implementation from the Impl* files and document
which definitions are intended for downstream proofs.
-/
