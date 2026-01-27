import RumpsteakV2.Protocol.Projection.Project.ImplCompPostfix

/-! # RumpsteakV2.Protocol.Projection.Project.CProjectTransRel

CProject-to-EQ2 transitivity path and coinduction relations.

## Expose

The following definitions form the semantic interface for proofs:

- `CProjectTransRel`: witness relation for coinduction
- `CProjectTransRelComp`: composition closure of the witness relation
- `CProjectTransRelComp_postfix`: postfix proof for the closure
- `CProject_implies_EQ2_trans`: CProject implies EQ2 to trans
- `CProject_implies_EQ2_trans_thm`: internal coinductive proof
-/

/-
The Problem. Provide a stable entry point for the coinductive projection-to-EQ2
transitivity path (CProjectTransRel and its composition variants) without exposing
implementation details.
Solution Structure. Re-export the implementation from the Impl* files and document
which definitions are intended for downstream proofs.
-/
