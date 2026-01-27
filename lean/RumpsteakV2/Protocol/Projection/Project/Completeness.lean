import RumpsteakV2.Protocol.Projection.Project.ImplCompleteness

/-! # RumpsteakV2.Protocol.Projection.Project.Completeness

Completeness and branch-coherence lemmas for projection.

## Expose

The following definitions form the semantic interface for proofs:

- `CProject_implies_EQ2_trans`: CProject implies EQ2 to trans
- `BranchesProjRel_implies_BranchesRel_EQ2`: branch-wise EQ2 coherence
- `AllBranchesProj_implies_EQ2_trans`: non-participant branch coherence
-/

/-
The Problem. Collect the completeness and branch-coherence lemmas that relate
CProject witnesses to trans outputs, so callers can import a single module.
Solution Structure. Re-export the completeness lemmas from the Impl* files and
summarize the exposed surface.
-/
