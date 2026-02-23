import Choreography.Projection.Project.ImplCompleteness

/-! # Choreography.Projection.Project.Completeness

Completeness and branch-coherence lemmas for projection.

## Expose

The following definitions form the semantic interface for proofs:

- `c_project_implies_eq2_trans`: CProject implies EQ2 to trans
- `branches_proj_rel_implies_branches_rel_eq2`: branch-wise EQ2 coherence
- `all_branches_proj_implies_eq2_trans`: non-participant branch coherence
-/

/-
The Problem. Collect the completeness and branch-coherence lemmas that relate
CProject witnesses to trans outputs, so callers can import a single module.
Solution Structure. Re-export the completeness lemmas from the Impl* files and
summarize the exposed surface.
-/
