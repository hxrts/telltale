import RumpsteakV2.Protocol.Projection.ProjectProps

/-! # RumpsteakV2.Protocol.Projection.Project.Props

Determinism properties for projection (up to EQ2).

## Expose

The following definitions form the semantic interface for proofs:

- `project_deterministic`: CProject determinism up to EQ2
- `branches_proj_deterministic`: branch-wise determinism up to EQ2
- `Claims`: bundle of determinism properties
-/

/-
The Problem. Provide a stable, documented entry point for projection
determinism properties without exposing the implementation details.
Solution Structure. Re-export the determinism theorems from
`RumpsteakV2.Protocol.Projection.ProjectProps`.
-/
