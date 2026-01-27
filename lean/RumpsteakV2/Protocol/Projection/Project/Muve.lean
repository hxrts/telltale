import RumpsteakV2.Protocol.Projection.Project.MuveImpl

/-! # RumpsteakV2.Protocol.Projection.Project.Muve

Muve (mu-var-end) theory used by projection proofs.

## Expose

The following definitions form the semantic interface for proofs:

- `isMuve`: mu-var-end chain predicate
- `ClosedMuveRel`: closed muve relation for EQ2 coinduction
- `EQ_end`: non-participants project to EEnd (EQ2-equivalent)
-/

/-
The Problem. Provide a stable entry point for the mu-var-end (muve) theory
used by projection proofs without exposing internal proof structure.
Solution Structure. This module re-exports the muve implementation from
`Project.MuveImpl` so other modules can depend on a single import.
-/
