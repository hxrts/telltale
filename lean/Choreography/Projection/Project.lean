import Choreography.Projection.Project.Core
import Choreography.Projection.Project.Muve
import Choreography.Projection.Project.CProjectTransRel
import Choreography.Projection.Project.CProjectU
import Choreography.Projection.Project.Completeness
import Choreography.Projection.Project.Props

/-! # Choreography.Projection.Project

Proof-carrying projection API for V2.

## Overview

This module re-exports the projection implementation from `Project.Impl`.

## Expose

The following definitions form the semantic interface for proofs:

- `projectR?`: proof-carrying projection (returns projection with CProject proof)
- `projectR?_some_iff_CProject`: specification lemma
- `projectR?_sound`: soundness (some implies CProject)
- `projectR?_complete`: completeness (CProject implies some)
- `EQ_end`: non-participants project to EEnd (EQ2-equivalent)
-/

/- 
The Problem. Provide a stable, proof-facing entry point for projection results
while keeping the implementation split across focused files.
Solution Structure. This module is a thin barrel that re-exports the projection
implementation from `Project.Impl` and related files, so downstream proofs can
depend on a single import.
-/
