import RumpsteakV2.Protocol.Projection.Project.Core
import RumpsteakV2.Protocol.Projection.Project.Muve
import RumpsteakV2.Protocol.Projection.Project.CProjectTransRel
import RumpsteakV2.Protocol.Projection.Project.CProjectU
import RumpsteakV2.Protocol.Projection.Project.Completeness
import RumpsteakV2.Protocol.Projection.Project.Props

/-
The Problem. Provide a stable, proof-facing entry point for projection results
while keeping the implementation split across focused files.

Solution Structure. This module is a thin barrel that re-exports the projection
implementation from `Project.Impl` and related files, so downstream proofs can
import a single path.
-/

/-! # RumpsteakV2.Protocol.Projection.Project

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
