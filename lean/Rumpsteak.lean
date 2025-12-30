-- Protocol modules (definitions only)
import Rumpsteak.Protocol.Core
import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ContentId
import Rumpsteak.Protocol.DeBruijn
import Rumpsteak.Protocol.Location
import Rumpsteak.Protocol.Resource
import Rumpsteak.Protocol.Heap
import Rumpsteak.Protocol.Merkle
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.Choreography
import Rumpsteak.Protocol.Projection
import Rumpsteak.Protocol.Program
import Rumpsteak.Protocol.Subtyping
import Rumpsteak.Protocol.Subtyping.Synchronous
import Rumpsteak.Protocol.Subtyping.TreeDecomposition
import Rumpsteak.Protocol.Subtyping.Asynchronous
-- Semantics modules (requires fixing Process.lean for Lean 4.24)
-- import Rumpsteak.Protocol.Semantics.Process
-- import Rumpsteak.Protocol.Semantics.Configuration
-- import Rumpsteak.Protocol.Semantics.HeapConfiguration
-- import Rumpsteak.Protocol.Semantics.Reduction
-- import Rumpsteak.Protocol.Semantics.Typing

-- Proof modules (theorems and claims)
import Rumpsteak.Proofs.Assumptions
import Rumpsteak.Proofs.Duality
import Rumpsteak.Proofs.Projection
import Rumpsteak.Proofs.Projection.Merging
import Rumpsteak.Proofs.Subtyping
import Rumpsteak.Proofs.Safety.SubjectReduction
import Rumpsteak.Proofs.Safety.Progress

-- Runner modules
import Rumpsteak.Runner.Main

-- Diagnostics
import Rumpsteak.Diagnostics.Basic

/-! # Rumpsteak

Root module for the Rumpsteak verification library.

## Overview

Rumpsteak provides formal verification for choreographic programming.
This module re-exports the main components:

- **Protocol**: Core types and operations for choreographies, projection, and subtyping
- **Proofs**: Formal proofs of key properties (duality, reflexivity, etc.)
- **Runner**: CLI tool for validating exported choreographies and programs

## Usage

Import this module for access to the complete verification API:

```lean
import Rumpsteak
```

Or import specific submodules as needed:

```lean
import Rumpsteak.Protocol.Core
import Rumpsteak.Proofs.Duality
```
-/
