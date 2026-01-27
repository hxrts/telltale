import Effects.Deployment.Part2a
import Effects.Deployment.Part2b

/-!
# MPST Deployed Protocol Bundle

This module defines the structure for a deployed protocol: a bundle containing
the protocol specification, projected local types, initial monitor state, and
all required certificates for safe execution.

## Overview

A **deployed protocol** is the artifact produced when a developer:
1. Defines a protocol (currently as local types, later as global type)
2. Provides proofs of well-formedness
3. Sets up initial monitor state
4. Declares the protocol's interface for composition

## Key Structures

- `InterfaceType`: What a protocol exports/imports for composition
- `DeployedProtocol`: Complete bundle with all certificates
- `ProtocolBundle`: Lightweight bundle without proofs (for runtime)

## Composition

Two deployed protocols can be composed if their interfaces are compatible:
- Disjoint session IDs
- Matching exports/imports
- Merged environments remain coherent

See Phase 12 for the full linking judgment.
-/
