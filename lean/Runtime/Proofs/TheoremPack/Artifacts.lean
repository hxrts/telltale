import Runtime.Proofs.TheoremPack.Artifacts.Core
import Runtime.Proofs.TheoremPack.Artifacts.Distributed
import Runtime.Proofs.TheoremPack.Artifacts.Envelope

/-! # Theorem Pack Artifacts

Packaged proof artifacts for distributed systems impossibility results,
quorum geometry safety, and consensus envelope theorems. -/

/-
The Problem. Theorem packs bundle proof artifacts (FLP, CAP, quorum,
etc.) for certificate generation. Each artifact type encapsulates
the protocol structure and its correctness proof in a uniform format.

Solution Structure. Define artifact structures for each theorem family:
`FLPLowerBoundArtifact`, `CAPImpossibilityArtifact`, `QuorumGeometry-
Artifact`, etc. Each bundles the protocol model with its proof term.
The schema is split into `Artifacts.Core` (semantic objects and metadata),
`Artifacts.Distributed` (distributed theorem families), and
`Artifacts.Envelope` (protocol-machine envelopes, bridge, runtime).
-/
