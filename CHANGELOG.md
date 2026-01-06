# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

#### Lean Verification
- Convert 6 projection axioms to theorems (`freeVars_substitute_subset`, `substitute_closed_when_only_var`, `allVarsBound_nil_implies_freeVars_nil`, `trans_muve_of_not_part_of2`, `CProject_muve_of_not_part_of2`, `part_of_all2_implies_part_of2`)

### Changed

- Move `lean_validation` example to `rumpsteak-lean-bridge` crate to eliminate circular dev-dependency during crates.io publishing

## [0.8.0] - 2025-01-06

### Added

#### Lean V2 Verification (Major)
- Complete V2 projection core with coinductive proofs
- Subject Reduction theorem implementation
- Harmony proofs connecting global and local semantics
- EQ2 equivalence and CProject coinductive projection
- Proof-carrying projection API (`projectR?`)
- `projectb_sound` theorem for V2 projection
- Participation predicates (`part_of2`, `part_of_all2`)
- Coinduction up-to techniques for EQ2 congruence proofs
- `QLocalTypeR` quotient type with lifted `substitute` and `dual` operations
- Convert 30+ axioms to proven theorems including:
  - `step_deterministic` (global step is deterministic)
  - `sizePred_substitute`, `actionPred_substitute`, `uniqLabels_substitute`
  - `projectR_substitute`, `merge_fold_member`
  - `sizePred_from_projectable`
  - `normalize` function with complete termination proof
  - `LocalTypeR.substitute` as total function (was partial)
  - `foldMerge_preserved`, `canStep_lift_to_comm`
  - `EQ2_substitute_barendregt`, `EQ2_dual`
  - `trans_CProject`
- Lean 4.25.0 upgrade with Coherence proof fixes

#### DSL Enhancements
- PureScript-style syntax for choreographies
- `RoleDecides` desugaring (loop decide by Role)
- Timing patterns: `heartbeat`, `@runtime_timeout`, `timed_choice`
- Typed annotation system (`ProtocolAnnotation` enum replacing `HashMap<String, String>`)
- `choreo_fmt` binary for DSL formatting
- Explicit `continue` syntax for recursive protocols

#### Content Addressing System
- `ContentId` type for cryptographic identity of protocol artifacts
- `Hasher` trait with pluggable hash algorithms (SHA-256, Blake3, Poseidon)
- `Contentable` trait for canonical serialization
- De Bruijn index conversion for alpha-equivalence
- Content store with structural sharing and memoization
- Lean definitions in `lean/Rumpsteak/Protocol/ContentId.lean` and `DeBruijn.lean`

#### Topology System
- `Topology` struct for separating protocol logic from deployment configuration
- `Location` enum (`Local`, `Remote`, `Colocated`)
- `TopologyConstraint` for placement requirements (`Colocated`, `Separated`, `Pinned`, `Region`)
- Topology DSL parser with mode support (`local`, `per_role`, `kubernetes`, `consul`)
- `TopologyHandler` for runtime topology-aware message routing
- Transport abstraction layer with `TransportFactory`
- Lean definitions in `lean/Rumpsteak/Protocol/Location.lean`

#### Resource Heap
- `ResourceId` for content-addressed resource identification
- `Resource` enum for heap-allocated protocol artifacts (`Channel`, `Message`, `Session`)
- `Heap` with deterministic `BTreeMap` storage and nullifier-based consumption tracking
- Merkle tree support for verifiable state proofs
- `HeapConfiguration` for protocol semantics integration
- Lean definitions in `lean/Rumpsteak/Protocol/Heap.lean`, `Resource.lean`, `Merkle.lean`

#### Testing
- Comprehensive test coverage for session type correctness
- Phase 3 handler and interpreter tests
- Phase 4 simulation engine tests
- Async subtyping property tests with deterministic seeds
- Golden file equivalence tests for Lean-Rust validation

#### Lean-Rust Bridge
- `LeanRunner` for invoking Lean verification binary
- `validate_projection_with_lean()` method in `Validator`
- Test utilities with `skip_without_lean!` macro for graceful degradation
- Property-based tests with deterministic seeds (`proptest_json_roundtrip.rs`)
- Integration tests comparing Rust and Lean projection results

#### CI & Tooling
- WASM compilation checks (`just wasm-check`, `just wasm-build`, `just wasm-test`)
- Improved CI dry run with `RUSTFLAGS="-D warnings"` to catch rustc warnings
- Golden file test commands (`just test-golden`, `just list-golden`)

#### Documentation
- `docs/05_content_addressing.md` - Content addressing system documentation
- `docs/08_topology.md` - Topology configuration documentation
- `docs/09_resource_heap.md` - Resource heap documentation
- Expanded API reference with new feature sections
- Academic citations for Lean axioms

### Changed

#### Crate Restructuring
- Removed `rumpsteak-aura-fsm` crate (visualization not currently needed)
- Removed `rumpsteak-transport-tcp` crate (superseded by topology module)
- Split large modules into submodules (codegen, choice_analysis, parser, topology)
- Moved V1 Lean proofs to `work/Rumpsteak/` directory

#### Merge Semantics (Breaking)
- Send merge now requires identical label sets (matches Lean `mergeSendSorted`)
- Receive merge unions label sets (matches Lean `mergeRecvSorted`)
- Updated `rust/theory/src/merge.rs` with correct semantics
- Updated `rust/choreography/src/compiler/merge.rs` to match

#### Documentation Reorganization
- Renamed `00_background.md` to `00_introduction.md`
- Renumbered all documentation files for logical ordering
- Moved `99_architecture.md` to `18_crate_architecture.md`
- Updated all internal links

#### API Changes
- Renamed `TopologyHandlerBuilder::as_role()` to `with_role()` (naming convention)
- Renamed `Topology::from_str()` to `Topology::parse()` (avoid trait confusion)
- Added `#[derive(Default)]` to `Location` and `TopologyMode` enums
- `NonEmptyVec<T>` for type-safe non-empty collections in AST
- Role constructors return `RoleValidationResult` for early validation

### Fixed
- Lean 4.24/4.25 API compatibility issues in semantics proofs
- Async session semantics in Lean formalization
- Channel BEq lawfulness
- Clippy warnings across workspace

### Removed

- `rust/fsm/` crate (DOT, Mermaid, Petri net visualization)
- `rust/transport-tcp/` crate
- `rust/codegen/` crate (merged into choreography)

## [0.7.0] - 2024-12-29

### Added
- Lean verification job in GitHub Actions
- Initial crate architecture documentation

### Changed
- Bumped version to 0.7.0
- Improved Lean documentation formatting

### Fixed
- mdbook build errors by pinning old version

[Unreleased]: https://github.com/hxrts/rumpsteak-aura/compare/v0.8.0...HEAD
[0.8.0]: https://github.com/hxrts/rumpsteak-aura/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/hxrts/rumpsteak-aura/releases/tag/v0.7.0
