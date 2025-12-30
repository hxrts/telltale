# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

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

#### Lean Verification Enhancements
- Expanded merge proofs in `Proofs/Projection/Merging.lean`
- Distinct merge semantics: `mergeSendSorted` (identical labels) and `mergeRecvSorted` (union labels)
- `HeapConfiguration.lean` for heap-based protocol semantics

#### Lean-Rust Bridge
- `LeanRunner` for invoking Lean verification binary
- `validate_projection_with_lean()` method in `Validator`
- Test utilities with `skip_without_lean!` macro for graceful degradation
- Property-based tests with deterministic seeds (`proptest_json_roundtrip.rs`)
- Integration tests comparing Rust and Lean projection results

#### TCP Transport Crate
- New `rumpsteak-transport-tcp` crate for network communication
- Connection pooling and configuration options
- Error handling with `TransportError` type

#### Documentation
- `docs/05_content_addressing.md` - Content addressing system documentation
- `docs/08_topology.md` - Topology configuration documentation
- `docs/09_resource_heap.md` - Resource heap documentation
- Expanded API reference with new feature sections

#### Examples
- `tcp_ping_pong.rs` - TCP transport example
- `topology_integration.rs` - Topology system example

### Changed

#### Crate Restructuring
- Removed `rumpsteak-codegen` crate (functionality merged into `rumpsteak-aura-choreography`)
- Reorganized module structure in choreography crate

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

### Removed

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

[Unreleased]: https://github.com/anthropics/rumpsteak-aura/compare/v0.7.0...HEAD
[0.7.0]: https://github.com/anthropics/rumpsteak-aura/releases/tag/v0.7.0
