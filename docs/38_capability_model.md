# Capability Model

This page is the canonical reference for Telltale's first-class
protocol-critical capability model.

The model is intentionally narrow. It covers protocol-critical authority,
evidence, finalization, handoff, and reconfiguration/runtime-upgrade semantics.
It does not define a general-purpose application authorization framework.

## Scope Boundary

In scope:

- protocol-critical capability semantics that change protocol-visible truth
- replay-visible evidence and finalization objects
- ownership and receipt/handoff/reconfiguration transition artifacts
- theorem-pack and runtime admission gates

Out of scope:

- general host application authorization
- arbitrary user/resource policy languages
- product-specific auth delegation systems unrelated to protocol semantics
- host-only policy decisions that cannot be modeled as typed Rust/Lean objects

## Four Capability Classes

| Class | Main question | Representative objects |
|---|---|---|
| `admission` | may this runtime/profile/configuration execute at all? | theorem-pack eligibility, runtime contracts, determinism-profile gates |
| `ownership` | who may currently mutate one live session or fragment? | `OwnershipCapability` |
| `evidence` | why is a protocol-critical branch or canonicalization step justified? | `ReadinessWitness`, `AuthoritativeRead`, `ObservedRead`, `MaterializationProof`, `CanonicalHandle`, `PublicationEvent` |
| `transition` | what explicit object authorizes transfer, handoff, cutover, or reconfiguration? | `OwnershipReceipt`, `SemanticHandoff`, `DelegationReceipt`, `RuntimeUpgradeArtifact`, reconfiguration transition artifacts |

The canonical Rust boundary is `rust/machine/src/capabilities.rs`.
The canonical Lean boundary is `lean/Runtime/Proofs/CapabilityModel.lean`
together with the theorem-pack and conservation proof surfaces.

## Canonical Lifecycle States

| State | Meaning |
|---|---|
| `issued` | object exists and may be consumed or transitioned later |
| `consumed` | object was used exactly once on its sanctioned path |
| `rejected` | object was denied as invalid, stale, or insufficient |
| `invalidated` | object became unusable because later semantic state revoked it |
| `committed` | transition object became canonical |
| `rolled_back` | transition object failed and did not become canonical |
| `expired` | object aged out of its validity window |

Not every class uses every lifecycle state. For example, `ownership` uses
`issued`, `invalidated`, `expired`, and `rejected`, while `transition`
artifacts commonly use `issued`, `committed`, `rolled_back`, `rejected`, and
`invalidated`.

## Finalization State Machine

Finalization is the explicit bridge from protocol observation to canonical
truth.

| Stage | Meaning |
|---|---|
| `observed` | only observational input exists |
| `authoritative` | authoritative evidence exists, but proof-bearing success is incomplete |
| `materialized` | proof-bearing success exists, but canonical publication/handle pairing is incomplete |
| `canonical` | publication/materialization/handle conditions are satisfied and the result may be consumed as protocol truth |
| `invalidated` | a handoff or transition revoked the path before canonical reuse |
| `rejected` | proof-bearing publication or repair failed |

The key runtime/Lean objects are:

- `ProtocolMachineFinalization`
- `FinalizationPath`
- `FinalizationReadClass`
- `FinalizationStage`

Observed input never becomes canonical directly. It must pass through the
explicit authoritative/materialization/publication path.

## Language Mapping

| DSL form | Capability class | Resulting semantic object family |
|---|---|---|
| `authoritative let x = check ...` | `evidence` | `AuthoritativeRead`, readiness/evidence-bearing path |
| `observe let x = observe ...` | `evidence` | `ObservedRead` |
| `let receipt = transfer ...` | `transition` | `OwnershipReceipt` / transfer receipt path |
| `publish witness as Publication` | `evidence` | `PublicationEvent` |
| `materialize proof from Publication` | `evidence` | `MaterializationProof`, `CanonicalHandle` |
| `handoff op to Role with receipt` | `transition` | `SemanticHandoff` |

Runtime upgrade and reconfiguration are first-class transition semantics in the
runtime and Lean model, but they are not choreography DSL statements today.

## Runtime Meaning

The runtime uses one canonical lifecycle audit and one canonical semantic-object
bundle:

- `ProtocolMachine::capability_lifecycle_audit_log()`
- `ThreadedGuestRuntime::capability_lifecycle_audit_log()`
- `ProtocolMachine::semantic_objects()`
- `ProtocolMachine::protocol_machine_finalization()`

Timeout expiry is modeled strictly: the runtime stores and later expires the
exact issued `TimeoutWitness`, rather than reconstructing expiry from a bare
clock map later.

Transfer/handoff and runtime upgrade/reconfiguration are also explicit. They
emit typed transition artifacts rather than relying on hidden host-local state.

## Lean and Bridge Surfaces

The Lean model exports this surface through:

- `lean/Runtime/Proofs/CapabilityModel.lean`
- `lean/Runtime/Tests/ProtocolMachineRunner.lean`

The strict Rust↔Lean correspondence lane checks the capability/finalization
surface through:

- `rust/bridge/tests/capability_model_correspondence.rs`
- `scripts/check/lean-bridge-strict.sh`

That lane keeps canonical vs invalidated finalization paths and
committed-cutover vs rolled-back runtime-upgrade artifacts executable and
claim-visible.

## Related Docs

- [Capability and Admission](25_capability_admission.md)
- [Protocol-Critical Authority Scope](33_protocol_authority_scope.md)
- [Authority Language Surface](34_authority_language_surface.md)
- [Protocol-Critical Authority and Evidence](35_protocol_authority_evidence.md)
- [Protocol Machine Architecture](12_protocol_machine_architecture.md)
- [Verification Inventory](32_testing_verification_inventory.md)
