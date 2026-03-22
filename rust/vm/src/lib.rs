//! Protocol-machine and guest-runtime surfaces for choreographic session type protocols.
//!
//! This crate provides a standalone, embeddable protocol machine that executes
//! choreographic protocols projected to local session types. The protocol
//! machine validates every instruction against its session type monitor,
//! ensuring protocol conformance at runtime.
//!
//! # Architecture
//!
//! The protocol machine follows the Lean specification in `lean/Runtime/VM/`:
//! - **Instructions** ([`instr::Instr`]): bytecode ops for send/recv/choice/session lifecycle
//! - **Coroutines** ([`coroutine::Coroutine`]): lightweight execution units, one per role
//! - **Sessions** ([`session::SessionStore`]): manage session lifecycle and namespaces
//! - **Buffers** ([`buffer::BoundedBuffer`]): bounded message channels with backpressure
//! - **Scheduler** ([`scheduler::Scheduler`]): policy-based coroutine scheduling
//! - **Loader** ([`loader`]): dynamic choreography loading with validation
//! - **Compiler** ([`compiler`]): compile `LocalTypeR` to bytecode
//!
//! The crate exposes one canonical single-thread protocol-machine surface,
//! [`ProtocolMachine`], plus guest-runtime driver surfaces such as
//! [`GuestRuntime`]. Higher-level systems (for example `telltale-simulator`)
//! instantiate guest runtimes around the protocol machine with deterministic
//! middleware for network latency, faults, property monitoring, and
//! checkpointing.
//!
//! **Nested simulation** is supported via [`nested::NestedVMHandler`], which
//! allows a protocol-machine coroutine to host an inner protocol machine for
//! distributed or hierarchical simulations.
//!
//! # Effect Handler Contract
//!
//! The protocol machine's [`ExternalHandler`] is synchronous, deterministic, and
//! **session-local**. It must not depend on global time or shared mutable
//! state across sessions. This is distinct from the async, typed
//! `telltale_choreography::ChoreoHandler` used by generated choreography code.
//!
//! # Usage
//!
//! ```ignore
//! use telltale_vm::{
//!     GuestRuntime, OwnedSession, ProtocolMachine, ProtocolMachineConfig, loader::CodeImage
//! };
//!
//! let config = ProtocolMachineConfig::default();
//! let mut machine = ProtocolMachine::new(config);
//! let image = CodeImage::from_local_types(&local_types, &global_type);
//! let _session: OwnedSession =
//!     machine.load_choreography_owned(&image, "runtime/owner")?;
//! while machine.step(&handler)? {}
//!
//! let mut guest = GuestRuntime::new(ProtocolMachineConfig::default());
//! let _owned = guest.load_choreography_owned(&image, "runtime/owner")?;
//! guest.run(&handler, 64, 1)?;
//! ```

use cfg_if::cfg_if;

pub mod architecture;
pub mod bridge;
pub mod buffer;
pub mod clock;
pub mod commit_common;
/// Communication replay modes and consumption state for deterministic and speculatively
/// replayed session histories.
pub mod communication_replay;
pub mod compiler;
pub mod composition;
pub mod coroutine;
pub mod determinism;
pub mod driver;
pub mod effect;
pub mod envelope_diff;
pub mod exec;
pub mod exec_api;
pub mod faults;
pub mod guard;
pub mod identity;
pub mod instr;
pub mod instruction_semantics;
pub mod integration;
pub mod intern;
pub mod kernel;
pub mod loader;
pub mod nested;
pub mod output_condition;
pub mod owned;
pub mod persistence;
pub mod runtime_contracts;
pub mod scheduler;
pub mod semantic_objects;
pub mod serialization;
/// Session store and role/session bookkeeping used by protocol execution.
pub mod session;
pub mod trace;
pub mod transfer_semantics;
pub mod verification;
#[doc(hidden)]
pub mod vm;

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        #[doc(hidden)]
        pub mod threaded;
    }
}

cfg_if! {
    if #[cfg(target_arch = "wasm32")] {
        pub mod wasm;
    }
}

/// Canonical protocol-machine public surface.
pub mod protocol_machine {
    pub use crate::kernel::VMKernel;
    pub use crate::semantic_objects::{
        AuthoritativeRead, AuthoritativeReadKind, AuthoritativeReadLifecycle, CanonicalHandle,
        CanonicalHandleKind, ObservedRead, OperationInstance, OperationPhase, OutstandingEffect,
        OutstandingEffectStatus, ProgressContract, ProgressState, ProtocolMachineSemanticObjects,
        PublicationEvent, PublicationObserverClass, PublicationStatus, SemanticHandoff,
        SEMANTIC_OBJECTS_SCHEMA_VERSION,
    };
    pub use crate::vm::{
        EffectTraceCaptureMode, MonitorMode, ObservabilityRetentionConfig,
        ObservabilityRetentionMode, PayloadValidationMode, Program, ProgramStore,
        RuntimeTuningProfile, SchedExecStatus, SchedStepDebug, ThreadedRoundSemantics,
        VMConfig as ProtocolMachineConfig, VMError as ProtocolMachineError,
        VMState as ProtocolMachineState, VmMemoryUsage, VmRetainedBytes, VM as ProtocolMachine,
    };
}

/// Canonical guest-runtime public surface.
pub mod guest_runtime {
    pub use crate::driver::NativeSingleThreadDriver as GuestRuntime;
    #[cfg(feature = "multi-thread")]
    pub use crate::driver::NativeThreadedDriver as ThreadedGuestRuntime;
}

/// Canonical host-runtime boundary surface.
pub mod host_runtime {
    pub use crate::effect::EffectHandler as ExternalHandler;
}

pub use architecture::{
    EngineOwnership, EngineRole, CANONICAL_ENGINE, CROSS_TARGET_CONTRACT, ENGINE_OWNERSHIP,
    EQUIVALENCE_SURFACES,
};
pub use bridge::{
    EffectGuardBridge, IdentityGuardBridge, IdentityPersistenceBridge, IdentityVerificationBridge,
    PersistenceEffectBridge,
};
pub use clock::SimClock;
pub use communication_replay::{
    CommunicationConsumeResult, CommunicationConsumption, CommunicationConsumptionArtifact,
    CommunicationIdentity, CommunicationReplayError, CommunicationReplayMode,
    CommunicationReplayState, CommunicationStepKind, DefaultCommunicationConsumption,
    COMM_IDENTITY_DOMAIN_TAG, COMM_REPLAY_DUPLICATE_TAG, COMM_REPLAY_SEQUENCE_MISMATCH_TAG,
};
pub use composition::{
    ComposedRuntime, CompositionCertificate, CompositionError, DeterminismCapability, MemoryBudget,
    MemoryUsage, ProtocolBundle, SchedulerCapability, TheoremPackCapabilities,
};
pub use coroutine::{CoroStatus, Coroutine, CoroutineState, KnowledgeSet, Value};
pub use determinism::{DeterminismMode, EffectDeterminismTier};
pub use driver::NativeSingleThreadDriver as GuestRuntime;
pub use effect::EffectHandler as ExternalHandler;
pub use effect::{
    CorruptionType, EffectAdmissibility, EffectAuthorityClass, EffectExchangeRecord, EffectFailure,
    EffectFailureKind, EffectHandlerDomain, EffectInterfaceMetadata, EffectOutcome,
    EffectOutcomeStatus, EffectReentrancyPolicy, EffectRequest, EffectRequestBody, EffectResponse,
    EffectResult, EffectTimeoutPolicy, EffectTotality, EffectTraceEntry, EffectTraceTape,
    RecordingEffectHandler, ReplayEffectHandler, TopologyPerturbation,
};
pub use envelope_diff::{
    EffectOrderingClass, EnvelopeDiff, EnvelopeDiffArtifactV1, FailureVisibleDiffClass,
    SchedulerPermutationClass, WaveWidthBound,
};
pub use exec_api::{ExecResult, ExecStatus, StepEvent, StepPack};
pub use faults::{classify_fault, fault_code, fault_code_of, FaultClass};
pub use guard::{GuardLayer, InMemoryGuardLayer, LayerId};
pub use identity::{IdentityModel, ParticipantId, SiteId as IdentitySiteId, StaticIdentityModel};
pub use instr::Instr;
pub use integration::{run_loaded_vm_record_replay_conformance, LoadedVmReplayConformance};
pub use intern::{EdgeId, EdgeSymbol, EdgeSymbolTable, StringId, SymbolTable};
pub use kernel::VMKernel;
pub use nested::NestedVMHandler;
pub use output_condition::{
    verify_output_condition, OutputConditionCheck, OutputConditionHint, OutputConditionMeta,
    OutputConditionPolicy,
};
pub use owned::OwnedSession;
pub use persistence::{NoopPersistence, PersistenceModel};
pub use runtime_contracts::{
    admit_vm_runtime, determinism_profile_supported, enforce_vm_runtime_gates,
    request_determinism_profile, requires_vm_runtime_contracts, runtime_capability_snapshot,
    DeterminismArtifacts, RuntimeAdmissionResult, RuntimeContracts, RuntimeGateResult,
};
pub use scheduler::{
    CrossLaneHandoff, LaneId as SchedulerLaneId, PriorityPolicy, SchedPolicy, SchedState,
    Scheduler, StepUpdate,
};
pub use semantic_objects::{
    protocol_machine_semantic_objects_v1, AuthoritativeRead, AuthoritativeReadKind,
    AuthoritativeReadLifecycle, CanonicalHandle, CanonicalHandleKind, ObservedRead,
    OperationInstance, OperationPhase, OutstandingEffect, OutstandingEffectStatus,
    ProgressContract, ProgressState, ProtocolMachineSemanticObjects, PublicationEvent,
    PublicationObserverClass, PublicationStatus, SemanticHandoff, SEMANTIC_OBJECTS_SCHEMA_VERSION,
};
pub use serialization::{
    canonical_effect_trace, canonical_replay_fragment_v1, canonical_semantic_audit_log,
    canonical_trace_v1, canonicalize_protocol_machine_semantic_objects, semantic_audit_log_v1,
    CanonicalReplayFragmentV1, CanonicalTraceV1, SemanticAuditRecord,
};
pub use session::{
    decode_edge_json, AuthorityArtifact, AuthorityAuditEvent, AuthorityAuditRecord,
    AuthorityWitnessId, CancellationWitness, ClosedSessionSummary, Edge, FragmentOwnerId,
    HandlerId, OwnershipCapability, OwnershipClaimId, OwnershipEpoch, OwnershipError,
    OwnershipReceipt, OwnershipScope, OwnershipTerminalReason, ReadinessWitness,
    SessionHostMutation, SessionId, SessionStore, SessionStoreMemoryUsage,
    SessionStoreRetainedBytes, TimeoutWitness,
};
pub use trace::{
    normalize_trace, normalize_trace_v1, obs_session, strict_trace, with_tick, NormalizedTraceV1,
    TRACE_NORMALIZATION_SCHEMA_VERSION,
};
pub use transfer_semantics::{
    decode_transfer_request, delegation_receipt, delegation_scope_for_endpoint,
    move_endpoint_bundle, validate_delegation_coherence, DelegationAuditRecord, DelegationReceipt,
    DelegationStatus, TransferRequest,
};
pub use verification::{
    signValue, sign_value, verifySignedValue, verify_signed_value, AuthProof, AuthTree, Commitment,
    DefaultVerificationModel, Hash, HashTag, Nullifier, Signature, SigningKey, VerificationModel,
    VerifyingKey,
};
pub use vm::{
    EffectTraceCaptureMode, MonitorMode, ObservabilityRetentionConfig, ObservabilityRetentionMode,
    PayloadValidationMode, Program, ProgramStore, RuntimeTuningProfile, SchedExecStatus,
    SchedStepDebug, ThreadedRoundSemantics, VMConfig as ProtocolMachineConfig,
    VMError as ProtocolMachineError, VMState as ProtocolMachineState, VmMemoryUsage,
    VmRetainedBytes, VM as ProtocolMachine,
};

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        pub use driver::NativeThreadedDriver as ThreadedGuestRuntime;
        pub use threaded::{ContentionMetrics, LaneHandoff, LaneId, LaneSchedulerState, LaneSelection};
    }
}

cfg_if! {
    if #[cfg(target_arch = "wasm32")] {
        pub use wasm::WasmVM;
    }
}
